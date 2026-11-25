//! Paths under an `Fs` (`std.files`, §13.4). The root `Fs` takes paths as
//! the operating system does. One that `files.within` confines holds its
//! directory open and resolves each path from it one component at a time:
//! every component is opened with `O_NOFOLLOW` relative to the directory
//! before it, so the kernel never follows a link itself. A link is read and
//! its target resolved here, from the link's directory; a `..` in it goes
//! back to a directory already opened, and one above the root is refused, as
//! is an absolute target. A path given may not be absolute or contain `..`.
//! Nothing is checked before it is opened, so a link changed meanwhile can't
//! lead out of the directory.

use std::ffi::{CString, OsStr};
use std::fs::File;
use std::io;
use std::os::fd::{AsRawFd, FromRawFd, OwnedFd};
use std::os::unix::ffi::OsStrExt;
use std::os::unix::fs::OpenOptionsExt;
use std::path::PathBuf;

/// A confined `Fs` (`Obj::Fs`).
pub enum Root {
    /// The directory, held open.
    Dir(OwnedFd),
    /// `within` couldn't open it, or it lies outside the `Fs` it was made
    /// from: every operation fails with this message.
    Denied(String),
}

/// Where a path leads, before it is opened.
pub enum Place {
    /// Under the root `Fs`: the path as given.
    Path(PathBuf),
    /// Under a confined one: its directory (a copy of the descriptor) and
    /// the path relative to it.
    Beneath(OwnedFd, String),
}

/// What is opened at the end of a path.
#[derive(Clone, Copy, PartialEq)]
enum Last {
    /// For reading (a file or a directory).
    Read,
    /// A file for writing, created or emptied.
    Create,
    /// A directory.
    Dir,
    /// A directory, creating it and each one before it that is missing.
    MakeDirs,
}

/// How many links one path may go through, as Linux allows.
const MAX_LINKS: usize = 40;

pub fn outside() -> io::Error {
    io::Error::new(io::ErrorKind::PermissionDenied, "Permission denied (outside the directory this capability allows)")
}

impl Place {
    /// The file at the path, for reading.
    pub fn open(self) -> io::Result<File> {
        match self {
            Place::Path(p) => File::open(p),
            Place::Beneath(root, p) => resolve(&root, &p, Last::Read).map(File::from),
        }
    }

    /// The file at the path, created or emptied, for writing.
    pub fn create(self) -> io::Result<File> {
        match self {
            Place::Path(p) => File::create(p),
            Place::Beneath(root, p) => resolve(&root, &p, Last::Create).map(File::from),
        }
    }

    /// The directory at the path, held open (`within`).
    pub fn dir(self) -> io::Result<OwnedFd> {
        match self {
            Place::Path(p) => {
                std::fs::OpenOptions::new().read(true).custom_flags(libc::O_DIRECTORY).open(p).map(OwnedFd::from)
            }
            Place::Beneath(root, p) => resolve(&root, &p, Last::Dir),
        }
    }

    /// Create the directory and its missing parents.
    pub fn create_dirs(self) -> io::Result<()> {
        match self {
            // `create_dir_all` takes a path's parent to be the path without
            // its last component, which for `out/.` is nothing: it then asks
            // for `out/.` in an `out` that isn't there. Without its `.`
            // components the path names the same directory, and its parents
            // are the ones to create.
            Place::Path(p) => std::fs::create_dir_all(p.components().collect::<PathBuf>()),
            Place::Beneath(root, p) => resolve(&root, &p, Last::MakeDirs).map(drop),
        }
    }

    /// The entries of the directory: each name and whether it is a
    /// directory (a link is not), unsorted.
    pub fn list(self) -> io::Result<Vec<(String, bool)>> {
        match self {
            Place::Path(p) => {
                let mut es = Vec::new();
                for e in std::fs::read_dir(p)? {
                    let e = e?;
                    let dir = e.file_type().is_ok_and(|t| t.is_dir());
                    es.push((e.file_name().to_string_lossy().into_owned(), dir));
                }
                Ok(es)
            }
            Place::Beneath(root, p) => entries(resolve(&root, &p, Last::Dir)?),
        }
    }
}

fn cstr(name: &[u8]) -> io::Result<CString> {
    CString::new(name).map_err(|_| io::Error::new(io::ErrorKind::InvalidInput, "a path with a NUL byte"))
}

fn open_at(dir: &OwnedFd, name: &CString, flags: libc::c_int) -> io::Result<OwnedFd> {
    let flags = flags | libc::O_NOFOLLOW | libc::O_CLOEXEC;
    loop {
        let fd = unsafe { libc::openat(dir.as_raw_fd(), name.as_ptr(), flags, 0o666 as libc::c_uint) };
        if fd >= 0 {
            return Ok(unsafe { OwnedFd::from_raw_fd(fd) });
        }
        let e = io::Error::last_os_error();
        if e.kind() != io::ErrorKind::Interrupted {
            return Err(e);
        }
    }
}

/// The target of the link `name` in `dir`, or `None` if it isn't one.
fn read_link_at(dir: &OwnedFd, name: &CString) -> Option<Vec<u8>> {
    let mut buf = vec![0u8; 256];
    loop {
        let k = unsafe { libc::readlinkat(dir.as_raw_fd(), name.as_ptr(), buf.as_mut_ptr().cast(), buf.len()) };
        if k < 0 {
            return None;
        }
        let k = k as usize;
        if k < buf.len() {
            buf.truncate(k);
            return Some(buf);
        }
        // It may have been cut short: try again with more room.
        let more = buf.len() * 2;
        buf.resize(more, 0);
    }
}

/// A path's components, last first; `.` and empty ones left out.
fn components(p: &[u8]) -> Vec<Vec<u8>> {
    p.split(|&c| c == b'/').filter(|c| !c.is_empty() && *c != b".").rev().map(|c| c.to_vec()).collect()
}

/// Open what `path` names beneath `root`, following links that stay
/// beneath it and refusing any resolution that leaves it.
fn resolve(root: &OwnedFd, path: &str, last: Last) -> io::Result<OwnedFd> {
    // A path given may not be absolute or go up (§13.4); a link's target
    // may go up, as long as it stays beneath `root`.
    if path.starts_with('/') || path.split('/').any(|c| c == "..") {
        return Err(outside());
    }
    // The directories opened so far below `root`, innermost last.
    let mut dirs: Vec<OwnedFd> = Vec::new();
    // What is left to resolve, next last.
    let mut todo = components(path.as_bytes());
    let mut links = 0;
    while let Some(c) = todo.pop() {
        if c == b".." {
            if dirs.pop().is_none() {
                return Err(outside());
            }
            continue;
        }
        let dir = dirs.last().unwrap_or(root);
        let name = cstr(&c)?;
        let at_end = todo.is_empty();
        let made = if last == Last::MakeDirs {
            match unsafe { libc::mkdirat(dir.as_raw_fd(), name.as_ptr(), 0o777) } {
                0 => None,
                _ => Some(io::Error::last_os_error()).filter(|e| e.raw_os_error() != Some(libc::EEXIST)),
            }
        } else {
            None
        };
        let flags = match (at_end, last) {
            (true, Last::Read) => libc::O_RDONLY,
            (true, Last::Create) => libc::O_WRONLY | libc::O_CREAT | libc::O_TRUNC,
            _ => libc::O_RDONLY | libc::O_DIRECTORY,
        };
        match open_at(dir, &name, flags) {
            Ok(fd) if at_end => return Ok(fd),
            Ok(fd) => dirs.push(fd),
            Err(e) => match read_link_at(dir, &name) {
                // A link: its target takes its place, resolved from `dir`.
                Some(target) => {
                    links += 1;
                    if links > MAX_LINKS {
                        return Err(io::Error::from_raw_os_error(libc::ELOOP));
                    }
                    if target.first() == Some(&b'/') {
                        return Err(outside());
                    }
                    if target.is_empty() {
                        return Err(io::Error::from_raw_os_error(libc::ENOENT));
                    }
                    todo.extend(components(&target));
                }
                // Creating the directory failed for a reason other than its
                // being there: that is why it can't be opened.
                None => match made {
                    Some(m) if e.raw_os_error() == Some(libc::ENOENT) => return Err(m),
                    _ => return Err(e),
                },
            },
        }
    }
    // The path names a directory already opened (it is empty, or ends in
    // `..` or a link to a directory).
    if last == Last::Create {
        return Err(io::Error::from_raw_os_error(libc::EISDIR));
    }
    match dirs.pop() {
        Some(d) => Ok(d),
        None => root.try_clone(),
    }
}

#[cfg(any(target_os = "linux", target_os = "android"))]
unsafe fn errno() -> *mut libc::c_int {
    libc::__errno_location()
}

#[cfg(not(any(target_os = "linux", target_os = "android")))]
unsafe fn errno() -> *mut libc::c_int {
    libc::__error()
}

/// The entries of an open directory, without `.` and `..`.
fn entries(dir: OwnedFd) -> io::Result<Vec<(String, bool)>> {
    let d = unsafe { libc::fdopendir(dir.as_raw_fd()) };
    if d.is_null() {
        return Err(io::Error::last_os_error());
    }
    // `closedir` closes it now.
    std::mem::forget(dir);
    let mut es = Vec::new();
    let r = loop {
        unsafe { *errno() = 0 };
        let e = unsafe { libc::readdir(d) };
        if e.is_null() {
            let n = unsafe { *errno() };
            break if n == 0 { Ok(()) } else { Err(io::Error::from_raw_os_error(n)) };
        }
        let name = unsafe { std::ffi::CStr::from_ptr((*e).d_name.as_ptr()) };
        let bytes = name.to_bytes();
        if bytes == b"." || bytes == b".." {
            continue;
        }
        let is_dir = match unsafe { (*e).d_type } {
            libc::DT_DIR => true,
            libc::DT_UNKNOWN => {
                let mut st: libc::stat = unsafe { std::mem::zeroed() };
                let ok = unsafe { libc::fstatat(libc::dirfd(d), name.as_ptr(), &mut st, libc::AT_SYMLINK_NOFOLLOW) } == 0;
                ok && st.st_mode & libc::S_IFMT == libc::S_IFDIR
            }
            _ => false,
        };
        es.push((OsStr::from_bytes(bytes).to_string_lossy().into_owned(), is_dir));
    };
    unsafe { libc::closedir(d) };
    r.map(|()| es)
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::io::{Read, Write};
    use std::os::unix::fs::symlink;
    use std::path::Path;

    /// A fresh directory with `root/sub/inside.txt` and `outside/secret.txt`.
    fn fixture(name: &str) -> PathBuf {
        let t = std::env::temp_dir().join(format!("checkers-confine-{}-{name}", std::process::id()));
        let _ = std::fs::remove_dir_all(&t);
        std::fs::create_dir_all(t.join("root/sub")).unwrap();
        std::fs::create_dir_all(t.join("outside")).unwrap();
        std::fs::write(t.join("root/sub/inside.txt"), "inside").unwrap();
        std::fs::write(t.join("outside/secret.txt"), "secret").unwrap();
        t
    }

    fn at(t: &Path, p: &str) -> Place {
        let root = Place::Path(t.join("root")).dir().unwrap();
        Place::Beneath(root, p.to_string())
    }

    fn read(t: &Path, p: &str) -> io::Result<String> {
        let mut s = String::new();
        at(t, p).open()?.read_to_string(&mut s)?;
        Ok(s)
    }

    fn refused<T>(r: io::Result<T>) -> bool {
        matches!(r, Err(e) if e.to_string() == outside().to_string())
    }

    #[test]
    fn links_out_are_refused() {
        let t = fixture("out");
        symlink("../outside", t.join("root/relative")).unwrap();
        symlink(t.join("outside"), t.join("root/absolute")).unwrap();
        symlink("../../outside", t.join("root/sub/nested")).unwrap();
        symlink("sub/../../outside", t.join("root/dotdot")).unwrap();
        symlink("relative", t.join("root/chain")).unwrap();
        symlink("../outside/made.txt", t.join("root/dangling")).unwrap();
        for p in ["relative/secret.txt", "absolute/secret.txt", "sub/nested/secret.txt", "dotdot/secret.txt", "chain/secret.txt"] {
            assert!(refused(read(&t, p)), "{p}");
        }
        assert!(refused(read(&t, "../outside/secret.txt")));
        assert!(refused(read(&t, "/etc/passwd")));
        assert!(refused(read(&t, "sub/../sub/inside.txt")));
        assert!(refused(at(&t, "dangling").create()));
        assert!(!t.join("outside/made.txt").exists());
        assert!(refused(at(&t, "relative/new/dir").create_dirs()));
        assert!(!t.join("outside/new").exists());
        assert!(refused(at(&t, "relative").list()));
        assert!(refused(at(&t, "relative").dir()));
        std::fs::remove_dir_all(&t).unwrap();
    }

    #[test]
    fn links_in_are_followed() {
        let t = fixture("in");
        symlink("sub", t.join("root/to_sub")).unwrap();
        symlink("sub/inside.txt", t.join("root/to_file")).unwrap();
        symlink("../sub/./inside.txt", t.join("root/sub/up")).unwrap();
        symlink("sub/new.txt", t.join("root/to_new")).unwrap();
        symlink("loop", t.join("root/loop")).unwrap();
        assert_eq!(read(&t, "to_sub/inside.txt").unwrap(), "inside");
        assert_eq!(read(&t, "to_file").unwrap(), "inside");
        assert_eq!(read(&t, "sub/up").unwrap(), "inside");
        assert_eq!(read(&t, "./sub//inside.txt").unwrap(), "inside");
        at(&t, "to_new").create().unwrap().write_all(b"new").unwrap();
        assert_eq!(std::fs::read_to_string(t.join("root/sub/new.txt")).unwrap(), "new");
        at(&t, "to_sub/a/./b").create_dirs().unwrap();
        assert!(t.join("root/sub/a/b").is_dir());
        let mut es = at(&t, "to_sub").list().unwrap();
        es.sort();
        let names: Vec<_> = es.iter().map(|(n, d)| format!("{n}{}", if *d { "/" } else { "" })).collect();
        assert_eq!(names, ["a/", "inside.txt", "new.txt", "up"]);
        assert_eq!(read(&t, "loop").unwrap_err().raw_os_error(), Some(libc::ELOOP));
        assert_eq!(at(&t, "").create().unwrap_err().raw_os_error(), Some(libc::EISDIR));
        std::fs::remove_dir_all(&t).unwrap();
    }
}
