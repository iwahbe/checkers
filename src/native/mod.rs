//! Native code (M8, D80, SPEC §14): erasure (`ir`), closure conversion
//! (`lower`), reference counting (`rc`), Cranelift (`codegen`), run in
//! memory (`run`; compile-time evaluation, `eval`) or written as an
//! executable (`build`). The runtime is the `checkers_rt` crate.

pub mod codegen;
pub mod eval;
pub mod ir;
pub mod lower;
pub mod rc;

use crate::core::{DefId, Globals};
use cranelift_codegen::settings::{self, Configurable};


/// The descriptor the runtime reads (`checkers_rt::prog::install`).
pub(crate) fn descriptor(g: &Globals, p: &lower::Program) -> String {
    let mut d = String::new();
    for (i, c) in g.cons.iter().enumerate() {
        let shown: String = c
            .fields
            .iter()
            .map(|f| if f.2 == crate::core::Icit::Expl && f.1 != crate::core::Mult::Zero { '1' } else { '0' })
            .collect();
        let _ = i;
        d += &format!("con {} {} {} {}\n", c.name, g.arity_con(crate::core::ConId(i as u32)), g.arity_ty(c.ty), shown);
    }
    for n in &p.names {
        d += &format!("def {n}\n");
    }
    let wk = &g.well_known;
    let find = |module: &str, name: &str| {
        g.cons.iter().position(|c| &*c.name == name && &*g.tys[c.ty.0 as usize].module == module).map(|i| i as u32)
    };
    let known: [(&str, Option<u32>); 18] = [
        ("true", wk.true_con.map(|c| c.0)),
        ("false", wk.false_con.map(|c| c.0)),
        ("some", wk.some.map(|c| c.0)),
        ("none", wk.none.map(|c| c.0)),
        ("ok", wk.ok.map(|c| c.0)),
        ("err", wk.err.map(|c| c.0)),
        ("nil", wk.nil.map(|c| c.0)),
        ("cons", wk.cons.map(|c| c.0)),
        ("parsed", find("std.cursor", "Parsed")),
        ("system", find("std.system", "System")),
        ("success", find("std.system", "Success")),
        ("failure", find("std.system", "Failure")),
        ("entry", find("std.files", "Entry")),
        ("output", find("std.proc", "Output")),
        ("spawned", find("std.proc", "Spawned")),
        ("inherit", find("std.proc", "Inherit")),
        ("pipe", find("std.proc", "Pipe")),
        ("discard", find("std.proc", "Discard")),
    ];
    for (k, v) in known {
        if let Some(v) = v {
            d += &format!("known {k} {v}\n");
        }
    }
    if let Some(s) = find("std.system", "System") {
        for f in &g.cons[s as usize].fields {
            d += &format!("system {}\n", f.0);
        }
    }
    d
}

/// Closure-convert and reference-count the program.
fn prepare(g: &Globals, staged: Option<&crate::stage::Staged>, main: DefId) -> lower::Program {
    let mut p = lower::lower(g, staged, main);
    rc_new(g, &mut p);
    p
}

/// Reference counting for the functions added since the last call.
pub(crate) fn rc_new(g: &Globals, p: &mut lower::Program) {
    let fields_of = |c: u32| g.cons[c as usize].fields.len();
    let from = p.rc_done;
    for f in &mut p.funcs[from..] {
        rc::function(f, &fields_of);
    }
    if std::env::var_os("CHECKERS_NATIVE_DUMP").is_some() {
        for (i, f) in p.funcs.iter().enumerate().skip(from) {
            eprintln!("ckf_{i} {} ({} params):\n{}", f.name, f.params.len(), dump(&f.body, 1));
        }
    }
    p.rc_done = p.funcs.len();
}

/// An in-memory module for this machine, with the runtime's symbols.
pub(crate) fn jit_module() -> cranelift_jit::JITModule {
    // Cranelift's tail calls rely on frame pointers.
    let mut jb = cranelift_jit::JITBuilder::with_flags(
        &[("opt_level", "speed"), ("preserve_frame_pointers", "true")],
        cranelift_module::default_libcall_names(),
    )
    .expect("a JIT for this machine");
    for (name, ptr) in checkers_rt::symbols() {
        jb.symbol(name, ptr);
    }
    cranelift_jit::JITModule::new(jb)
}

fn dump(e: &lower::E, d: usize) -> String {
    use lower::E;
    let ind = "  ".repeat(d);
    match e {
        E::Let(x, a, b) => format!("{ind}let v{x} =\n{}\n{}", dump(a, d + 1), dump(b, d)),
        E::Dup(x, b) => format!("{ind}dup v{x}\n{}", dump(b, d)),
        E::Drop(x, b) => format!("{ind}drop v{x}\n{}", dump(b, d)),
        E::DropReuse(x, t, n, b) => format!("{ind}v{t} = drop_reuse v{x} ({n})\n{}", dump(b, d)),
        E::Case { scrut, arms, lits, default } => {
            let mut s = format!("{ind}case v{scrut}");
            for a in arms {
                let fs: Vec<String> = a.fields.iter().map(|f| f.map_or("_".into(), |v| format!("v{v}"))).collect();
                s += &format!("\n{ind}| con{} {} ->\n{}", a.con, fs.join(" "), dump(&a.body, d + 1));
            }
            for (l, b) in lits {
                s += &format!("\n{ind}| {} ->\n{}", dump(l, 0).trim(), dump(b, d + 1));
            }
            if let Some(x) = default {
                s += &format!("\n{ind}| _ ->\n{}", dump(x, d + 1));
            }
            s
        }
        E::Call { f, args, tail } => {
            format!("{ind}{}call ckf_{f}({})", if *tail { "tail " } else { "" }, args.iter().map(|a| dump(a, 0).trim().to_string()).collect::<Vec<_>>().join(", "))
        }
        E::Apply { f, args, tail } => format!(
            "{ind}{}apply {} ({})",
            if *tail { "tail " } else { "" },
            dump(f, 0).trim(),
            args.iter().map(|a| dump(a, 0).trim().to_string()).collect::<Vec<_>>().join(", ")
        ),
        E::Borrow { op, args, drops } => format!(
            "{ind}{op:?}({}){}",
            args.iter().map(|a| dump(a, 0).trim().to_string()).collect::<Vec<_>>().join(", "),
            if drops.is_empty() { String::new() } else { format!(" drop {:?}", drops) }
        ),
        E::Con { con, fields, reuse } => format!(
            "{ind}con{con}{}({})",
            reuse.map_or(String::new(), |t| format!("@v{t}")),
            fields.iter().map(|a| dump(a, 0).trim().to_string()).collect::<Vec<_>>().join(", ")
        ),
        E::MkClo { f, captured } => format!("{ind}closure ckf_{f} {:?}", captured),
        E::Var(v) => format!("{ind}v{v}"),
        E::Int(n) => format!("{ind}{n}"),
        E::Global(g) => format!("{ind}global{g}"),
        E::Tuple(xs) => format!("{ind}({})", xs.iter().map(|a| dump(a, 0).trim().to_string()).collect::<Vec<_>>().join(", ")),
        E::Str(s) => format!("{ind}{s:?}"),
        other => format!("{ind}{}", match other {
            E::Erased => "erased".to_string(),
            E::Unit => "()".to_string(),
            E::BigLit(s) => s.clone(),
            E::Bytes(_) => "b\"…\"".to_string(),
            E::ConFn(c) => format!("conf{c}"),
            E::Par(_) => "par".to_string(),
            E::Fail(m) => format!("fail {m}"),
            _ => "?".to_string(),
        }),
    }
}

/// Compile in memory and run `main` (`checkers run`): the exit code.
pub fn run(g: &Globals, staged: Option<&crate::stage::Staged>, main: DefId, args: &[String], threads: usize) -> i32 {
    let p = prepare(g, staged, main);
    let desc = descriptor(g, &p);
    let module = jit_module();
    let mut gen = codegen::Gen::new(module, p, g);
    gen.define_new();
    let main_clo = gen.main_closure();
    let invoke = gen.invoke;
    let mut module = gen.m;
    module.finalize_definitions().expect("finish native code");
    let inv = module.get_finalized_function(invoke);
    let (clo, _) = module.get_finalized_data(main_clo);
    let invoke: checkers_rt::prog::Invoke = unsafe { std::mem::transmute(inv) };
    let main_w = clo as u64;
    let owner = main.0;
    let args = args.to_vec();
    // `main` and its callees may recurse deeply: a large stack.
    let code = std::thread::Builder::new()
        .stack_size(1 << 30)
        .spawn(move || checkers_rt::entry::run_main(&desc, invoke, main_w, owner, &args, threads))
        .expect("spawn the main thread")
        .join()
        .unwrap_or(70);
    // The code must outlive every thread that runs it.
    std::mem::forget(module);
    code
}

/// Write an executable (`checkers build`).
pub fn build(g: &Globals, staged: Option<&crate::stage::Staged>, main: DefId, out: &std::path::Path) -> Result<(), String> {
    let p = prepare(g, staged, main);
    let desc = descriptor(g, &p);
    let mut fb = settings::builder();
    fb.set("opt_level", "speed").map_err(|e| e.to_string())?;
    fb.set("is_pic", "true").map_err(|e| e.to_string())?;
    // Cranelift's tail calls rely on frame pointers.
    fb.set("preserve_frame_pointers", "true").map_err(|e| e.to_string())?;
    let isa = cranelift_native::builder()
        .map_err(|e| e.to_string())?
        .finish(settings::Flags::new(fb))
        .map_err(|e| e.to_string())?;
    let ob = cranelift_object::ObjectBuilder::new(isa, "checkers_program", cranelift_module::default_libcall_names())
        .map_err(|e| e.to_string())?;
    let module = cranelift_object::ObjectModule::new(ob);
    let mut gen = codegen::Gen::new(module, p, g);
    gen.define_new();
    gen.define_c_main(&desc);
    let product = gen.m.finish();
    let bytes = product.emit().map_err(|e| e.to_string())?;
    let dir = std::env::temp_dir().join(format!("checkers-build-{}", std::process::id()));
    std::fs::create_dir_all(&dir).map_err(|e| e.to_string())?;
    let obj = dir.join("program.o");
    std::fs::write(&obj, bytes).map_err(|e| e.to_string())?;
    let lib = runtime_library().ok_or_else(|| {
        "the runtime library (libcheckers_rt.a) was not found next to `ckc`; set CHECKERS_RT_LIB to its path".to_string()
    })?;
    let status = std::process::Command::new(std::env::var("CC").unwrap_or_else(|_| "cc".into()))
        .arg("-o")
        .arg(out)
        .arg(&obj)
        .arg(&lib)
        .args(["-lpthread", "-ldl", "-lm", "-lrt", "-lutil", "-lgcc_s", "-lc"])
        .status()
        .map_err(|e| format!("running the C compiler to link: {e}"))?;
    let _ = std::fs::remove_dir_all(&dir);
    if !status.success() {
        return Err(format!("linking failed ({status})"));
    }
    Ok(())
}

/// The runtime library to link executables with: `CHECKERS_RT_LIB`, or the
/// newest `libcheckers_rt*.a` next to the running `checkers` (an installed
/// copy) or in `deps/` beside it (built by Cargo, during development).
fn runtime_library() -> Option<std::path::PathBuf> {
    if let Some(p) = std::env::var_os("CHECKERS_RT_LIB") {
        return Some(p.into());
    }
    let exe = std::env::current_exe().ok()?;
    let dir = exe.parent()?;
    let mut best: Option<(std::time::SystemTime, std::path::PathBuf)> = None;
    for d in [dir.join("deps"), dir.to_path_buf()] {
        let Ok(rd) = std::fs::read_dir(&d) else { continue };
        for e in rd.flatten() {
            let name = e.file_name().to_string_lossy().to_string();
            if name.starts_with("libcheckers_rt") && name.ends_with(".a") {
                let t = e.metadata().and_then(|m| m.modified()).unwrap_or(std::time::UNIX_EPOCH);
                if best.as_ref().is_none_or(|(bt, _)| t > *bt) {
                    best = Some((t, e.path()));
                }
            }
        }
    }
    best.map(|(_, p)| p)
}
