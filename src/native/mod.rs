//! Native code (M8, D80, SPEC §14): erasure (`ir`), closure conversion
//! (`lower`), reference counting (`rc`), Cranelift (`codegen`), run in
//! memory (`run`; compile-time evaluation, `eval`) or written as an
//! executable (`build`). The runtime is the `checkers_rt` crate.

pub mod codegen;
pub mod eval;
pub mod fold;
pub mod inline;
pub mod ir;
pub mod lower;
pub mod rc;
pub mod spec;
pub mod tailrec;
pub mod unbox;
pub mod wide;

use crate::core::{DefId, Globals};
use cranelift_codegen::settings::{self, Configurable};


/// The descriptor the runtime reads (`checkers_rt::prog::install`).
pub(crate) fn descriptor(g: &Globals, p: &lower::Program) -> String {
    let mut d = String::new();
    let fns: Vec<(crate::core::ConId, usize)> = field_fns(g).into_iter().map(|(c, k, _)| (c, k)).collect();
    for (i, c) in g.cons.iter().enumerate() {
        let shown: String = c
            .fields
            .iter()
            .map(|f| if f.2 == crate::core::Icit::Expl && f.1 != crate::core::Mult::Zero { '1' } else { '0' })
            .collect();
        let templates: Vec<String> = (0..c.fields.len()).map(|k| field_template(g, crate::core::ConId(i as u32), k, &fns).write()).collect();
        let templates = if templates.is_empty() { "-".to_string() } else { templates.join(";") };
        d += &format!("con {} {} {} {} {} {templates}\n", c.name, g.arity_con(crate::core::ConId(i as u32)), g.arity_ty(c.ty), shown, c.ty.0);
    }
    // Types shown otherwise than by their constructors (#170).
    let wk = &g.well_known;
    for (i, t) in g.tys.iter().enumerate() {
        let id = Some(crate::core::TyId(i as u32));
        let kind = if id == wk.list {
            "list"
        } else if id == wk.array {
            "array"
        } else if &*t.module == "std.bag" && &*t.name == "Bag" {
            "bag"
        } else {
            "-"
        };
        let unboxed = t.ctors.first().and_then(|c| g.unboxed_field(*c).map(|k| format!("{}:{k}", c.0)));
        if kind != "-" || unboxed.is_some() {
            d += &format!("ty {i} {kind} {}\n", unboxed.as_deref().unwrap_or("-"));
        }
    }
    for n in &p.names {
        d += &format!("def {n}\n");
    }
    // Each type with a hand-written `Debug`: which of the instances'
    // functions shows it (#126), how many type parameters it takes, and
    // whether it is the standard library's (`std`), which the derived form
    // uses too: it is how `String` is shown.
    for (k, (t, f)) in g.well_known.debug_insts.iter().enumerate() {
        let from = if g.defs[f.0 as usize].module.starts_with("std.") { "std" } else { "-" };
        d += &format!("debug {} {k} {} {from}\n", t.0, lower::type_params(g, *f));
    }
    let wk = &g.well_known;
    let find = |module: &str, name: &str| {
        g.cons.iter().position(|c| &*c.name == name && &*g.tys[c.ty.0 as usize].module == module).map(|i| i as u32)
    };
    let known: [(&str, Option<u32>); 17] = [
        ("true", wk.true_con.map(|c| c.0)),
        ("false", wk.false_con.map(|c| c.0)),
        ("some", wk.some.map(|c| c.0)),
        ("none", wk.none.map(|c| c.0)),
        ("ok", wk.ok.map(|c| c.0)),
        ("err", wk.err.map(|c| c.0)),
        ("nil", wk.nil.map(|c| c.0)),
        ("cons", wk.cons.map(|c| c.0)),
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

/// The fields whose types are computed from earlier fields (#170), in the
/// order of the runtime's table of functions computing them: constructor,
/// field, and its type.
pub(crate) fn field_fns(g: &Globals) -> Vec<(crate::core::ConId, usize, crate::core::Tm)> {
    let mut out = Vec::new();
    for (i, ci) in g.cons.iter().enumerate() {
        let c = crate::core::ConId(i as u32);
        for k in 0..ci.fields.len() {
            if g.is_runtime_field(c, k) && ci.fields[k].2 == crate::core::Icit::Expl {
                if let crate::core::FieldType::FromFields(t) = crate::core::field_type(g, c, k) {
                    out.push((c, k, t));
                }
            }
        }
    }
    out
}

/// Field `k` of constructor `c`'s type, from its type's parameters (#170);
/// `fns`: the fields whose types are computed, in their table's order.
fn field_template(g: &Globals, c: crate::core::ConId, k: usize, fns: &[(crate::core::ConId, usize)]) -> checkers_rt::desc::Template {
    use crate::core::Desc;
    use checkers_rt::desc::Template;
    if let Some(i) = fns.iter().position(|x| *x == (c, k)) {
        return Template::Fn(i);
    }
    let ci = &g.cons[c.0 as usize];
    let np = g.arity_ty(ci.ty);
    let env = std::rc::Rc::new((0..np + k).map(crate::core::Val::var).collect::<Vec<_>>());
    let v = crate::core::eval(g, &env, &ci.fields[k].3);
    fn go(d: &Desc, np: usize) -> Template {
        match d {
            Desc::Known(tag, args) => Template::Con(*tag, args.iter().map(|a| go(a, np)).collect()),
            Desc::Var(l) if *l < np => Template::Param(*l),
            _ => Template::Unknown,
        }
    }
    go(&crate::core::desc_of(g, &v), np)
}

/// Closure-convert and reference-count the program, for a machine whose
/// functions return at most `max_parts` words (`codegen::return_words`).
fn prepare(g: &Globals, staged: Option<&crate::stage::Staged>, main: DefId, max_parts: usize) -> lower::Program {
    let mut p = lower::lower(g, staged, main);
    p.max_parts = max_parts;
    rc_new(g, &mut p);
    p
}

/// Code generation for this machine, as `ckc build` writes it.
fn host_isa() -> Result<std::sync::Arc<dyn cranelift_codegen::isa::TargetIsa>, String> {
    cranelift_native::builder()?.finish(flags()?).map_err(|e| e.to_string())
}

/// The settings for compiled programs: optimized, position independent.
fn flags() -> Result<settings::Flags, String> {
    let mut fb = settings::builder();
    fb.set("opt_level", "speed").map_err(|e| e.to_string())?;
    fb.set("is_pic", "true").map_err(|e| e.to_string())?;
    // Cranelift's tail calls rely on frame pointers.
    fb.set("preserve_frame_pointers", "true").map_err(|e| e.to_string())?;
    Ok(settings::Flags::new(fb))
}

/// The most words a function returns in registers on this machine.
pub fn host_return_words() -> usize {
    static WORDS: std::sync::OnceLock<usize> = std::sync::OnceLock::new();
    *WORDS.get_or_init(|| host_isa().map_or(1, |isa| codegen::return_words(&*isa)))
}

/// Reference counting for the functions added since the last call.
pub(crate) fn rc_new(g: &Globals, p: &mut lower::Program) {
    let fields_of = |c: u32| g.cons[c as usize].fields.len();
    let from = p.rc_done;
    tailrec::program(&mut p.funcs, from, g.well_known.nil.map(|c| c.0));
    unbox::program(p, from);
    for f in &mut p.funcs[from..] {
        f.body = rc::forward_aliases(std::mem::replace(&mut f.body, lower::E::Erased));
    }
    rc::infer_borrowed(&p.funcs, from, &mut p.borrowed, &fields_of);
    let rets: Vec<usize> = p.funcs.iter().map(|f| f.rets).collect();
    let rets = |f: u32| rets[f as usize];
    let to = p.funcs.len();
    for (i, f) in p.funcs[from..].iter_mut().enumerate() {
        rc::function((from + i) as u32, f, &fields_of, &p.borrowed, &rets);
    }
    // A closure's code takes its arguments owned: a function with borrowed
    // parameters made a closure (as a value, or as `main`) is entered
    // through one that drops them after the call.
    let mut closures = Vec::new();
    if let Some(lower::DefShape::Fn { func, .. }) = p.defs.get(&p.main) {
        closures.push(*func);
    }
    let mut values = Vec::new();
    for f in &p.funcs[from..to] {
        rc::closures_in(&f.body, &mut values, &mut closures);
    }
    for d in values {
        if let Some(lower::DefShape::Fn { func, .. }) = p.defs.get(&d) {
            closures.push(*func);
        }
    }
    for i in closures {
        if let (Some(b), false) = (p.borrowed.get(&i), p.entries.contains_key(&i)) {
            let e = rc::owned_entry(i, &p.funcs[i as usize], b);
            p.entries.insert(i, p.funcs.len() as u32);
            p.funcs.push(e);
        }
    }
    if std::env::var_os("CHECKERS_NATIVE_DUMP").is_some() {
        for (i, f) in p.funcs.iter().enumerate().skip(from) {
            let rets = if f.rets == 1 { String::new() } else { format!(", {} results", f.rets) };
            eprintln!("ckf_{i} {} ({} params{rets}):\n{}", f.name, f.params.len(), dump(&f.body, 1));
        }
    }
    p.rc_done = p.funcs.len();
}

/// An in-memory module for this machine, with the runtime's symbols.
pub(crate) fn jit_module() -> cranelift_jit::JITModule {
    jit_module_with(&[])
}

/// `jit_module`, with some of the runtime's symbols at other addresses.
fn jit_module_with(instead: &[(&'static str, *const u8)]) -> cranelift_jit::JITModule {
    let mut jb = jit_builder();
    jb.symbol("ck_invoke", shared_invoke() as *const u8);
    for (name, ptr) in checkers_rt::symbols() {
        let ptr = instead.iter().find(|(n, _)| *n == name).map_or(ptr, |(_, p)| *p);
        jb.symbol(name, ptr);
    }
    cranelift_jit::JITModule::new(jb)
}

fn jit_builder() -> cranelift_jit::JITBuilder {
    // Cranelift's tail calls rely on frame pointers.
    cranelift_jit::JITBuilder::with_flags(
        &[("opt_level", "speed"), ("preserve_frame_pointers", "true")],
        cranelift_module::default_libcall_names(),
    )
    .expect("a JIT for this machine")
}

/// The Rust-to-native dispatcher depends only on the host's calling
/// conventions, not on a program. Compile it once for all JIT modules,
/// including the evaluators created while checking types and staging.
fn shared_invoke() -> checkers_rt::prog::Invoke {
    static INVOKE: std::sync::OnceLock<checkers_rt::prog::Invoke> = std::sync::OnceLock::new();
    *INVOKE.get_or_init(|| {
        let g = Globals::default();
        let module = cranelift_jit::JITModule::new(jit_builder());
        let mut gen = codegen::Gen::new(module, lower::Program::new(&g, None), &g);
        gen.define_new();
        gen.m.finalize_definitions().expect("finish the native dispatcher");
        let code = gen.m.get_finalized_function(gen.invoke);
        // The dispatcher has the runtime's Invoke signature. Its code
        // must outlive every program and every thread using it.
        let invoke = unsafe { std::mem::transmute::<*const u8, checkers_rt::prog::Invoke>(code) };
        std::mem::forget(gen.m);
        invoke
    })
}

fn dump(e: &lower::E, d: usize) -> String {
    use lower::E;
    let ind = "  ".repeat(d);
    match e {
        E::Let(x, a, b) => format!("{ind}let v{x} =\n{}\n{}", dump(a, d + 1), dump(b, d)),
        E::Dup(x, b) => format!("{ind}dup v{x}\n{}", dump(b, d)),
        E::Drop(x, b) => format!("{ind}drop v{x}\n{}", dump(b, d)),
        E::DropReuse(x, t, n, b) => format!("{ind}v{t} = drop_reuse v{x} ({n})\n{}", dump(b, d)),
        E::At(o, b) => format!("{ind}at def{o}:\n{}", dump(b, d + 1)),
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
        E::Multi(xs) => format!("{ind}multi({})", xs.iter().map(|a| dump(a, 0).trim().to_string()).collect::<Vec<_>>().join(", ")),
        E::LetMulti(xs, a, b) => format!(
            "{ind}let {} =\n{}\n{}",
            xs.iter().map(|x| format!("v{x}")).collect::<Vec<_>>().join(" "),
            dump(a, d + 1),
            dump(b, d)
        ),
        E::Str(s) => format!("{ind}{s:?}"),
        E::Static(..) => format!("{ind}static"),
        other => format!("{ind}{}", match other {
            E::Erased => "erased".to_string(),
            E::Unit => "()".to_string(),
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
    run_in(jit_module(), g, staged, main, args, threads)
}

fn run_in(module: cranelift_jit::JITModule, g: &Globals, staged: Option<&crate::stage::Staged>, main: DefId, args: &[String], threads: usize) -> i32 {
    let p = prepare(g, staged, main, host_return_words());
    // The check (§8.9): a compiler bug, and the program doesn't run.
    if !p.residual.is_empty() {
        for r in &p.residual {
            eprintln!("{r}");
        }
        return 101;
    }
    let desc = descriptor(g, &p);
    let mut gen = codegen::Gen::importing_invoke(module, p, g);
    gen.define_new();
    let main_clo = gen.main_closure();
    let debug = gen.debug_table();
    let mut module = gen.m;
    module.finalize_definitions().expect("finish native code");
    let debug = match debug {
        Some(codegen::Placed::Word(x)) => x,
        Some(codegen::Placed::Data(d, o)) => module.get_finalized_data(d).0 as u64 + o as u64,
        None => 0,
    };
    let (clo, _) = module.get_finalized_data(main_clo);
    let invoke = shared_invoke();
    let main_w = clo as u64;
    let owner = main.0;
    let args = args.to_vec();
    // `main` and its callees may recurse deeply: a large stack.
    let code = std::thread::Builder::new()
        .stack_size(1 << 30)
        .spawn(move || checkers_rt::entry::run_main(&desc, invoke, debug, main_w, owner, &args, threads))
        .expect("spawn the main thread")
        .join()
        .unwrap_or(70);
    // The code must outlive every thread that runs it.
    std::mem::forget(module);
    code
}

/// The program as an object file for `isa`, with a C `main`.
pub fn object(
    g: &Globals,
    staged: Option<&crate::stage::Staged>,
    main: DefId,
    isa: std::sync::Arc<dyn cranelift_codegen::isa::TargetIsa>,
) -> Result<Vec<u8>, String> {
    let p = prepare(g, staged, main, codegen::return_words(&*isa));
    if !p.residual.is_empty() {
        return Err(p.residual.join("\n"));
    }
    let desc = descriptor(g, &p);
    let ob = cranelift_object::ObjectBuilder::new(isa, "checkers_program", cranelift_module::default_libcall_names())
        .map_err(|e| e.to_string())?;
    let module = cranelift_object::ObjectModule::new(ob);
    let mut gen = codegen::Gen::new(module, p, g);
    gen.define_new();
    gen.define_c_main(&desc);
    gen.m.finish().emit().map_err(|e| e.to_string())
}

/// Write an executable (`checkers build`).
pub fn build(g: &Globals, staged: Option<&crate::stage::Staged>, main: DefId, out: &std::path::Path) -> Result<(), String> {
    let bytes = object(g, staged, main, host_isa()?)?;
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
        .args(SYSTEM_LIBS)
        .status()
        .map_err(|e| format!("running the C compiler to link: {e}"))?;
    let _ = std::fs::remove_dir_all(&dir);
    if !status.success() {
        return Err(format!("linking failed ({status})"));
    }
    Ok(())
}

/// The system libraries the runtime (a Rust static library) needs.
#[cfg(target_os = "linux")]
const SYSTEM_LIBS: &[&str] = &["-lpthread", "-ldl", "-lm", "-lrt", "-lutil", "-lgcc_s", "-lc"];
/// On macOS everything is in libSystem, which the C compiler links anyway.
#[cfg(target_vendor = "apple")]
const SYSTEM_LIBS: &[&str] = &[];

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

#[cfg(test)]
mod tests {
    use super::*;

    const MACHINES: [(&str, usize); 4] =
        [("x86_64-unknown-linux-gnu", 8), ("x86_64-apple-darwin", 8), ("aarch64-unknown-linux-gnu", 6), ("aarch64-apple-darwin", 6)];

    fn isa(triple: &str) -> std::sync::Arc<dyn cranelift_codegen::isa::TargetIsa> {
        cranelift_codegen::isa::lookup_by_name(triple).expect(triple).finish(flags().unwrap()).expect(triple)
    }

    /// Each machine returns as many words in registers as its `tail`
    /// calling convention has registers for, and no more.
    #[test]
    fn return_words_by_machine() {
        for (triple, n) in MACHINES {
            assert_eq!(codegen::return_words(&*isa(triple)), n, "{triple}");
        }
    }

    /// The shared dispatcher calls code in independent modules at every
    /// supported arity, including arguments passed on the stack. Defining
    /// them a batch at a time or one at a time gives the same results.
    #[test]
    fn shared_dispatcher_calls_every_arity() {
        use checkers_rt::word as w;
        for (offset, incremental) in [(10, false), (100, true)] {
            let g = Globals::default();
            let mut gen = codegen::Gen::importing_invoke(jit_module(), lower::Program::new(&g, None), &g);
            for n in 0..=lower::MAX_ARITY {
                gen.p.funcs.push(lower::Func {
                    name: format!("arity_{n}"),
                    owner: lower::NO_OWNER,
                    kind: lower::FnKind::Global,
                    params: (0..n as u32).collect(),
                    body: if n == 0 { lower::E::Int(offset) } else { lower::E::Var(n as u32 - 1) },
                    nvars: n as u32,
                    rets: 1,
                    bounds: Default::default(),
                });
                if incremental {
                    gen.define_new();
                    gen.m.finalize_definitions().unwrap();
                }
            }
            gen.define_new();
            gen.m.finalize_definitions().unwrap();
            let invoke = shared_invoke();
            for n in 0..=lower::MAX_ARITY {
                let args: Vec<_> = (0..n).map(|i| w::mk_int(offset + i as i64)).collect();
                let code = gen.m.get_finalized_function(gen.func_id(n as u32)) as u64;
                let result = invoke(code, w::ERASED, args.as_ptr(), n as u64);
                assert_eq!(result, w::mk_int(offset + n.saturating_sub(1) as i64), "arity {n}");
            }
            // No values or threads retain this module's code.
            unsafe { gen.m.free_memory() };
        }
    }

    /// The functions of a test program in tests/run/, ready to compile.
    fn funcs_of(name: &'static str, f: impl FnOnce(&lower::Program) + Send + 'static) {
        let path = format!("{}/tests/run/{name}", env!("CARGO_MANIFEST_DIR"));
        let text = std::fs::read_to_string(&path).unwrap();
        let dir = std::path::Path::new(&path).parent().unwrap().to_path_buf();
        crate::with_big_stack(move || {
            let (e, main, staged, report) = crate::ready_to_run(name, &text, &dir, false).map_err(|r| r.report).unwrap();
            assert_eq!(report, "");
            f(&prepare(&e.g, Some(&staged), main, host_return_words()));
        })
    }

    /// A copy made for a known dictionary takes neither the dictionary nor
    /// the type (tests/run/copy_params.ck): `lo`'s copies take `x` and `y`.
    /// A copy that would take nothing keeps one parameter. The copies are
    /// read as `spec` makes them, before small functions are inlined.
    #[test]
    fn copies_take_no_dictionaries() {
        funcs_of("copy_params.ck", |p| {
            let specs = p.specs.borrow();
            let arity = |name: &str| {
                let mut out: Vec<usize> = specs
                    .copies
                    .iter()
                    .filter(|c| p.names[c.of.0 as usize] == name)
                    .map(|c| {
                        let (mut n, mut b) = (0, &c.body);
                        while let crate::core::Tm::Lam(_, _, _, x) = b {
                            n += 1;
                            b = x;
                        }
                        n
                    })
                    .collect();
                out.dedup();
                out
            };
            // `lo`'s copies for a dictionary take its two values; the copy for
            // `lo 5 3` in `pick`'s copy (both known, §8.9) keeps one.
            assert_eq!(arity("lo"), [2, 1]);
            assert_eq!(arity("nothing"), [1]);
        })
    }

    /// A standard library function called from a program with a value known
    /// when compiling is specialized on it (§14), as the program's own are
    /// (tests/run/std_specialized.ck): `take 2 args` calls a copy of `take`
    /// that takes only the list.
    #[test]
    fn std_calls_are_specialized_on_known_values() {
        funcs_of("std_specialized.ck", |p| {
            let specs = p.specs.borrow();
            let arities: Vec<usize> = specs
                .copies
                .iter()
                .filter(|c| p.names[c.of.0 as usize] == "take")
                .map(|c| {
                    let (mut n, mut b) = (0, &c.body);
                    while let crate::core::Tm::Lam(_, _, _, x) = b {
                        n += 1;
                        b = x;
                    }
                    n
                })
                .collect();
            assert!(arities.contains(&1), "take's copies take {arities:?} parameters");
        })
    }

    /// A value given through `std.hint.blackbox` is not known when compiling
    /// (§8.9, tests/run/blackbox.ck): `main` calls it and adds at run time.
    #[test]
    fn blackbox_is_not_folded() {
        funcs_of("blackbox.ck", |p| {
            let main = p.funcs.iter().find(|f| f.name == "main").expect("main");
            let code = dump(&main.body, 0);
            assert!(code.contains("ckb_hint_blackbox") && code.contains("Prim(Add"), "{code}");
        })
    }

    /// Whether `e` duplicates or drops `v`.
    fn counts(e: &lower::E, v: lower::V) -> bool {
        use lower::E;
        match e {
            E::Dup(x, b) | E::Drop(x, b) | E::DropReuse(x, _, _, b) => *x == v || counts(b, v),
            E::Borrow { drops, args, .. } => drops.contains(&v) || args.iter().any(|a| counts(a, v)),
            E::Let(_, a, b) | E::LetMulti(_, a, b) => counts(a, v) || counts(b, v),
            E::Call { args, .. } | E::Tuple(args) | E::Par(args) | E::Multi(args) => args.iter().any(|a| counts(a, v)),
            E::Apply { f, args, .. } => counts(f, v) || args.iter().any(|a| counts(a, v)),
            E::Con { fields, .. } => fields.iter().any(|a| counts(a, v)),
            E::Case { arms, lits, default, .. } => {
                arms.iter().any(|a| counts(&a.body, v)) || lits.iter().any(|(_, b)| counts(b, v)) || default.as_ref().is_some_and(|d| counts(d, v))
            }
            E::At(_, b) => counts(b, v),
            _ => false,
        }
    }

    /// A parameter a loop only reads and passes on unchanged is borrowed
    /// (tests/run/borrowed_params.ck): `walk`'s `n` is neither duplicated
    /// nor dropped; `longer` borrows the string it compares with and owns
    /// the list whose cells it reuses. Both are recursive, so neither is
    /// inlined.
    #[test]
    fn loops_borrow_what_they_pass_on() {
        funcs_of("borrowed_params.ck", |p| {
            let func = |name: &str| p.funcs.iter().position(|f| f.name == name).unwrap();
            let walk = func("walk");
            assert_eq!(p.borrowed.get(&(walk as u32)).map(Vec::as_slice), Some(&[true, false, false][..]));
            assert!(!counts(&p.funcs[walk].body, p.funcs[walk].params[0]));
            assert_eq!(p.borrowed.get(&(func("longer") as u32)).map(Vec::as_slice), Some(&[true, false][..]));
        })
    }

    /// Results returned as their parts, six to eight words wide
    /// (tests/run/unboxed_wide.ck), compile for every machine: none returns
    /// more words than the machine has registers for, and each returns as
    /// many as it can.
    #[test]
    fn wide_results_compile_for_every_machine() {
        crate::with_big_stack(|| {
            let path = concat!(env!("CARGO_MANIFEST_DIR"), "/tests/run/unboxed_wide.ck");
            let text = std::fs::read_to_string(path).unwrap();
            let dir = std::path::Path::new(path).parent().unwrap();
            let (e, main, staged, report) = crate::ready_to_run("unboxed_wide.ck", &text, dir, false).map_err(|r| r.report).unwrap();
            assert_eq!(report, "");
            for (triple, n) in MACHINES {
                let p = prepare(&e.g, Some(&staged), main, n);
                let widest = p.funcs.iter().map(|f| f.rets).max().unwrap();
                assert_eq!(widest, n, "{triple}: the widest result");
                object(&e.g, Some(&staged), main, isa(triple)).unwrap_or_else(|m| panic!("{triple}: {m}"));
            }
        })
    }

    /// Each function's name and machine code for `triple`, of the program
    /// in `tests/run/<name>.ck`, every runtime error's owner written as 0:
    /// code put into another function names where it came from.
    fn machine_code(name: &str, triple: &str) -> Vec<(String, String)> {
        machine_code_as(name, triple, true)
    }

    /// `machine_code`, as if the program were `proved` or not (§13.3).
    fn machine_code_as(name: &str, triple: &str, proved: bool) -> Vec<(String, String)> {
        let path = format!("{}/tests/run/{name}.ck", env!("CARGO_MANIFEST_DIR"));
        let text = std::fs::read_to_string(&path).unwrap();
        let dir = std::path::Path::new(&path).parent().unwrap();
        let (mut e, main, staged, report) = crate::ready_to_run(&format!("{name}.ck"), &text, dir, false).map_err(|r| r.report).unwrap();
        assert_eq!(report, "");
        assert!(e.g.proved, "`{name}` relies on an `admit`");
        e.g.proved = proved;
        let isa = isa(triple);
        let p = prepare(&e.g, Some(&staged), main, codegen::return_words(&*isa));
        let ob = cranelift_object::ObjectBuilder::new(isa, "test", cranelift_module::default_libcall_names()).unwrap();
        let mut gen = codegen::Gen::new(cranelift_object::ObjectModule::new(ob), p, &e.g);
        gen.disasm = Some(Vec::new());
        gen.define_new();
        gen.disasm.unwrap()
    }

    /// The code of the function named `f` (the only one).
    fn code_of<'a>(code: &'a [(String, String)], f: &str) -> &'a str {
        let found: Vec<&(String, String)> = code.iter().filter(|(n, _)| n == f).collect();
        assert_eq!(found.len(), 1, "functions named `{f}`");
        &found[0].1
    }

    /// The table of hand-written `Debug` instances is static data, laid out
    /// when the program is compiled (tests/run/debug_table_static.ck): its
    /// code is its value, so the runtime is handed the value and runs
    /// nothing to build it.
    #[test]
    fn debug_table_is_static() {
        funcs_of("debug_table_static.ck", |p| {
            let f = p.debug.expect("a table of `Debug` instances");
            assert!(matches!(p.funcs[f as usize].body, lower::E::Static(..)), "{}", dump(&p.funcs[f as usize].body, 0));
        })
    }

    /// Known parts of code are computed when compiling (§8.9,
    /// tests/run/folded.ck): `x < LIMIT * 2` compiles as `x < 2097152`, and
    /// `scale 3 x` calls a copy of `scale` for `3` whose code is `by_hand`'s,
    /// the general `scale` not being compiled at all.
    #[test]
    fn known_parts_are_computed() {
        crate::with_big_stack(|| {
            for (triple, _) in MACHINES {
                let code = machine_code("folded", triple);
                assert_eq!(code_of(&code, "under"), code_of(&code, "under_number"), "{triple}");
                assert_eq!(code_of(&code, "scale"), code_of(&code, "by_hand"), "{triple}");
            }
        })
    }

    /// Code put into a function from another (`at`: a small function
    /// inlined) compiles as the same code written there: a comparison's
    /// `Bool` is branched on, not built and dropped, and a remainder by a
    /// small integer is known to be one (tests/run/at_compare.ck).
    #[test]
    fn code_from_another_function_compiles_the_same() {
        crate::with_big_stack(|| {
            for (triple, _) in MACHINES {
                let code = machine_code("at_compare", triple);
                assert_eq!(code_of(&code, "pick"), code_of(&code, "pick_int"), "{triple}");
                assert_eq!(code_of(&code, "step"), code_of(&code, "step_int"), "{triple}");
            }
        })
    }

    /// Integers whose types bound them (tests/run/bounded_ints.ck) need no
    /// runtime: no small-integer test, overflow check or zero test, so no
    /// slow path calling the runtime and no `drop`s. A product of two `I32`s
    /// can reach 2^62, past the small integers: it keeps its check.
    #[test]
    fn bounded_integers_need_no_runtime() {
        crate::with_big_stack(|| {
            for (triple, _) in MACHINES {
                let code = machine_code("bounded_ints", triple);
                for f in ["add_bytes", "spread", "halves", "take"] {
                    let c = code_of(&code, f);
                    assert!(!c.contains("ext_name"), "{triple}: `{f}` calls the runtime:\n{c}");
                }
                assert!(code_of(&code, "product").contains("ext_name"), "{triple}: `product` without its overflow path");
            }
        })
    }

    /// A value known at compile time compiles as the same value written as
    /// a literal (tests/run/known_bounds.ck): as a bound, `a < math.pow 2
    /// 32` as `a < 4294967296`, `a < LIMIT` as `a < 1000`, and a sealed
    /// function's value (`std.array.count`, the program's own
    /// `limits.power_of_two`) as `256`, and so is a value computed by a
    /// function of the same module (`own_size`); in code, `LIMIT` as `1000`.
    #[test]
    fn known_bounds_compile_as_literals() {
        crate::with_big_stack(|| {
            for (triple, _) in MACHINES {
                let code = machine_code("known_bounds", triple);
                assert_eq!(code_of(&code, "by_call"), code_of(&code, "by_literal"), "{triple}");
                assert_eq!(code_of(&code, "by_name"), code_of(&code, "by_number"), "{triple}");
                assert_eq!(code_of(&code, "with_name"), code_of(&code, "with_number"), "{triple}");
                assert_eq!(code_of(&code, "by_std"), code_of(&code, "by_bytes"), "{triple}");
                assert_eq!(code_of(&code, "by_own"), code_of(&code, "by_bytes"), "{triple}");
                assert_eq!(code_of(&code, "by_module"), code_of(&code, "by_bytes"), "{triple}");
            }
        })
    }

    /// A constant only code generation wants (tests/run/known_release.ck,
    /// `FAR`, past the work limit): compiled as its value in a release
    /// build, not in a development one, where it costs too much (§8.9).
    #[test]
    fn release_builds_compute_constants_to_completion() {
        crate::with_big_stack(|| {
            let path = concat!(env!("CARGO_MANIFEST_DIR"), "/tests/run/known_release.ck");
            let text = std::fs::read_to_string(path).unwrap();
            let dir = std::path::Path::new(path).parent().unwrap();
            for release in [false, true] {
                let (e, ..) = crate::ready_to_run("known_release.ck", &text, dir, release).map_err(|r| r.report).unwrap();
                let far = e.g.defs.iter().position(|d| &*d.name == "FAR" && &*d.module == "known_release").unwrap();
                let known = crate::core::known_const(&e.g, crate::core::DefId(far as u32));
                assert_eq!(known.is_some(), release, "release: {release}");
            }
        })
    }

    /// Constants of every type known at compile time are static data
    /// (§8.9): a program's code has no constant computed on first use
    /// (`FnKind::Caf`, read through a slot checked for `UNSET`).
    #[test]
    fn known_constants_have_no_first_use_code() {
        crate::with_big_stack(|| {
            for name in ["known_baked", "known_arrays", "known_closures"] {
                let path = format!("{}/tests/run/{name}.ck", env!("CARGO_MANIFEST_DIR"));
                let text = std::fs::read_to_string(&path).unwrap();
                let dir = std::path::Path::new(&path).parent().unwrap().to_path_buf();
                let (e, main, staged, _) = crate::ready_to_run(&format!("{name}.ck"), &text, &dir, false).map_err(|r| r.report).unwrap();
                let p = super::prepare(&e.g, Some(&staged), main, super::host_return_words());
                // A definition's constant (not the closed code a program
                // runs once at start, its `Debug` instances' table).
                let cafs: Vec<&str> = p
                    .funcs
                    .iter()
                    .filter(|f| matches!(f.kind, super::lower::FnKind::Caf) && (f.owner as usize) < e.g.defs.len())
                    .map(|f| f.name.as_str())
                    .collect();
                assert!(cafs.is_empty(), "{name}: computed on first use: {cafs:?}");
            }
        })
    }

    /// A guarded operation whose obligation is proved has no run-time check
    /// (§13.3, tests/run/proved_guards.ck): a division by a divisor proved
    /// not zero is one whose bounds show it, and a `Nat` subtraction, a
    /// division and an index are shorter than where their checks are kept.
    /// (A `when`'s check is the runtime's, told whether to make it.)
    #[test]
    fn proved_operations_have_no_checks() {
        crate::with_big_stack(|| {
            for (triple, _) in MACHINES {
                let code = machine_code("proved_guards", triple);
                assert_eq!(code_of(&code, "nonzero"), code_of(&code, "positive"), "{triple}");
                let checked = machine_code_as("proved_guards", triple, false);
                for f in ["nat_less", "nonzero", "byte_at"] {
                    let (proved, kept) = (code_of(&code, f), code_of(&checked, f));
                    assert!(proved.lines().count() < kept.lines().count(), "{triple}: `{f}` keeps its check:\n{proved}");
                }
            }
        })
    }

    /// Integers' inline paths (tests/run/small_int_edges.ck: overflow
    /// checks, constants, comparisons branched on; wide_int_edges.ck: on
    /// 128 bits) compile for every machine, whose overflow-checking and
    /// 128-bit instructions differ.
    #[test]
    fn integer_paths_compile_for_every_machine() {
        crate::with_big_stack(|| {
            for name in ["small_int_edges.ck", "wide_int_edges.ck"] {
                let path = format!("{}/tests/run/{name}", env!("CARGO_MANIFEST_DIR"));
                let text = std::fs::read_to_string(&path).unwrap();
                let dir = std::path::Path::new(&path).parent().unwrap();
                let (e, main, staged, report) = crate::ready_to_run(name, &text, dir, false).map_err(|r| r.report).unwrap();
                assert_eq!(report, "");
                for (triple, _) in MACHINES {
                    object(&e.g, Some(&staged), main, isa(triple)).unwrap_or_else(|m| panic!("{name}, {triple}: {m}"));
                }
            }
        })
    }

    /// Calls of the runtime's arithmetic, counted.
    static ARITHMETIC: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(0);

    fn counted() {
        ARITHMETIC.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
    }

    extern "C" fn add(a: u64, b: u64) -> u64 {
        counted();
        checkers_rt::ops::ck_add(a, b)
    }
    extern "C" fn sub(a: u64, b: u64) -> u64 {
        counted();
        checkers_rt::ops::ck_sub(a, b)
    }
    extern "C" fn natsub(a: u64, b: u64, o: u64) -> u64 {
        counted();
        checkers_rt::ops::ck_natsub(a, b, o)
    }
    extern "C" fn mul(a: u64, b: u64) -> u64 {
        counted();
        checkers_rt::ops::ck_mul(a, b)
    }
    extern "C" fn div(a: u64, b: u64, o: u64) -> u64 {
        counted();
        checkers_rt::ops::ck_div(a, b, o)
    }
    extern "C" fn rem(a: u64, b: u64, o: u64) -> u64 {
        counted();
        checkers_rt::ops::ck_rem(a, b, o)
    }
    extern "C" fn neg(a: u64) -> u64 {
        counted();
        checkers_rt::ops::ck_neg(a)
    }
    extern "C" fn cmp(a: u64, b: u64) -> i64 {
        counted();
        checkers_rt::ops::ck_cmp(a, b)
    }
    extern "C" fn eq(a: u64, b: u64, o: u64) -> u64 {
        counted();
        checkers_rt::ops::ck_eq(a, b, o)
    }
    extern "C" fn ne(a: u64, b: u64, o: u64) -> u64 {
        counted();
        checkers_rt::ops::ck_ne(a, b, o)
    }

    /// Numbers within 128 bits (tests/run/wide_int_inline.ck: small
    /// integers whose operations overflow a word, and two-word numbers)
    /// are computed in compiled code (the program's 128-bit functions):
    /// running the program calls none of the runtime's arithmetic.
    #[test]
    fn numbers_within_128_bits_need_no_runtime() {
        crate::with_big_stack(|| {
            let path = concat!(env!("CARGO_MANIFEST_DIR"), "/tests/run/wide_int_inline.ck");
            let text = std::fs::read_to_string(path).unwrap();
            let dir = std::path::Path::new(path).parent().unwrap();
            let (e, main, staged, report) = crate::ready_to_run("wide_int_inline.ck", &text, dir, false).map_err(|r| r.report).unwrap();
            assert_eq!(report, "");
            let counting: [(&'static str, *const u8); 10] = [
                ("ck_add", add as *const u8),
                ("ck_sub", sub as *const u8),
                ("ck_natsub", natsub as *const u8),
                ("ck_mul", mul as *const u8),
                ("ck_div", div as *const u8),
                ("ck_rem", rem as *const u8),
                ("ck_neg", neg as *const u8),
                ("ck_cmp", cmp as *const u8),
                ("ck_eq", eq as *const u8),
                ("ck_ne", ne as *const u8),
            ];
            let code = run_in(jit_module_with(&counting), &e.g, Some(&staged), main, &[], 1);
            assert_eq!(code, 0);
            assert_eq!(ARITHMETIC.load(std::sync::atomic::Ordering::Relaxed), 0, "calls of the runtime's arithmetic");
        })
    }
}
