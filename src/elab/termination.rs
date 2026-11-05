//! Termination (§5.3): structural recursion, `decreasing` measures, `partial`.

use super::*;

impl Elab {
    pub fn check_termination(&mut self) {
        let fns: Vec<DefId> = std::mem::take(&mut self.module_fns);
        let calls: Vec<CallRec> = std::mem::take(&mut self.calls);
        let idx: HashMap<DefId, usize> = fns.iter().enumerate().map(|(i, d)| (*d, i)).collect();
        let n = fns.len();
        let mut edges: Vec<Vec<usize>> = vec![Vec::new(); n];
        for c in &calls {
            if let (Some(&a), Some(&b)) = (idx.get(&c.caller), idx.get(&c.callee)) {
                edges[a].push(b);
            }
        }

        // A total function may not call a partial one.
        for c in &calls {
            let caller = self.fn_meta.get(&c.caller).cloned().unwrap_or_default();
            let callee = self.fn_meta.get(&c.callee).cloned().unwrap_or_default();
            if !caller.partial && callee.partial {
                self.err(
                    Diagnostic::error(
                        "E0302",
                        format!("`{}` is `partial` (it may not terminate), so `{}` cannot call it", callee.name, caller.name),
                        c.span,
                    )
                    .with_help(format!("mark `{}` as `partial fn` too", caller.name)),
                );
            }
        }

        for scc in tarjan(&edges) {
            let recursive = scc.len() > 1 || edges[scc[0]].contains(&scc[0]);
            if !recursive {
                continue;
            }
            let members: Vec<DefId> = scc.iter().map(|&i| fns[i]).collect();
            let metas: Vec<FnMeta> = members.iter().map(|d| self.fn_meta.get(d).cloned().unwrap_or_default()).collect();
            if metas.iter().all(|m| m.partial || m.decreasing) {
                continue; // `decreasing` measures are checked by the prover (M5).
            }
            let inner: Vec<&CallRec> = calls
                .iter()
                .filter(|c| members.contains(&c.caller) && members.contains(&c.callee))
                .collect();
            if structural(&members, &metas, &inner) {
                continue;
            }
            // Report at the first recursive call made by a function without `decreasing`.
            let bad = inner
                .iter()
                .find(|c| {
                    let k = members.iter().position(|d| *d == c.caller).unwrap();
                    !metas[k].partial && !metas[k].decreasing
                })
                .copied();
            if let Some(c) = bad {
                let k = members.iter().position(|d| *d == c.caller).unwrap();
                let name = metas[k].name.clone();
                let msg = if members.len() == 1 {
                    format!("cannot show that `{name}` terminates: no argument gets structurally smaller in this recursive call")
                } else {
                    let names: Vec<String> = metas.iter().map(|m| format!("`{}`", m.name)).collect();
                    format!(
                        "cannot show that {} terminate: they call each other, and no argument gets structurally smaller",
                        names.join(", ")
                    )
                };
                self.err(
                    Diagnostic::error("E0301", msg, c.span)
                        .with_label("recursive call")
                        .with_help(format!(
                            "recurse on a part of a parameter you matched on, or add `decreasing <measure>` as the first line of `{name}`, or mark it `partial`"
                        )),
                );
            }
        }
    }
}

/// Is there a choice of one parameter per function such that every call
/// inside the group passes a strict subterm of the caller's chosen parameter
/// in the callee's chosen position?
fn structural(members: &[DefId], metas: &[FnMeta], calls: &[&CallRec]) -> bool {
    let arities: Vec<usize> = metas.iter().map(|m| m.params.len()).collect();
    if arities.contains(&0) {
        return false;
    }
    let total: usize = arities.iter().product();
    if total > 4096 {
        return false;
    }
    let mut choice = vec![0usize; members.len()];
    for k in 0..total {
        let mut r = k;
        for (i, a) in arities.iter().enumerate() {
            choice[i] = r % a;
            r /= a;
        }
        let ok = calls.iter().all(|c| {
            let fi = members.iter().position(|d| *d == c.caller).unwrap();
            let gi = members.iter().position(|d| *d == c.callee).unwrap();
            c.args.get(choice[gi]).copied().flatten() == Some(choice[fi])
        });
        if ok {
            return true;
        }
    }
    false
}

fn tarjan(edges: &[Vec<usize>]) -> Vec<Vec<usize>> {
    struct St<'a> {
        edges: &'a [Vec<usize>],
        index: Vec<Option<usize>>,
        low: Vec<usize>,
        on: Vec<bool>,
        stack: Vec<usize>,
        next: usize,
        out: Vec<Vec<usize>>,
    }
    fn visit(s: &mut St, v: usize) {
        s.index[v] = Some(s.next);
        s.low[v] = s.next;
        s.next += 1;
        s.stack.push(v);
        s.on[v] = true;
        for &w in &s.edges[v].clone() {
            match s.index[w] {
                None => {
                    visit(s, w);
                    s.low[v] = s.low[v].min(s.low[w]);
                }
                Some(iw) if s.on[w] => s.low[v] = s.low[v].min(iw),
                _ => {}
            }
        }
        if Some(s.low[v]) == s.index[v] {
            let mut comp = Vec::new();
            while let Some(w) = s.stack.pop() {
                s.on[w] = false;
                comp.push(w);
                if w == v {
                    break;
                }
            }
            s.out.push(comp);
        }
    }
    let n = edges.len();
    let mut s = St { edges, index: vec![None; n], low: vec![0; n], on: vec![false; n], stack: vec![], next: 0, out: vec![] };
    for v in 0..n {
        if s.index[v].is_none() {
            visit(&mut s, v);
        }
    }
    s.out
}
