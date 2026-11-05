//! Recursive-descent parser for the surface grammar (§9.2).

use super::ast::*;
use super::token::{Assoc, Kw, Op, Tok, Token};
use crate::diag::Diagnostic;
use crate::source::Span;

pub fn parse(tokens: Vec<Token>) -> (Module, Vec<Diagnostic>) {
    let mut p = Parser { toks: tokens, pos: 0, diags: Vec::new(), last_dedent: false, indent: 0, no_arrow: false };
    let m = p.module();
    (m, p.diags)
}

/// Marker: a diagnostic was already recorded.
struct Failed;
type PResult<T> = Result<T, Failed>;

struct Parser {
    toks: Vec<Token>,
    pos: usize,
    diags: Vec<Diagnostic>,
    /// The most recently consumed token was a DEDENT. A construct that ends in
    /// an indented block has already consumed its line end.
    last_dedent: bool,
    /// Current INDENT nesting, for error recovery.
    indent: usize,
    /// Parsing a match guard: `->` ends the guard instead of forming a function type.
    no_arrow: bool,
}

impl Parser {
    // ── token plumbing ──────────────────────────────────────────────────────

    fn peek(&self) -> &Tok {
        &self.toks[self.pos].tok
    }

    fn peek_at(&self, n: usize) -> &Tok {
        let i = (self.pos + n).min(self.toks.len() - 1);
        &self.toks[i].tok
    }

    fn tok(&self) -> &Token {
        &self.toks[self.pos]
    }

    fn span(&self) -> Span {
        self.toks[self.pos].span
    }

    fn prev_span(&self) -> Span {
        self.toks[self.pos.saturating_sub(1)].span
    }

    fn bump(&mut self) -> Token {
        let t = self.toks[self.pos].clone();
        match t.tok {
            Tok::Indent => self.indent += 1,
            Tok::Dedent => self.indent = self.indent.saturating_sub(1),
            _ => {}
        }
        self.last_dedent = t.tok == Tok::Dedent;
        if self.pos < self.toks.len() - 1 {
            self.pos += 1;
        }
        t
    }

    fn at(&self, t: &Tok) -> bool {
        self.peek() == t
    }

    fn at_kw(&self, k: Kw) -> bool {
        *self.peek() == Tok::Kw(k)
    }

    fn eat(&mut self, t: &Tok) -> bool {
        if self.at(t) {
            self.bump();
            true
        } else {
            false
        }
    }

    fn eat_kw(&mut self, k: Kw) -> bool {
        self.eat(&Tok::Kw(k))
    }

    fn error_here(&mut self, expected: &str) -> Failed {
        let found = self.peek().clone();
        let span = self.span();
        self.diags.push(
            Diagnostic::error("E0100", format!("expected {expected}, found {found}"), span)
                .with_label(format!("expected {expected}")),
        );
        Failed
    }

    fn expect(&mut self, t: Tok, what: &str) -> PResult<Token> {
        if self.at(&t) {
            Ok(self.bump())
        } else {
            Err(self.error_here(what))
        }
    }

    fn expect_kw(&mut self, k: Kw) -> PResult<Token> {
        self.expect(Tok::Kw(k), &format!("`{}`", k.as_str()))
    }

    /// End of a logical line: a NEWLINE, or a just-closed indented block.
    fn end_line(&mut self) -> PResult<()> {
        if self.eat(&Tok::Newline) || self.last_dedent {
            self.last_dedent = false;
            Ok(())
        } else if self.at(&Tok::LArrow) {
            let span = self.span();
            self.diags.push(
                Diagnostic::error("E0113", "`<-` binds an effectful result and must start a statement", span)
                    .with_help("write `x <- f a cap` on its own line; for a comparison with a negative number write `x < -1`"),
            );
            Err(Failed)
        } else {
            Err(self.error_here("end of line"))
        }
    }

    /// Expect NEWLINE INDENT, opening a block.
    fn open_block(&mut self, what: &str) -> PResult<()> {
        if !self.eat(&Tok::Newline) {
            return Err(self.error_here(&format!("end of line before {what}")));
        }
        if !self.eat(&Tok::Indent) {
            return Err(self.error_here(&format!("an indented {what}")));
        }
        Ok(())
    }

    fn ident(&mut self, what: &str) -> PResult<Ident> {
        match self.peek().clone() {
            Tok::LName(name) | Tok::UName(name) => {
                let span = self.bump().span;
                Ok(Ident { name, span })
            }
            _ => Err(self.error_here(what)),
        }
    }

    fn at_ident(&self) -> bool {
        matches!(self.peek(), Tok::LName(_) | Tok::UName(_))
    }

    /// Skip to the start of the next top-level declaration.
    fn recover_top(&mut self) {
        loop {
            let t = self.peek().clone();
            if t == Tok::Eof {
                return;
            }
            self.bump();
            if matches!(t, Tok::Newline | Tok::Dedent)
                && self.indent == 0
                && !self.at(&Tok::Indent)
                && !self.at(&Tok::Dedent)
            {
                self.last_dedent = false;
                return;
            }
        }
    }

    // ── module level ────────────────────────────────────────────────────────

    fn module(&mut self) -> Module {
        while self.eat(&Tok::Newline) {}
        let name = if self.at_kw(Kw::Module) {
            self.bump();
            match self.qname().and_then(|q| self.end_line().map(|_| q)) {
                Ok(q) => Some(q),
                Err(_) => {
                    self.recover_top();
                    None
                }
            }
        } else {
            let span = self.span();
            self.diags.push(
                Diagnostic::error("E0101", "a file must start with `module <name>`", span)
                    .with_help("add a line such as `module json` at the top of the file"),
            );
            None
        };
        let mut imports = Vec::new();
        while self.at_kw(Kw::Import) {
            match self.import() {
                Ok(i) => imports.push(i),
                Err(_) => self.recover_top(),
            }
        }
        let mut decls = Vec::new();
        while !self.at(&Tok::Eof) {
            if self.eat(&Tok::Newline) {
                continue;
            }
            if self.at(&Tok::Indent) {
                let span = self.span();
                self.diags.push(Diagnostic::error("E0102", "unexpected indented block", span));
                self.bump();
                self.recover_top();
                continue;
            }
            if self.at_kw(Kw::Import) {
                let span = self.span();
                self.diags.push(Diagnostic::error(
                    "E0103",
                    "imports must come before all declarations",
                    span,
                ));
                let _ = self.import();
                continue;
            }
            match self.decl() {
                Ok(d) => decls.push(d),
                Err(_) => self.recover_top(),
            }
        }
        Module { name, imports, decls }
    }

    fn qname(&mut self) -> PResult<QName> {
        let first = self.ident("a module name")?;
        let mut span = first.span;
        let mut parts = vec![first];
        while self.at(&Tok::Op(Op::Dot)) && !self.tok().space_before {
            self.bump();
            let p = self.ident("a name after `.`")?;
            span = span.to(p.span);
            parts.push(p);
        }
        Ok(QName { parts, span })
    }

    fn import(&mut self) -> PResult<Import> {
        let start = self.bump().span; // import
        let path = self.qname()?;
        let mut items = None;
        if self.eat(&Tok::LParen) {
            let mut v = Vec::new();
            if !self.at(&Tok::RParen) {
                loop {
                    v.push(self.ident("an imported name")?);
                    if !self.eat(&Tok::Comma) {
                        break;
                    }
                }
            }
            self.expect(Tok::RParen, "`)`")?;
            items = Some(v);
        }
        let alias = if self.eat_kw(Kw::As) { Some(self.ident("an alias")?) } else { None };
        let span = start.to(self.prev_span());
        self.end_line()?;
        Ok(Import { path, items, alias, span })
    }

    fn decl(&mut self) -> PResult<Decl> {
        let start = self.span();
        let export = if self.eat_kw(Kw::Export) {
            if self.eat_kw(Kw::Abstract) {
                Export::Abstract
            } else if self.eat_kw(Kw::Transparent) {
                Export::Transparent
            } else {
                Export::Yes
            }
        } else {
            Export::No
        };
        let kind = match self.peek() {
            Tok::Kw(Kw::Fn) | Tok::Kw(Kw::Partial) => self.fn_decl()?,
            Tok::Kw(Kw::Enum) => self.enum_decl()?,
            Tok::Kw(Kw::Record) => self.record_decl()?,
            Tok::Kw(Kw::Type) => self.alias_decl()?,
            Tok::Kw(Kw::Lemma) => self.lemma_decl()?,
            Tok::Kw(Kw::Let) => self.const_decl()?,
            Tok::Kw(Kw::Check) if export == Export::No => {
                self.bump();
                let expr = self.expr()?;
                self.end_line()?;
                DeclKind::Check { expr }
            }
            _ => return Err(self.error_here("a declaration (`fn`, `enum`, `record`, `type`, `lemma`, `let`, `check`)")),
        };
        if matches!(export, Export::Abstract) && !matches!(kind, DeclKind::Enum { .. } | DeclKind::Record { .. }) {
            self.diags.push(Diagnostic::error(
                "E0104",
                "`export abstract` applies only to `enum` and `record`",
                start,
            ));
        }
        if matches!(export, Export::Transparent) && !matches!(kind, DeclKind::Fn { .. }) {
            self.diags.push(Diagnostic::error("E0105", "`export transparent` applies only to `fn`", start));
        }
        Ok(Decl { export, kind, span: start.to(self.prev_span()) })
    }

    fn names_until_header_end(&mut self) -> Vec<Ident> {
        let mut v = Vec::new();
        while self.at_ident() {
            let t = self.bump();
            if let Tok::LName(n) | Tok::UName(n) = t.tok {
                v.push(Ident { name: n, span: t.span });
            }
        }
        v
    }

    fn params(&mut self) -> PResult<Vec<Param>> {
        let mut v = Vec::new();
        loop {
            let polarity = if self.at(&Tok::Op(Op::Add)) {
                self.bump();
                Some(Polarity::Pos)
            } else if self.at(&Tok::Op(Op::Sub)) {
                self.bump();
                Some(Polarity::Neg)
            } else {
                None
            };
            if polarity.is_none() && !self.at_ident() {
                return Ok(v);
            }
            let name = self.ident("a parameter name")?;
            v.push(Param { polarity, name });
        }
    }

    fn opt_constraints(&mut self) -> PResult<Vec<Constraint>> {
        if self.eat(&Tok::Colon) {
            self.constraints()
        } else {
            Ok(Vec::new())
        }
    }

    fn constraints(&mut self) -> PResult<Vec<Constraint>> {
        let mut v = vec![self.constraint()?];
        while self.eat(&Tok::Comma) {
            v.push(self.constraint()?);
        }
        Ok(v)
    }

    fn mult(&mut self) -> Mult {
        if self.eat_kw(Kw::Ghost) {
            Mult::Ghost
        } else if self.eat_kw(Kw::Own) {
            Mult::Own
        } else {
            Mult::Many
        }
    }

    fn constraint(&mut self) -> PResult<Constraint> {
        if self.at_ident() && *self.peek_at(1) == Tok::Tilde {
            let name = self.ident("a name")?;
            self.bump(); // ~
            let mult = self.mult();
            let ty = self.expr()?;
            Ok(Constraint::Typed { name, mult, ty })
        } else {
            Ok(Constraint::Pred(self.expr()?))
        }
    }

    fn fn_decl(&mut self) -> PResult<DeclKind> {
        let partial = self.eat_kw(Kw::Partial);
        self.expect_kw(Kw::Fn)?;
        let name = self.ident("a function name")?;
        let params = self.names_until_header_end();
        let result = if self.eat(&Tok::Arrow) { Some(self.ident("a result name after `->`")?) } else { None };
        let constraints = self.opt_constraints()?;
        self.open_block("function body")?;
        let decreasing = if self.eat_kw(Kw::Decreasing) {
            let e = self.expr()?;
            self.end_line()?;
            Some(e)
        } else {
            None
        };
        let body = self.block_rest()?;
        Ok(DeclKind::Fn { partial, name, params, result, constraints, decreasing, body })
    }

    fn enum_decl(&mut self) -> PResult<DeclKind> {
        self.bump(); // enum
        let name = self.ident("an enum name")?;
        let params = self.params()?;
        let constraints = self.opt_constraints()?;
        let mut ctors = Vec::new();
        if self.at(&Tok::Newline) && *self.peek_at(1) == Tok::Indent {
            self.open_block("list of constructors")?;
            while !self.at(&Tok::Dedent) && !self.at(&Tok::Eof) {
                let start = self.span();
                let cname = self.ident("a constructor name")?;
                let cparams = self.names_until_header_end();
                let cs = self.opt_constraints()?;
                let span = start.to(self.prev_span());
                self.end_line()?;
                ctors.push(Ctor { name: cname, params: cparams, constraints: cs, span });
            }
            self.bump(); // dedent
        } else {
            self.end_line()?;
        }
        Ok(DeclKind::Enum { name, params, constraints, ctors })
    }

    fn record_decl(&mut self) -> PResult<DeclKind> {
        self.bump(); // record
        let name = self.ident("a record name")?;
        let params = self.params()?;
        let constraints = self.opt_constraints()?;
        self.open_block("list of fields")?;
        let mut fields = Vec::new();
        while !self.at(&Tok::Dedent) && !self.at(&Tok::Eof) {
            let start = self.span();
            let fname = self.ident("a field name")?;
            self.expect(Tok::Tilde, "`~` and the field's type")?;
            let mult = self.mult();
            let ty = self.expr()?;
            let mut preds = Vec::new();
            while self.eat(&Tok::Comma) {
                preds.push(self.expr()?);
            }
            let span = start.to(self.prev_span());
            self.end_line()?;
            fields.push(Field { name: fname, mult, ty, preds, span });
        }
        self.bump();
        Ok(DeclKind::Record { name, params, constraints, fields })
    }

    fn alias_decl(&mut self) -> PResult<DeclKind> {
        self.bump(); // type
        let name = self.ident("a type name")?;
        let params = self.names_until_header_end();
        self.expect(Tok::Eq, "`=`")?;
        let constraints = self.constraints()?;
        if !matches!(constraints.first(), Some(Constraint::Typed { .. })) {
            let span = self.prev_span();
            self.diags.push(
                Diagnostic::error("E0106", "a type alias must start with a typed binder such as `n~Nat`", span)
                    .with_help("write `type Small = n~Nat, n < 10`"),
            );
        }
        self.end_line()?;
        Ok(DeclKind::Alias { name, params, constraints })
    }

    fn lemma_decl(&mut self) -> PResult<DeclKind> {
        self.bump(); // lemma
        let name = self.ident("a lemma name")?;
        let params = self.names_until_header_end();
        let constraints = self.opt_constraints()?;
        self.open_block("lemma body (`ensures …`)")?;
        let mut lets = Vec::new();
        while self.eat_kw(Kw::Let) {
            let p = self.pattern()?;
            self.expect(Tok::Eq, "`=`")?;
            let e = self.expr()?;
            self.end_line()?;
            lets.push((p, e));
        }
        self.expect_kw(Kw::Ensures)?;
        let ensures = self.expr()?;
        self.end_line()?;
        let proof = if self.eat_kw(Kw::Proof) {
            self.open_block("proof")?;
            Some(self.block_rest()?)
        } else {
            None
        };
        if !self.eat(&Tok::Dedent) {
            return Err(self.error_here("end of lemma"));
        }
        Ok(DeclKind::Lemma { name, params, constraints, lets, ensures, proof })
    }

    fn const_decl(&mut self) -> PResult<DeclKind> {
        self.bump(); // let
        let name = self.ident("a constant name")?;
        self.expect(Tok::Eq, "`=`")?;
        let value = self.expr()?;
        self.end_line()?;
        Ok(DeclKind::Const { name, value })
    }

    // ── blocks and statements ───────────────────────────────────────────────

    /// After an INDENT: statements, then a final expression, then DEDENT.
    fn block_rest(&mut self) -> PResult<Block> {
        let start = self.span();
        let mut stmts = Vec::new();
        loop {
            if self.at(&Tok::Dedent) || self.at(&Tok::Eof) {
                return Err(self.error_here("an expression ending the block"));
            }
            if self.at_kw(Kw::When) {
                let w = self.when_stmt()?;
                let kw = Span::new(w.span.start as usize, w.span.start as usize + 4);
                stmts.push(Stmt::When(w));
                if self.at(&Tok::Dedent) || self.at(&Tok::Eof) {
                    self.diags.push(
                        Diagnostic::error("E0117", "a block cannot end with `when`", kw)
                            .with_label("`when` schedules work and has no value")
                            .with_help("add the block's result on the next line, e.g. `()`"),
                    );
                    return Err(Failed);
                }
                continue;
            }
            if !self.at_kw(Kw::Let) && self.line_has_larrow() {
                let p = self.pattern()?;
                let arrow = self.expect(Tok::LArrow, "`<-`")?.span;
                let e = if self.at_fork_join() {
                    self.fork_join()?
                } else {
                    let e = self.expr()?;
                    self.end_line()?;
                    e
                };
                stmts.push(Stmt::Bind(p, e));
                if self.at(&Tok::Dedent) {
                    self.diags.push(
                        Diagnostic::error("E0114", "a block cannot end with a `<-` binding", arrow)
                            .with_label("this binds a result; the block still needs a final expression")
                            .with_help("add the block's result on the next line; for a comparison with a negative number write `x < -1`"),
                    );
                    return Err(Failed);
                }
                continue;
            }
            if self.eat_kw(Kw::Let) {
                let p = self.pattern()?;
                if self.at(&Tok::LArrow) {
                    let span = self.span();
                    self.diags.push(
                        Diagnostic::error("E0111", "`<-` does not take `let`", span)
                            .with_help("write `x <- f a cap` without `let`"),
                    );
                    return Err(Failed);
                }
                self.expect(Tok::Eq, "`=`")?;
                let e = if self.at(&Tok::Newline) && *self.peek_at(1) == Tok::Indent {
                    self.open_block("expression")?;
                    let b = self.block_rest()?;
                    let span = b.span;
                    Expr { kind: ExprKind::Block(b), span }
                } else {
                    let e = self.expr()?;
                    self.end_line()?;
                    e
                };
                stmts.push(Stmt::Let(p, e));
                continue;
            }
            if self.at_kw(Kw::Have) {
                let hspan = self.bump().span;
                let e = self.expr()?;
                self.end_line()?;
                stmts.push(Stmt::Have(e));
                // A proof block may end with `have`: the goal is then closed by an implicit `auto` (D13).
                if self.at(&Tok::Dedent) {
                    self.bump();
                    let span = start.to(self.prev_span());
                    return Ok(Block { stmts, result: Box::new(Expr { kind: ExprKind::Auto, span: hspan }), span });
                }
                continue;
            }
            let e = self.expr()?;
            self.end_line()?;
            if !self.at(&Tok::Dedent) {
                // A `Unit` statement (D35); the type checker rejects other types.
                stmts.push(Stmt::Expr(e));
                continue;
            }
            self.bump(); // dedent
            let span = start.to(self.prev_span());
            return Ok(Block { stmts, result: Box::new(e), span });
        }
    }

    /// Does the current logical line contain a top-level `<-`?
    fn line_has_larrow(&self) -> bool {
        let mut depth = 0usize;
        for t in &self.toks[self.pos..] {
            match t.tok {
                Tok::LParen | Tok::LBracket | Tok::LBrace => depth += 1,
                Tok::RParen | Tok::RBracket | Tok::RBrace => depth = depth.saturating_sub(1),
                Tok::LArrow if depth == 0 => return true,
                Tok::Newline | Tok::Indent | Tok::Dedent | Tok::Eof => return false,
                _ => {}
            }
        }
        false
    }

    /// `when x = c, … using sched` NL INDENT block DEDENT (D30)
    fn when_stmt(&mut self) -> PResult<When> {
        let start = self.bump().span; // when
        let mut binds = Vec::new();
        loop {
            let name = self.ident("a name for the cown's contents")?;
            self.expect(Tok::Eq, "`=` and a cown")?;
            let cown = self.expr()?;
            binds.push((name, cown));
            if !self.eat(&Tok::Comma) {
                break;
            }
        }
        if !self.at_kw(Kw::Using) {
            let span = self.span();
            self.diags.push(
                Diagnostic::error("E0112", "`when` needs a scheduler capability: `using sched`", span)
                    .with_label("expected `using`")
                    .with_help("scheduling is an effect; pass the `Sched` capability, e.g. `when l = log using sched`"),
            );
            return Err(Failed);
        }
        self.bump();
        let sched = self.ident("the `Sched` capability")?;
        self.open_block("behaviour body")?;
        let body = self.block_rest()?;
        let span = start.to(self.prev_span());
        Ok(When { binds, sched, body, span })
    }

    /// `fork` and `join` are contextual: `fork using …` and `join name = …`.
    /// Elsewhere they are ordinary names (e.g. the list function `join`).
    fn at_fork_join(&self) -> bool {
        match self.peek() {
            Tok::LName(n) if n == "fork" => *self.peek_at(1) == Tok::Kw(Kw::Using),
            Tok::LName(n) if n == "join" => self.at_ident_at(1) && *self.peek_at(2) == Tok::Eq,
            _ => false,
        }
    }

    fn at_ident_at(&self, n: usize) -> bool {
        matches!(self.peek_at(n), Tok::LName(_) | Tok::UName(_))
    }

    /// `fork using sched` / `join x = f, … using sched`, then an indented block (D33).
    fn fork_join(&mut self) -> PResult<Expr> {
        let is_fork = matches!(self.peek(), Tok::LName(n) if n == "fork");
        let start = self.bump().span;
        let what = if is_fork { "fork" } else { "join" };
        let mut binds = Vec::new();
        if !is_fork {
            loop {
                let name = self.ident("a name for the future's value")?;
                self.expect(Tok::Eq, "`=` and a future")?;
                binds.push((name, self.expr()?));
                if !self.eat(&Tok::Comma) {
                    break;
                }
            }
        }
        if !self.at_kw(Kw::Using) {
            let span = self.span();
            self.diags.push(
                Diagnostic::error("E0112", format!("`{what}` needs a scheduler capability: `using sched`"), span)
                    .with_label("expected `using`")
                    .with_help(format!("scheduling is an effect; pass the `Sched` capability, e.g. `f <- {what} … using sched`")),
            );
            return Err(Failed);
        }
        self.bump();
        let sched = self.ident("the `Sched` capability")?;
        self.open_block(&format!("{what} body"))?;
        let body = self.block_rest()?;
        let span = start.to(self.prev_span());
        let kind = if is_fork { ExprKind::Fork(sched, body) } else { ExprKind::Join(binds, sched, body) };
        Ok(Expr { kind, span })
    }

    /// An indented block as an expression.
    fn block_expr(&mut self, what: &str) -> PResult<Expr> {
        self.open_block(what)?;
        let b = self.block_rest()?;
        let span = b.span;
        Ok(Expr { kind: ExprKind::Block(b), span })
    }

    // ── expressions ─────────────────────────────────────────────────────────

    pub fn expr(&mut self) -> PResult<Expr> {
        let start = self.span();
        match self.peek() {
            Tok::Kw(Kw::If) => self.if_expr(),
            Tok::Kw(Kw::Match) => self.match_expr(),
            Tok::Backslash => {
                self.bump();
                let mut pats = vec![self.apat()?];
                while !self.at(&Tok::Arrow) {
                    pats.push(self.apat()?);
                }
                self.bump(); // ->
                let body = if self.at(&Tok::Newline) && *self.peek_at(1) == Tok::Indent {
                    self.block_expr("lambda body")?
                } else {
                    self.expr()?
                };
                let span = start.to(body.span);
                Ok(Expr { kind: ExprKind::Lambda(pats, Box::new(body)), span })
            }
            Tok::Kw(Kw::Try) => {
                self.bump();
                let e = self.expr()?;
                let span = start.to(e.span);
                Ok(Expr { kind: ExprKind::Try(Box::new(e)), span })
            }
            Tok::Kw(Kw::Have) => {
                // `have L args` as an expression (e.g. a match-arm body in a proof): `have` then implicit `auto`.
                self.bump();
                let e = self.expr()?;
                let span = start.to(e.span);
                let block = Block { stmts: vec![Stmt::Have(e)], result: Box::new(Expr { kind: ExprKind::Auto, span: start }), span };
                Ok(Expr { kind: ExprKind::Block(block), span })
            }
            Tok::Kw(Kw::Auto) => {
                self.bump();
                Ok(Expr { kind: ExprKind::Auto, span: start })
            }
            _ if self.at_fork_join() => {
                let what = if matches!(self.peek(), Tok::LName(n) if n == "fork") { "fork" } else { "join" };
                self.diags.push(
                    Diagnostic::error("E0116", format!("`{what}` must be bound to a future"), start)
                        .with_help(format!("write `f <- {what} … using sched` on its own line; use `_ <-` to ignore the future")),
                );
                Err(Failed)
            }
            Tok::Kw(Kw::Admit) => {
                self.bump();
                Ok(Expr { kind: ExprKind::Admit, span: start })
            }
            _ => self.dollar(),
        }
    }

    /// `a $ b`, lowest precedence, right-associative.
    fn dollar(&mut self) -> PResult<Expr> {
        let lhs = self.arrow()?;
        if self.at(&Tok::Op(Op::Dollar)) && !self.op_before_rparen() {
            self.bump();
            let rhs = if self.starts_tail_expr() { self.expr()? } else { self.dollar()? };
            let span = lhs.span.to(rhs.span);
            return Ok(Expr { kind: ExprKind::Binary(Op::Dollar, Box::new(lhs), Box::new(rhs)), span });
        }
        Ok(lhs)
    }

    /// Function type `a -> b`, right-associative, just above `$`.
    fn arrow(&mut self) -> PResult<Expr> {
        let lhs = self.binary(1)?;
        if self.at(&Tok::Arrow) && !self.no_arrow {
            self.bump();
            let rhs = self.arrow()?;
            let span = lhs.span.to(rhs.span);
            return Ok(Expr { kind: ExprKind::Arrow(Box::new(lhs), Box::new(rhs)), span });
        }
        Ok(lhs)
    }

    fn if_expr(&mut self) -> PResult<Expr> {
        let start = self.bump().span; // if
        let cond = self.expr()?;
        if self.eat_kw(Kw::Then) {
            let t = self.expr()?;
            self.expect_kw(Kw::Else)?;
            let e = self.expr()?;
            let span = start.to(e.span);
            return Ok(Expr { kind: ExprKind::If(Box::new(cond), Box::new(t), Box::new(e)), span });
        }
        let t = self.block_expr("`if` branch (or write `then` on the same line)")?;
        if !self.at_kw(Kw::Else) {
            self.diags.push(
                Diagnostic::error("E0108", "a multi-line `if` needs an `else` branch", start.to(cond.span))
                    .with_label("this `if` has no `else`")
                    .with_help("every `if` is an expression and must produce a value on both branches"),
            );
            return Err(Failed);
        }
        self.bump(); // else
        let e = if self.at_kw(Kw::If) { self.if_expr()? } else { self.block_expr("`else` branch")? };
        let span = start.to(e.span);
        Ok(Expr { kind: ExprKind::If(Box::new(cond), Box::new(t), Box::new(e)), span })
    }

    fn match_expr(&mut self) -> PResult<Expr> {
        let start = self.bump().span; // match
        let scrut = self.expr()?;
        self.open_block("list of match arms")?;
        let mut arms = Vec::new();
        while !self.at(&Tok::Dedent) && !self.at(&Tok::Eof) {
            let astart = self.span();
            let pat = self.pattern()?;
            let guard = if self.eat_kw(Kw::If) {
                let saved = std::mem::replace(&mut self.no_arrow, true);
                let g = self.expr();
                self.no_arrow = saved;
                Some(g?)
            } else {
                None
            };
            self.expect(Tok::Arrow, "`->`")?;
            let body = if self.at(&Tok::Newline) && *self.peek_at(1) == Tok::Indent {
                self.block_expr("arm body")?
            } else {
                let e = self.expr()?;
                self.end_line()?;
                e
            };
            let span = astart.to(body.span);
            arms.push(Arm { pat, guard, body, span });
        }
        self.bump(); // dedent
        let span = start.to(self.prev_span());
        Ok(Expr { kind: ExprKind::Match(Box::new(scrut), arms), span })
    }

    fn starts_tail_expr(&self) -> bool {
        matches!(
            self.peek(),
            Tok::Kw(Kw::If) | Tok::Kw(Kw::Match) | Tok::Backslash | Tok::Kw(Kw::Try)
        )
    }

    /// The token after the current one closes a paren: `(x +)` must not
    /// consume `+` as a binary operator.
    fn op_before_rparen(&self) -> bool {
        *self.peek_at(1) == Tok::RParen
    }

    fn binary(&mut self, min_prec: u8) -> PResult<Expr> {
        let mut lhs = self.unary()?;
        while let Tok::Op(op) = *self.peek() {
            if op.prec() < min_prec || self.op_before_rparen() {
                break;
            }
            self.bump();
            let rhs = if self.starts_tail_expr() {
                self.expr()?
            } else {
                let next = match op.assoc() {
                    Assoc::Right => op.prec(),
                    _ => op.prec() + 1,
                };
                self.binary(next)?
            };
            if op.assoc() == Assoc::None {
                if let Tok::Op(o2) = *self.peek() {
                    if o2.assoc() == Assoc::None && !self.op_before_rparen() {
                        let span = self.span();
                        self.diags.push(
                            Diagnostic::error(
                                "E0109",
                                format!("comparison operators cannot be chained (`{}` after `{}`)", o2.as_str(), op.as_str()),
                                span,
                            )
                            .with_help("use `and`, e.g. `a < b and b < c`"),
                        );
                        return Err(Failed);
                    }
                }
            }
            let span = lhs.span.to(rhs.span);
            lhs = Expr { kind: ExprKind::Binary(op, Box::new(lhs), Box::new(rhs)), span };
        }
        Ok(lhs)
    }

    fn unary(&mut self) -> PResult<Expr> {
        if self.at(&Tok::Op(Op::Sub)) {
            let start = self.bump().span;
            let e = self.app()?;
            let span = start.to(e.span);
            return Ok(Expr { kind: ExprKind::Neg(Box::new(e)), span });
        }
        self.app()
    }

    fn starts_atom(&self) -> bool {
        matches!(
            self.peek(),
            Tok::LName(_)
                | Tok::UName(_)
                | Tok::Int(_)
                | Tok::Byte(_)
                | Tok::Char(_)
                | Tok::Str(_)
                | Tok::Bytes(_)
                | Tok::LParen
                | Tok::LBracket
                | Tok::Error
                | Tok::Kw(Kw::Par)
        )
    }

    fn app(&mut self) -> PResult<Expr> {
        let mut f = self.postfix()?;
        while self.starts_atom() {
            let arg = self.postfix()?;
            let span = f.span.to(arg.span);
            f = Expr { kind: ExprKind::App(Box::new(f), Box::new(arg)), span };
        }
        Ok(f)
    }

    fn postfix(&mut self) -> PResult<Expr> {
        let mut e = self.atom()?;
        loop {
            let glued = !self.tok().space_before;
            if glued && self.at(&Tok::Op(Op::Dot)) {
                self.bump();
                let name = self.ident("a field or member name after `.`")?;
                let span = e.span.to(name.span);
                e = Expr { kind: ExprKind::Field(Box::new(e), name), span };
            } else if glued && self.at(&Tok::LBracket) {
                self.bump();
                let i = self.expr()?;
                let end = self.expect(Tok::RBracket, "`]`")?.span;
                let span = e.span.to(end);
                e = Expr { kind: ExprKind::Index(Box::new(e), Box::new(i)), span };
            } else {
                return Ok(e);
            }
        }
    }

    fn atom(&mut self) -> PResult<Expr> {
        let start = self.span();
        let kind = match self.peek().clone() {
            Tok::LName(n) => {
                self.bump();
                if n == "_" {
                    self.diags.push(Diagnostic::error("E0110", "`_` is only allowed in patterns", start));
                }
                ExprKind::Var(n)
            }
            Tok::UName(n) => {
                self.bump();
                ExprKind::Con(n)
            }
            Tok::Int(s) => {
                self.bump();
                ExprKind::Lit(Lit::Int(s))
            }
            Tok::Byte(b) => {
                self.bump();
                ExprKind::Lit(Lit::Byte(b))
            }
            Tok::Char(c) => {
                self.bump();
                ExprKind::Lit(Lit::Char(c))
            }
            Tok::Str(s) => {
                self.bump();
                ExprKind::Lit(Lit::Str(s))
            }
            Tok::Bytes(b) => {
                self.bump();
                ExprKind::Lit(Lit::Bytes(b))
            }
            Tok::Error => {
                self.bump();
                ExprKind::Error
            }
            Tok::Kw(Kw::Par) => {
                self.bump();
                let arg = self.atom()?;
                let span = start.to(arg.span);
                return match arg.kind {
                    ExprKind::Tuple(items) => Ok(Expr { kind: ExprKind::Par(items), span }),
                    _ => {
                        self.diags.push(
                            Diagnostic::error("E0115", "`par` takes a tuple of two or more expressions", arg.span)
                                .with_help("write `par (f x, g y)`; the components are evaluated in parallel"),
                        );
                        Err(Failed)
                    }
                };
            }
            Tok::LParen => return self.paren(),
            Tok::LBracket => {
                self.bump();
                let mut items = Vec::new();
                if !self.at(&Tok::RBracket) {
                    loop {
                        items.push(self.expr()?);
                        if !self.eat(&Tok::Comma) {
                            break;
                        }
                    }
                }
                let end = self.expect(Tok::RBracket, "`,` or `]`")?.span;
                return Ok(Expr { kind: ExprKind::List(items), span: start.to(end) });
            }
            _ => return Err(self.error_here("an expression")),
        };
        Ok(Expr { kind, span: start })
    }

    fn paren(&mut self) -> PResult<Expr> {
        let start = self.bump().span; // (
        if self.at(&Tok::RParen) {
            let end = self.bump().span;
            return Ok(Expr { kind: ExprKind::Unit, span: start.to(end) });
        }
        if let Tok::Op(op) = *self.peek() {
            if *self.peek_at(1) == Tok::RParen {
                self.bump();
                let end = self.bump().span;
                return Ok(Expr { kind: ExprKind::OpRef(op), span: start.to(end) });
            }
            if op != Op::Sub {
                self.bump();
                let e = self.expr()?;
                let end = self.expect(Tok::RParen, "`)`")?.span;
                return Ok(Expr { kind: ExprKind::SectionR(op, Box::new(e)), span: start.to(end) });
            }
        }
        let first = self.expr()?;
        if let Tok::Op(op) = *self.peek() {
            if *self.peek_at(1) == Tok::RParen {
                self.bump();
                let end = self.bump().span;
                return Ok(Expr { kind: ExprKind::SectionL(op, Box::new(first)), span: start.to(end) });
            }
        }
        if self.eat(&Tok::Comma) {
            let mut items = vec![first];
            loop {
                items.push(self.expr()?);
                if !self.eat(&Tok::Comma) {
                    break;
                }
            }
            let end = self.expect(Tok::RParen, "`,` or `)`")?.span;
            return Ok(Expr { kind: ExprKind::Tuple(items), span: start.to(end) });
        }
        let end = self.expect(Tok::RParen, "`)`")?.span;
        Ok(Expr { kind: first.kind, span: start.to(end) })
    }

    // ── patterns ────────────────────────────────────────────────────────────

    fn pattern(&mut self) -> PResult<Pattern> {
        let first = self.cpat()?;
        if !self.at(&Tok::Pipe) {
            return Ok(first);
        }
        let mut alts = vec![first];
        while self.eat(&Tok::Pipe) {
            alts.push(self.cpat()?);
        }
        let span = alts[0].span.to(alts.last().unwrap().span);
        Ok(Pattern { kind: PatKind::Or(alts), span })
    }

    fn starts_apat(&self) -> bool {
        if *self.peek() == Tok::Op(Op::Sub) {
            return matches!(self.peek_at(1), Tok::Int(_));
        }
        matches!(
            self.peek(),
            Tok::LName(_)
                | Tok::UName(_)
                | Tok::Int(_)
                | Tok::Byte(_)
                | Tok::Char(_)
                | Tok::Str(_)
                | Tok::Bytes(_)
                | Tok::LParen
                | Tok::LBracket
                | Tok::Error
        )
    }

    fn cpat(&mut self) -> PResult<Pattern> {
        let head = if let Tok::UName(n) = self.peek().clone() {
            let span = self.bump().span;
            if self.at(&Tok::LBrace) {
                self.bump();
                let mut fields = Vec::new();
                loop {
                    let f = self.ident("a field name")?;
                    let p = if self.eat(&Tok::Eq) {
                        self.pattern()?
                    } else {
                        Pattern { kind: PatKind::Var(f.name.clone()), span: f.span }
                    };
                    fields.push((f, p));
                    if !self.eat(&Tok::Comma) {
                        break;
                    }
                }
                let end = self.expect(Tok::RBrace, "`,` or `}`")?.span;
                return Ok(Pattern { kind: PatKind::Record(Ident { name: n, span }, fields), span: span.to(end) });
            }
            let mut args = Vec::new();
            while self.starts_apat() {
                args.push(self.apat()?);
            }
            let full = args.last().map(|a| span.to(a.span)).unwrap_or(span);
            Pattern { kind: PatKind::Con(Ident { name: n, span }, args), span: full }
        } else {
            self.apat()?
        };
        if self.eat(&Tok::Op(Op::Cons)) {
            let tail = self.cpat()?;
            let span = head.span.to(tail.span);
            return Ok(Pattern { kind: PatKind::Cons(Box::new(head), Box::new(tail)), span });
        }
        Ok(head)
    }

    fn apat(&mut self) -> PResult<Pattern> {
        let start = self.span();
        let kind = match self.peek().clone() {
            Tok::LName(n) => {
                self.bump();
                if n == "_" {
                    PatKind::Wild
                } else {
                    PatKind::Var(n)
                }
            }
            Tok::Error => {
                self.bump();
                PatKind::Wild
            }
            Tok::UName(n) => {
                self.bump();
                PatKind::Con(Ident { name: n, span: start }, Vec::new())
            }
            Tok::Int(s) => {
                self.bump();
                PatKind::Lit(Lit::Int(s))
            }
            Tok::Byte(b) => {
                self.bump();
                PatKind::Lit(Lit::Byte(b))
            }
            Tok::Char(c) => {
                self.bump();
                PatKind::Lit(Lit::Char(c))
            }
            Tok::Str(s) => {
                self.bump();
                PatKind::Lit(Lit::Str(s))
            }
            Tok::Bytes(b) => {
                self.bump();
                PatKind::Lit(Lit::Bytes(b))
            }
            Tok::Op(Op::Sub) => {
                self.bump();
                match self.peek().clone() {
                    Tok::Int(s) => {
                        self.bump();
                        PatKind::Neg(s)
                    }
                    _ => return Err(self.error_here("a number after `-` in a pattern")),
                }
            }
            Tok::LParen => {
                self.bump();
                if self.at(&Tok::RParen) {
                    let end = self.bump().span;
                    return Ok(Pattern { kind: PatKind::Unit, span: start.to(end) });
                }
                let first = self.pattern()?;
                if self.eat(&Tok::Comma) {
                    let mut items = vec![first];
                    loop {
                        items.push(self.pattern()?);
                        if !self.eat(&Tok::Comma) {
                            break;
                        }
                    }
                    let end = self.expect(Tok::RParen, "`,` or `)`")?.span;
                    return Ok(Pattern { kind: PatKind::Tuple(items), span: start.to(end) });
                }
                let end = self.expect(Tok::RParen, "`)`")?.span;
                return Ok(Pattern { kind: first.kind, span: start.to(end) });
            }
            Tok::LBracket => {
                self.bump();
                let mut items = Vec::new();
                if !self.at(&Tok::RBracket) {
                    loop {
                        items.push(self.pattern()?);
                        if !self.eat(&Tok::Comma) {
                            break;
                        }
                    }
                }
                let end = self.expect(Tok::RBracket, "`,` or `]`")?.span;
                return Ok(Pattern { kind: PatKind::List(items), span: start.to(end) });
            }
            _ => return Err(self.error_here("a pattern")),
        };
        Ok(Pattern { kind, span: start })
    }
}
