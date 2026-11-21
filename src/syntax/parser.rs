//! Recursive-descent parser for the surface grammar (§9.2).

use super::ast::*;
use super::token::{Assoc, Kw, Op, TemplatePart, Tok, Token};
use crate::diag::Diagnostic;
use crate::source::Span;

pub fn parse(tokens: Vec<Token>) -> (Module, Vec<Diagnostic>) {
    let (m, diags, _) = parse_with_place(tokens);
    (m, diags)
}

/// `parse`, and the kind of place the cursor token (D142) is in, if any.
pub fn parse_with_place(tokens: Vec<Token>) -> (Module, Vec<Diagnostic>, Option<Place>) {
    let mut p = Parser {
        toks: tokens,
        pos: 0,
        diags: Vec::new(),
        last_dedent: false,
        indent: 0,
        no_arrow: false,
        place: None,
        in_proof: 0,
        body_start: false,
        in_type: 0,
        keyword_params: Vec::new(),
    };
    let m = p.module();
    (m, p.diags, p.place)
}

/// The kind of place the cursor is in (D142 c): what can be written there.
#[derive(Clone, Debug, PartialEq)]
pub enum PlaceKind {
    /// The start of a declaration; `first`: none before it (so `import` too).
    Top { first: bool },
    /// After `export`.
    Export,
    /// The start of a statement; `first`: a function body's first (`decreasing`).
    Stmt { first: bool },
    /// After `have`: a lemma.
    Have,
    /// Anywhere else an expression starts.
    Expr,
    /// A signature's clause, or `ensures`.
    Cond,
    /// A type: `start`, directly after `~` (where `ghost`, `own` and
    /// `comptime` go; a record's field: `ghost` only).
    Type { start: bool, field: bool },
    /// After `x.`.
    Member,
    /// A pattern.
    Pattern,
    /// A module path after `import`, with the parts before the cursor.
    Import(Vec<String>),
    /// A name in an import's list: `import std.list (so‸`, the module's path.
    ImportItem(Vec<String>),
    /// A lemma's body before `ensures`.
    LemmaBody,
    /// After a lemma's `ensures` line.
    Proof,
    /// After a multi-line `if`'s branch.
    Else,
    /// A class's or an instance's body.
    Members,
}

#[derive(Clone, Debug, PartialEq)]
pub struct Place {
    pub kind: PlaceKind,
    /// In a `proof` block: `auto`, `admit` and lemmas too.
    pub proof: bool,
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
    /// Where the cursor token is (D142), once the parser has met it.
    place: Option<Place>,
    /// Inside `proof` blocks.
    in_proof: usize,
    /// At a function body's first statement.
    body_start: bool,
    /// Inside a type after `~`.
    in_type: usize,
    /// Keywords a header used as parameter names (reported, E0122): its
    /// constraints may name them without a second report.
    keyword_params: Vec<String>,
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

    /// At the cursor token (D142): note the kind of place, the first time.
    /// Parsing then goes on as for a name.
    fn mark(&mut self, kind: PlaceKind) {
        if self.place.is_none() && matches!(self.peek(), Tok::LName(n) if n == super::lexer::CURSOR) {
            self.place = Some(Place { kind, proof: self.in_proof > 0 });
        }
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
        } else {
            Err(self.error_here("end of line"))
        }
    }

    /// Expect NEWLINE INDENT, opening a block; if it isn't there (a header
    /// being written), report it and skip to the next declaration: false.
    fn open_body(&mut self, what: &str) -> bool {
        if !self.eat(&Tok::Newline) {
            self.error_here(&format!("end of line before {what}"));
            self.recover_top();
            return false;
        }
        if !self.eat(&Tok::Indent) {
            // The next line is the next declaration.
            self.error_here(&format!("an indented {what}"));
            return false;
        }
        true
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
            Tok::Kw(k) => {
                self.keyword_as_name(k, what);
                Err(Failed)
            }
            _ => Err(self.error_here(what)),
        }
    }

    /// E0122: a keyword where a name belongs.
    fn keyword_as_name(&mut self, k: Kw, what: &str) {
        let kw = k.as_str();
        let span = self.span();
        self.diags.push(
            Diagnostic::error("E0122", format!("`{kw}` is a keyword, so it can't be {what}"), span)
                .with_label(format!("expected {what}"))
                .with_help(format!("use another name, such as `{kw}_`")),
        );
    }

    /// A keyword used as a parameter's name: reported, and kept as the
    /// name so the rest of the header still parses.
    fn keyword_param(&mut self) -> Option<Ident> {
        let Tok::Kw(k) = *self.peek() else { return None };
        self.keyword_as_name(k, "a parameter's name");
        let span = self.bump().span;
        self.keyword_params.push(k.as_str().to_string());
        Some(Ident { name: k.as_str().into(), span })
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
            self.mark(PlaceKind::Top { first: decls.is_empty() });
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
        // The path, noting the parts before the cursor (D142).
        self.mark(PlaceKind::Import(Vec::new()));
        let first = self.ident("a module name")?;
        let mut span = first.span;
        let mut parts = vec![first];
        while self.at(&Tok::Op(Op::Dot)) && !self.tok().space_before {
            self.bump();
            self.mark(PlaceKind::Import(parts.iter().map(|p| p.name.clone()).collect()));
            let p = self.ident("a name after `.`")?;
            span = span.to(p.span);
            parts.push(p);
        }
        let path = QName { parts, span };
        let mut items = None;
        if self.eat(&Tok::LParen) {
            let mut v = Vec::new();
            if !self.at(&Tok::RParen) {
                loop {
                    self.mark(PlaceKind::ImportItem(path.parts.iter().map(|p| p.name.clone()).collect()));
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
            self.mark(PlaceKind::Export);
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
            Tok::Kw(Kw::Class) => self.class_decl()?,
            Tok::Kw(Kw::Instance) if export == Export::No => self.instance_decl()?,
            Tok::Kw(Kw::Check) if export == Export::No => {
                self.bump();
                let expr = self.expr()?;
                self.end_line()?;
                DeclKind::Check { expr }
            }
            Tok::Kw(Kw::Instance) => {
                self.diags.push(
                    Diagnostic::error("E0120", "an instance is not exported: it is visible wherever its class and type are", start)
                        .with_help("remove `export`"),
                );
                self.instance_decl()?
            }
            _ => return Err(self.error_here("a declaration (`fn`, `enum`, `record`, `type`, `lemma`, `let`, `class`, `instance`, `check`)")),
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
        loop {
            if self.at_ident() {
                let t = self.bump();
                if let Tok::LName(n) | Tok::UName(n) = t.tok {
                    v.push(Ident { name: n, span: t.span });
                }
            } else if let Some(i) = self.keyword_param() {
                // Nothing else in a header's parameters is a keyword.
                v.push(i);
            } else {
                return v;
            }
        }
    }

    fn params(&mut self) -> PResult<Vec<Param>> {
        let mut v = Vec::new();
        loop {
            let polarity = if self.at(&Tok::Op(Op::Add)) {
                self.bump();
                Some(Polarity::Pos)
            } else if self.at(&Tok::Op(Op::Sub)) || self.at(&Tok::Neg) {
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
        } else if self.eat_kw(Kw::Comptime) {
            Mult::Comptime
        } else {
            Mult::Many
        }
    }

    fn constraint(&mut self) -> PResult<Constraint> {
        self.mark(PlaceKind::Cond);
        // A predicate, even in a refinement inside a type, is not a type.
        let saved = std::mem::replace(&mut self.in_type, 0);
        let c = self.constraint_inner();
        self.in_type = saved;
        c
    }

    fn constraint_inner(&mut self) -> PResult<Constraint> {
        if matches!(self.peek(), Tok::LName(_)) && *self.peek_at(1) == Tok::Colon {
            let name = self.ident("a name")?;
            self.bump(); // :
            return Ok(Constraint::Named(name, self.expr()?));
        }
        let keyword_param = match self.peek() {
            Tok::Kw(k) => *self.peek_at(1) == Tok::Tilde && self.keyword_params.iter().any(|p| p == k.as_str()),
            _ => false,
        };
        if (self.at_ident() || keyword_param) && *self.peek_at(1) == Tok::Tilde {
            let name = if keyword_param {
                let t = self.bump();
                let Tok::Kw(k) = t.tok else { unreachable!() };
                Ident { name: k.as_str().into(), span: t.span }
            } else {
                self.ident("a name")?
            };
            self.bump(); // ~
            self.mark(PlaceKind::Type { start: true, field: false });
            let mult = self.mult();
            self.in_type += 1;
            let ty = self.expr();
            self.in_type -= 1;
            Ok(Constraint::Typed { name, mult, ty: ty? })
        } else {
            Ok(Constraint::Pred(self.expr()?))
        }
    }

    fn fn_decl(&mut self) -> PResult<DeclKind> {
        let partial = self.eat_kw(Kw::Partial);
        self.expect_kw(Kw::Fn)?;
        self.keyword_params.clear();
        let name = self.ident("a function name")?;
        let params = self.names_until_header_end();
        let result_name = if self.eat(&Tok::Arrow) { Some(self.ident("a result name after `->`")?) } else { None };
        let constraints = self.opt_constraints()?;
        let result = result_name.clone();
        // A header without a body yet (being written) is still checked.
        if !self.open_body("function body") {
            let span = self.prev_span();
            let result = Box::new(Expr { kind: ExprKind::Error, span });
            let body = Block { stmts: Vec::new(), result, span };
            return Ok(DeclKind::Fn { partial, name, params, result: result_name, constraints, decreasing: None, body });
        }
        // A body that fails to parse keeps the header (D122): uses of the
        // function still see its signature.
        let start = self.span();
        self.body_start = true;
        let parsed = (|| {
            let decreasing = if self.eat_kw(Kw::Decreasing) {
                let e = self.expr()?;
                self.end_line()?;
                Some(e)
            } else {
                None
            };
            Ok((decreasing, self.block_rest()?))
        })();
        let (decreasing, body) = match parsed {
            Ok(x) => x,
            Err(Failed) => {
                self.recover_top();
                let span = start.to(self.prev_span());
                let result = Box::new(Expr { kind: ExprKind::Error, span });
                (None, Block { stmts: Vec::new(), result, span })
            }
        };
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
            self.mark(PlaceKind::Type { start: true, field: true });
            let mult = self.mult();
            self.in_type += 1;
            let ty = self.expr();
            self.in_type -= 1;
            let ty = ty?;
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

    /// A type, after `type Name =` in a class or an instance.
    fn type_expr(&mut self) -> PResult<Expr> {
        self.mark(PlaceKind::Type { start: false, field: false });
        self.in_type += 1;
        let ty = self.expr();
        self.in_type -= 1;
        ty
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
        if !self.open_body("lemma body (`ensures …`)") {
            // A header being written: checked, with nothing to prove yet.
            let ensures = Expr { kind: ExprKind::Error, span: self.prev_span() };
            return Ok(DeclKind::Lemma { name, params, constraints, decreasing: None, lets: Vec::new(), ensures, proof: None });
        }
        let mut lets = Vec::new();
        self.mark(PlaceKind::LemmaBody);
        while self.eat_kw(Kw::Let) {
            let p = self.pattern()?;
            self.expect(Tok::Eq, "`=`")?;
            let e = self.expr()?;
            self.end_line()?;
            lets.push((p, e));
            self.mark(PlaceKind::LemmaBody);
        }
        self.expect_kw(Kw::Ensures)?;
        self.mark(PlaceKind::Cond);
        let ensures = self.expr()?;
        self.end_line()?;
        self.mark(PlaceKind::Proof);
        let (decreasing, proof) = if self.eat_kw(Kw::Proof) {
            let (d, b) = self.proof_block()?;
            (d, Some(b))
        } else {
            (None, None)
        };
        if !self.eat(&Tok::Dedent) {
            return Err(self.error_here("end of lemma"));
        }
        Ok(DeclKind::Lemma { name, params, constraints, decreasing, lets, ensures, proof })
    }

    /// A lemma's proof, after `proof`: its first line may be `decreasing e`,
    /// the induction's measure (#76), as a function body's may.
    fn proof_block(&mut self) -> PResult<(Option<Expr>, Block)> {
        self.open_block("proof")?;
        self.in_proof += 1;
        self.body_start = true;
        let b = (|| {
            let decreasing = if self.eat_kw(Kw::Decreasing) {
                let e = self.expr()?;
                self.end_line()?;
                Some(e)
            } else {
                None
            };
            Ok((decreasing, self.block_rest()?))
        })();
        self.body_start = false;
        self.in_proof -= 1;
        b
    }

    fn class_decl(&mut self) -> PResult<DeclKind> {
        self.bump(); // class
        let name = self.ident("a class name")?;
        let mut params = vec![self.ident("the class's type parameter")?];
        while matches!(self.tok().tok, Tok::LName(_)) {
            params.push(self.ident("a type parameter")?);
        }
        self.open_block("list of the class's functions and lemmas")?;
        let mut members = Vec::new();
        while !self.at(&Tok::Dedent) && !self.at(&Tok::Eof) {
            let start = self.span();
            self.mark(PlaceKind::Members);
            if self.eat_kw(Kw::Type) {
                let mname = self.ident("a type name")?;
                let params = self.names_until_header_end();
                if let (Some(first), Some(last)) = (params.first(), params.last()) {
                    self.diags.push(
                        Diagnostic::error("E0124", format!("a class's type `{}` takes no parameters", mname.name), first.span.to(last.span))
                            .with_help(format!("write `type {}`; each instance gives it for its own type", mname.name)),
                    );
                    return Err(Failed);
                }
                let default = if self.eat(&Tok::Eq) { Some(self.type_expr()?) } else { None };
                let span = start.to(self.prev_span());
                self.end_line()?;
                members.push(ClassMember::Type { name: mname, default, span });
            } else if self.eat_kw(Kw::Fn) {
                let mname = self.ident("a function name")?;
                let params = self.names_until_header_end();
                let result = if self.eat(&Tok::Arrow) { Some(self.ident("a result name after `->`")?) } else { None };
                let constraints = self.opt_constraints()?;
                let span = start.to(self.prev_span());
                if self.at(&Tok::Newline) && *self.peek_at(1) == Tok::Indent {
                    self.diags.push(
                        Diagnostic::error("E0121", format!("a class's function `{}` has no body", mname.name), mname.span)
                            .with_help("each instance gives the body; a class only gives the signature"),
                    );
                    return Err(Failed);
                }
                self.end_line()?;
                members.push(ClassMember::Fn { name: mname, params, result, constraints, span });
            } else if self.eat_kw(Kw::Lemma) {
                let mname = self.ident("a lemma name")?;
                let params = self.names_until_header_end();
                let constraints = self.opt_constraints()?;
                self.open_block("lemma statement (`ensures …`)")?;
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
                if self.at_kw(Kw::Proof) {
                    self.diags.push(
                        Diagnostic::error("E0121", format!("a class's lemma `{}` has no proof", mname.name), self.span())
                            .with_help("each instance proves it; to prove something once from the class's lemmas, write a lemma outside the class"),
                    );
                    return Err(Failed);
                }
                if !self.eat(&Tok::Dedent) {
                    return Err(self.error_here("end of lemma"));
                }
                let span = start.to(self.prev_span());
                members.push(ClassMember::Lemma { name: mname, params, constraints, lets, ensures, span });
            } else {
                return Err(self.error_here("`type`, `fn` or `lemma`"));
            }
        }
        self.bump(); // dedent
        Ok(DeclKind::Class { name, params, members })
    }

    fn instance_decl(&mut self) -> PResult<DeclKind> {
        self.bump(); // instance
        let class = self.ident("a class name")?;
        let mut tys = vec![self.postfix()?];
        while !self.at(&Tok::Colon) && !self.at(&Tok::Newline) && !self.at(&Tok::Eof) {
            tys.push(self.postfix()?);
        }
        let mut context = Vec::new();
        if self.eat(&Tok::Colon) {
            context.push(self.expr()?);
            while self.eat(&Tok::Comma) {
                context.push(self.expr()?);
            }
        }
        let mut members = Vec::new();
        if !(self.at(&Tok::Newline) && *self.peek_at(1) == Tok::Indent) {
            self.end_line()?;
            return Ok(DeclKind::Instance { class, tys, context, members });
        }
        self.open_block("list of the instance's functions and lemmas")?;
        while !self.at(&Tok::Dedent) && !self.at(&Tok::Eof) {
            let start = self.span();
            self.mark(PlaceKind::Members);
            if self.eat_kw(Kw::Type) {
                let mname = self.ident("a type name")?;
                let params = self.names_until_header_end();
                if let (Some(first), Some(last)) = (params.first(), params.last()) {
                    self.diags.push(
                        Diagnostic::error("E0124", format!("a class's type `{}` takes no parameters", mname.name), first.span.to(last.span))
                            .with_help(format!("write `type {} = …` with the type for this instance", mname.name)),
                    );
                    return Err(Failed);
                }
                self.expect(Tok::Eq, "`=` and the type")?;
                let ty = self.type_expr()?;
                let span = start.to(self.prev_span());
                self.end_line()?;
                members.push(InstMember::Type { name: mname, ty, span });
            } else if self.eat_kw(Kw::Fn) {
                let mname = self.ident("a function name")?;
                let params = self.names_until_header_end();
                if self.at(&Tok::Colon) || self.at(&Tok::Arrow) {
                    self.diags.push(
                        Diagnostic::error("E0121", format!("an instance's function `{}` takes its signature from the class", mname.name), self.span())
                            .with_help("write only its name and parameters, then its body"),
                    );
                    return Err(Failed);
                }
                self.open_block("function body")?;
                self.body_start = true;
                let decreasing = if self.eat_kw(Kw::Decreasing) {
                    let e = self.expr()?;
                    self.end_line()?;
                    Some(e)
                } else {
                    None
                };
                let body = self.block_rest()?;
                let span = start.to(self.prev_span());
                members.push(InstMember::Fn { name: mname, params, decreasing, body, span });
            } else if self.eat_kw(Kw::Lemma) {
                let mname = self.ident("a lemma name")?;
                let params = self.names_until_header_end();
                if self.at(&Tok::Colon) {
                    self.diags.push(
                        Diagnostic::error("E0121", format!("an instance's lemma `{}` takes its statement from the class", mname.name), self.span())
                            .with_help("write only its name and parameters, then its proof"),
                    );
                    return Err(Failed);
                }
                let (decreasing, proof) = if self.at(&Tok::Newline) && *self.peek_at(1) == Tok::Indent {
                    self.open_block("proof")?;
                    self.mark(PlaceKind::Proof);
                    self.expect_kw(Kw::Proof)?;
                    let (d, b) = self.proof_block()?;
                    if !self.eat(&Tok::Dedent) {
                        return Err(self.error_here("end of lemma"));
                    }
                    (d, Some(b))
                } else {
                    self.end_line()?;
                    (None, None)
                };
                let span = start.to(self.prev_span());
                members.push(InstMember::Lemma { name: mname, params, decreasing, proof, span });
            } else {
                return Err(self.error_here("`type`, `fn` or `lemma`"));
            }
        }
        self.bump(); // dedent
        Ok(DeclKind::Instance { class, tys, context, members })
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

    /// The rest of a block, after its INDENT. A statement that fails to
    /// parse becomes a hole (`ExprKind::Error`, bound if it was a `let`) and
    /// parsing goes on at the block's next statement (D142 e): the rest of
    /// the body is still checked.
    fn block_rest(&mut self) -> PResult<Block> {
        let start = self.span();
        let level = self.indent;
        let mut stmts = Vec::new();
        loop {
            let (had_place, before) = (self.place.is_some(), stmts.len());
            match self.block_step(&mut stmts, start) {
                Ok(Some(b)) => return Ok(b),
                Ok(None) => {}
                Err(Failed) => {
                    let at = self.span();
                    let hole = Span { start: at.start, end: at.start };
                    // The cursor (D142) was in the statement that failed: the
                    // hole is the cursor's name, so the checker still sees
                    // what is in scope there.
                    let mut cursor = (!had_place && self.place.is_some())
                        .then(|| Expr { kind: ExprKind::Var(super::lexer::CURSOR.to_string()), span: hole });
                    if stmts.len() > before {
                        if let (Some(c), Some(Stmt::Let(_, rhs))) = (&cursor, stmts.last_mut()) {
                            *rhs = c.clone();
                            cursor = None;
                        }
                    }
                    self.recover_stmt(level);
                    if self.at(&Tok::Eof) || (self.at(&Tok::Dedent) && self.indent == level) || self.indent < level {
                        if self.at(&Tok::Dedent) && self.indent == level {
                            self.bump();
                        }
                        self.last_dedent = true;
                        let span = start.to(self.prev_span());
                        let result = Box::new(cursor.unwrap_or(Expr { kind: ExprKind::Error, span: hole }));
                        return Ok(Block { stmts, result, span });
                    }
                    if let Some(c) = cursor {
                        stmts.push(Stmt::Expr(c));
                    }
                }
            }
        }
    }

    /// Skip to the start of the next statement of the block at `level`, or
    /// to the DEDENT that ends it.
    fn recover_stmt(&mut self, level: usize) {
        loop {
            if self.at(&Tok::Eof) || self.indent < level {
                return;
            }
            if self.indent == level && self.at(&Tok::Dedent) {
                return;
            }
            let t = self.bump();
            // The failed statement's own indented block goes with it.
            if t.tok == Tok::Newline && self.indent == level && !self.at(&Tok::Indent) {
                return;
            }
            if t.tok == Tok::Dedent && self.indent == level {
                return;
            }
        }
    }

    /// One statement of a block, or its last expression (the block, done).
    fn block_step(&mut self, stmts: &mut Vec<Stmt>, start: Span) -> PResult<Option<Block>> {
        {
            let first = std::mem::replace(&mut self.body_start, false);
            self.mark(PlaceKind::Stmt { first });
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
                return Ok(None);
            }
            if self.eat_kw(Kw::Let) {
                let p = self.pattern()?;
                self.expect(Tok::Eq, "`=`")?;
                let at = self.span();
                let parsed = (|| {
                    if self.at(&Tok::Newline) && *self.peek_at(1) == Tok::Indent {
                        self.open_block("expression")?;
                        let b = self.block_rest()?;
                        let span = b.span;
                        Ok(Expr { kind: ExprKind::Block(b), span })
                    } else {
                        let e = self.expr()?;
                        self.end_line()?;
                        Ok(e)
                    }
                })();
                let e = match parsed {
                    Ok(e) => e,
                    Err(Failed) => {
                        // Still bound, to a hole, for what follows.
                        stmts.push(Stmt::Let(p, Expr { kind: ExprKind::Error, span: Span { start: at.start, end: at.start } }));
                        return Err(Failed);
                    }
                };
                stmts.push(Stmt::Let(p, e));
                return Ok(None);
            }
            if self.at_kw(Kw::Have) {
                let hspan = self.bump().span;
                self.mark(PlaceKind::Have);
                if self.at_ident() && *self.peek_at(1) == Tok::Tilde {
                    // `have x~T` (D170).
                    let name = self.ident("a name")?;
                    self.bump(); // ~
                    self.mark(PlaceKind::Type { start: true, field: false });
                    self.in_type += 1;
                    let ty = self.expr();
                    self.in_type -= 1;
                    let ty = ty?;
                    self.end_line()?;
                    stmts.push(Stmt::HaveType(name, ty));
                    return Ok(None);
                }
                let e = self.expr()?;
                self.end_line()?;
                stmts.push(Stmt::Have(e));
                // A proof block may end with `have`: the goal is then closed by an implicit `auto` (D13).
                if self.at(&Tok::Dedent) {
                    self.bump();
                    let span = start.to(self.prev_span());
                    return Ok(Some(Block { stmts: std::mem::take(stmts), result: Box::new(Expr { kind: ExprKind::Auto, span: hspan }), span }));
                }
                return Ok(None);
            }
            let e = self.expr()?;
            self.end_line()?;
            if !self.at(&Tok::Dedent) {
                // A `Unit` statement (D35); the type checker rejects other types.
                stmts.push(Stmt::Expr(e));
                return Ok(None);
            }
            self.bump(); // dedent
            let span = start.to(self.prev_span());
            Ok(Some(Block { stmts: std::mem::take(stmts), result: Box::new(e), span }))
        }
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
                self.mark(PlaceKind::Have);
                let e = self.expr()?;
                let span = start.to(e.span);
                let block = Block { stmts: vec![Stmt::Have(e)], result: Box::new(Expr { kind: ExprKind::Auto, span: start }), span };
                Ok(Expr { kind: ExprKind::Block(block), span })
            }
            Tok::Kw(Kw::Auto) => {
                self.bump();
                Ok(Expr { kind: ExprKind::Auto, span: start })
            }
            Tok::Kw(Kw::Admit) => {
                self.bump();
                Ok(Expr { kind: ExprKind::Admit, span: start })
            }
            Tok::Kw(Kw::Forall) => self.forall(),
            _ => self.dollar(),
        }
    }

    /// `forall x y : c, …` (D137): its clauses are those that follow and
    /// mention one of its variables (parenthesize to end it sooner).
    fn forall(&mut self) -> PResult<Expr> {
        let start = self.bump().span; // forall
        let mut vars = Vec::new();
        while matches!(self.peek(), Tok::LName(_)) {
            vars.push(self.ident("a variable")?);
        }
        if vars.is_empty() {
            return Err(self.error_here("the variables of `forall`"));
        }
        self.expect(Tok::Colon, "`:` and the clauses of `forall`")?;
        let names: Vec<String> = vars.iter().map(|v| v.name.clone()).collect();
        let mut clauses = vec![self.constraint()?];
        loop {
            if !self.at(&Tok::Comma) {
                break;
            }
            let (pos, ndiags, indent, last) = (self.pos, self.diags.len(), self.indent, self.last_dedent);
            self.bump(); // ,
            let c = match self.constraint() {
                Ok(c) => c,
                Err(Failed) => {
                    (self.pos, self.indent, self.last_dedent) = (pos, indent, last);
                    self.diags.truncate(ndiags);
                    break;
                }
            };
            if constraint_mentions(&c, &names) {
                clauses.push(c);
            } else {
                (self.pos, self.indent, self.last_dedent) = (pos, indent, last);
                self.diags.truncate(ndiags);
                break;
            }
        }
        let end = self.prev_span();
        Ok(Expr { kind: ExprKind::Forall(vars, clauses), span: start.to(end) })
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
        self.mark(PlaceKind::Else);
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
            self.mark(PlaceKind::Pattern);
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
            Tok::Kw(Kw::If) | Tok::Kw(Kw::Match) | Tok::Backslash | Tok::Kw(Kw::Try) | Tok::Kw(Kw::Forall)
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
        if self.at(&Tok::Op(Op::Sub)) || self.at(&Tok::Neg) {
            let start = self.bump().span;
            let e = self.app()?;
            let span = start.to(e.span);
            return Ok(Expr { kind: ExprKind::Neg(Box::new(e)), span });
        }
        self.app()
    }

    fn starts_atom(&self) -> bool {
        self.starts_simple() || matches!(self.peek(), Tok::Kw(Kw::Par) | Tok::Neg)
    }

    /// At a token that starts both an atom and an atomic pattern.
    fn starts_simple(&self) -> bool {
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

    /// `item`s separated by commas, at least one, added to `items`.
    fn commas<T>(&mut self, items: &mut Vec<T>, mut item: impl FnMut(&mut Self) -> PResult<T>) -> PResult<()> {
        loop {
            items.push(item(self)?);
            if !self.eat(&Tok::Comma) {
                return Ok(());
            }
        }
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
        // A sign glued to an argument negates it: `f -x` is `f (-x)` (D169).
        if self.at(&Tok::Neg) {
            let start = self.bump().span;
            let e = self.postfix()?;
            let span = start.to(e.span);
            return Ok(Expr { kind: ExprKind::Neg(Box::new(e)), span });
        }
        let mut e = self.atom()?;
        loop {
            let glued = !self.tok().space_before;
            if glued && self.at(&Tok::Op(Op::Dot)) {
                self.bump();
                self.mark(PlaceKind::Member);
                let name = self.ident("a field or member name after `.`")?;
                let span = e.span.to(name.span);
                e = Expr { kind: ExprKind::Field(Box::new(e), name), span };
            } else if glued && matches!(self.peek(), Tok::Template(_)) {
                // A template: the string is glued to its tag (#132).
                let t = self.bump();
                let Tok::Template(parts) = t.tok else { unreachable!() };
                let pieces = parts.into_iter().map(|p| self.template_piece(p)).collect();
                let span = e.span.to(t.span);
                e = Expr { kind: ExprKind::Template(Box::new(e), pieces), span };
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

    /// A template's piece (#132); a hole's tokens are parsed by a parser of
    /// their own, so an error inside one stays inside it.
    fn template_piece(&mut self, part: TemplatePart) -> TemplatePiece {
        let (toks, span) = match part {
            TemplatePart::Text(s, sp) => return TemplatePiece::Text(s, sp),
            TemplatePart::Hole(toks, span) => (toks, span),
        };
        // `|` splits the hole at bracket depth 0.
        let mut depth = 0usize;
        let mut split = None;
        for (i, t) in toks.iter().enumerate() {
            match t.tok {
                Tok::LParen | Tok::LBracket | Tok::LBrace => depth += 1,
                Tok::RParen | Tok::RBracket | Tok::RBrace => depth = depth.saturating_sub(1),
                Tok::Pipe if depth == 0 => {
                    split = Some(i);
                    break;
                }
                _ => {}
            }
        }
        // Each part is parsed up to the token after it: the `|`, or the
        // hole's `}`.
        let close = Token { tok: Tok::RBrace, span: Span { start: span.end - 1, end: span.end }, space_before: false };
        let (value_toks, value_end, option_toks) = match split {
            Some(i) => (toks[..i].to_vec(), toks[i].clone(), Some(toks[i + 1..].to_vec())),
            None => (toks, close.clone(), None),
        };
        let value = if value_toks.is_empty() {
            None
        } else {
            self.sub_parse(value_toks, value_end, "`|` or `}`", |p| p.expr())
        };
        let options = match option_toks {
            None => Vec::new(),
            Some(ts) => self
                .sub_parse(ts, close, "`,` or `}`", |p| {
                    let mut items = Vec::new();
                    p.commas(&mut items, Self::expr)?;
                    Ok(items)
                })
                .unwrap_or_default(),
        };
        TemplatePiece::Hole { value, options, span }
    }

    /// Parse `toks` (part of a hole) with `f`, which must use all of them,
    /// stopping at `end`, the token after them.
    fn sub_parse<T>(&mut self, mut toks: Vec<Token>, end: Token, what: &str, f: impl FnOnce(&mut Self) -> PResult<T>) -> Option<T> {
        let last = toks.len();
        toks.push(end);
        let mut p = Parser {
            toks,
            pos: 0,
            diags: Vec::new(),
            last_dedent: false,
            indent: 0,
            no_arrow: false,
            place: None,
            in_proof: self.in_proof,
            body_start: false,
            in_type: 0,
            keyword_params: Vec::new(),
        };
        let r = f(&mut p).ok().filter(|_| {
            if p.pos == last {
                true
            } else {
                // `:` is no part of any expression, so it ends up here.
                p.error_here(what);
                false
            }
        });
        self.diags.append(&mut p.diags);
        if self.place.is_none() {
            self.place = p.place;
        }
        r
    }

    fn atom(&mut self) -> PResult<Expr> {
        let start = self.span();
        self.mark(if self.in_type > 0 { PlaceKind::Type { start: false, field: false } } else { PlaceKind::Expr });
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
                    self.commas(&mut items, Self::expr)?;
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
        // `(x~T, …)` or `(x~A -> …)`: a refinement written in a type (D82).
        if self.at_ident() && *self.peek_at(1) == Tok::Tilde {
            let param = self.ident("a name")?;
            self.bump(); // ~
            let mult_span = self.span();
            let mult = self.mult();
            let saved = std::mem::replace(&mut self.no_arrow, true);
            let dom = self.expr();
            self.no_arrow = saved;
            let dom = dom?;
            let arrow = if self.eat(&Tok::Arrow) { Some(self.refine_result()?) } else { None };
            // Only a function's parameter may be `own` (D172 b).
            if mult != Mult::Many && !(mult == Mult::Own && arrow.is_some()) {
                self.refine_mult_error(mult, mult_span, arrow.is_some());
            }
            let mut e = self.refine_rest(start, Some(param), dom, arrow)?;
            if let ExprKind::Refine(r) = &mut e.kind {
                r.own = mult == Mult::Own;
            }
            return Ok(e);
        }
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
        // `(A -> y~B, …)`: a refined function type with an unnamed parameter.
        if self.at(&Tok::Tilde) {
            if let ExprKind::Arrow(dom, res) = &first.kind {
                if let ExprKind::Var(y) = &res.kind {
                    let name = Ident { name: y.clone(), span: res.span };
                    self.bump(); // ~
                    let mult_span = self.span();
                    let mult = self.mult();
                    if mult != Mult::Many {
                        self.refine_mult_error(mult, mult_span, false);
                    }
                    let cod = self.expr()?;
                    return self.refine_rest(start, None, (**dom).clone(), Some((Some(name), cod)));
                }
            }
        }
        if let Tok::Op(op) = *self.peek() {
            if *self.peek_at(1) == Tok::RParen {
                self.bump();
                let end = self.bump().span;
                return Ok(Expr { kind: ExprKind::SectionL(op, Box::new(first)), span: start.to(end) });
            }
        }
        if self.eat(&Tok::Comma) {
            let mut items = vec![first];
            self.commas(&mut items, Self::expr)?;
            let end = self.expect(Tok::RParen, "`,` or `)`")?.span;
            return Ok(Expr { kind: ExprKind::Tuple(items), span: start.to(end) });
        }
        let end = self.expect(Tok::RParen, "`)`")?.span;
        Ok(Expr { kind: first.kind, span: start.to(end) })
    }

    /// After `->` in a refined function type: `y~B` or `B`.
    fn refine_result(&mut self) -> PResult<(Option<Ident>, Expr)> {
        if self.at_ident() && *self.peek_at(1) == Tok::Tilde {
            let name = self.ident("a name")?;
            self.bump(); // ~
            let mult_span = self.span();
            let mult = self.mult();
            if mult != Mult::Many {
                self.refine_mult_error(mult, mult_span, false);
            }
            Ok((Some(name), self.expr()?))
        } else {
            Ok((None, self.expr()?))
        }
    }

    /// E0123: `ghost`, `own` or `comptime` where a type can't carry it: on
    /// a refinement, a function type's result, or (`ghost`, `comptime`) its
    /// parameter. They were ignored before (D172 b).
    fn refine_mult_error(&mut self, mult: Mult, span: Span, is_param: bool) {
        let word = match mult {
            Mult::Ghost => "ghost",
            Mult::Own => "own",
            Mult::Comptime => "comptime",
            Mult::Many => return,
        };
        let d = Diagnostic::error("E0123", format!("`{word}` can't be written here, inside a type"), span);
        let d = if is_param {
            d.with_help(format!("only `own` may be written on a function type's parameter; give `{word}` to the variable instead"))
        } else {
            d.with_help(format!("write `{word}` on a parameter of a function (`x~{word} T`), or on a function type's parameter (`own` only)"))
        };
        self.diags.push(d);
    }

    /// The predicates and `)` of a refinement type.
    fn refine_rest(&mut self, start: Span, param: Option<Ident>, dom: Expr, arrow: Option<(Option<Ident>, Expr)>) -> PResult<Expr> {
        let mut preds = Vec::new();
        while self.eat(&Tok::Comma) {
            preds.push(self.expr()?);
        }
        let end = self.expect(Tok::RParen, "`,` or `)`")?.span;
        Ok(Expr { kind: ExprKind::Refine(Box::new(RefineTy { param, own: false, dom, arrow, preds })), span: start.to(end) })
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
        if matches!(self.peek(), Tok::Op(Op::Sub) | Tok::Neg) {
            return matches!(self.peek_at(1), Tok::Int(_));
        }
        self.starts_simple()
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
        self.mark(PlaceKind::Pattern);
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
            Tok::Op(Op::Sub) | Tok::Neg => {
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
                    self.commas(&mut items, Self::pattern)?;
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
                    self.commas(&mut items, Self::pattern)?;
                }
                let end = self.expect(Tok::RBracket, "`,` or `]`")?.span;
                return Ok(Pattern { kind: PatKind::List(items), span: start.to(end) });
            }
            _ => return Err(self.error_here("a pattern")),
        };
        Ok(Pattern { kind, span: start })
    }
}

/// Does the constraint mention one of `names` (as a variable, or as the name
/// a typed binder gives a type to)?
fn constraint_mentions(c: &Constraint, names: &[String]) -> bool {
    match c {
        Constraint::Typed { name, ty, .. } => names.contains(&name.name) || expr_mentions(ty, names),
        Constraint::Pred(e) | Constraint::Named(_, e) => expr_mentions(e, names),
    }
}

fn expr_mentions(e: &Expr, names: &[String]) -> bool {
    let go = |x: &Expr| expr_mentions(x, names);
    match &e.kind {
        ExprKind::Var(n) => names.contains(n),
        ExprKind::Tuple(xs) | ExprKind::List(xs) | ExprKind::Par(xs) => xs.iter().any(go),
        ExprKind::App(a, b) | ExprKind::Binary(_, a, b) | ExprKind::Arrow(a, b) | ExprKind::Index(a, b) => go(a) || go(b),
        ExprKind::Neg(a) | ExprKind::SectionL(_, a) | ExprKind::SectionR(_, a) | ExprKind::Field(a, _) | ExprKind::Try(a) => go(a),
        ExprKind::If(a, b, c) => go(a) || go(b) || go(c),
        ExprKind::Match(a, arms) => go(a) || arms.iter().any(|arm| go(&arm.body) || arm.guard.as_ref().is_some_and(go)),
        ExprKind::Lambda(_, b) => go(b),
        ExprKind::Template(t, ps) => go(t) || ps.iter().any(|p| p.exprs().any(go)),
        ExprKind::Refine(r) => r.types().into_iter().any(go) || r.preds.iter().any(go),
        ExprKind::Forall(_, cs) => cs.iter().any(|c| constraint_mentions(c, names)),
        ExprKind::Block(b) => go(&b.result),
        _ => false,
    }
}
