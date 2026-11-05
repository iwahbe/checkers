//! Surface AST (§9.2). Names are not yet resolved; `decimal.scan_json` is a
//! `Field` on `Var("decimal")` until name resolution decides it is qualified.

use super::token::Op;
use crate::source::Span;

#[derive(Clone, Debug)]
pub struct Ident {
    pub name: String,
    pub span: Span,
}

#[derive(Clone, Debug)]
pub struct Module {
    pub name: Option<QName>,
    pub imports: Vec<Import>,
    pub decls: Vec<Decl>,
}

#[derive(Clone, Debug)]
pub struct QName {
    pub parts: Vec<Ident>,
    pub span: Span,
}

impl QName {
    pub fn dotted(&self) -> String {
        self.parts.iter().map(|p| p.name.as_str()).collect::<Vec<_>>().join(".")
    }
}

#[derive(Clone, Debug)]
pub struct Import {
    pub path: QName,
    pub items: Option<Vec<Ident>>,
    pub alias: Option<Ident>,
    pub span: Span,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Export {
    No,
    Yes,
    Abstract,
    Transparent,
}

#[derive(Clone, Debug)]
pub struct Decl {
    pub export: Export,
    pub kind: DeclKind,
    pub span: Span,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Mult {
    Many,
    Ghost,
    Own,
}

#[derive(Clone, Debug)]
pub enum Constraint {
    /// `x~T`, `x~ghost T`, `x~own T`
    Typed { name: Ident, mult: Mult, ty: Expr },
    /// A Bool/Prop predicate.
    Pred(Expr),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Polarity {
    Pos,
    Neg,
}

#[derive(Clone, Debug)]
pub struct Param {
    pub polarity: Option<Polarity>,
    pub name: Ident,
}

#[derive(Clone, Debug)]
pub struct Ctor {
    pub name: Ident,
    pub params: Vec<Ident>,
    pub constraints: Vec<Constraint>,
    pub span: Span,
}

#[derive(Clone, Debug)]
pub struct Field {
    pub name: Ident,
    pub mult: Mult,
    pub ty: Expr,
    pub preds: Vec<Expr>,
    pub span: Span,
}

#[derive(Clone, Debug)]
pub enum DeclKind {
    Fn {
        partial: bool,
        name: Ident,
        params: Vec<Ident>,
        result: Option<Ident>,
        constraints: Vec<Constraint>,
        decreasing: Option<Expr>,
        body: Block,
    },
    Enum {
        name: Ident,
        params: Vec<Param>,
        constraints: Vec<Constraint>,
        ctors: Vec<Ctor>,
    },
    Record {
        name: Ident,
        params: Vec<Param>,
        constraints: Vec<Constraint>,
        fields: Vec<Field>,
    },
    Alias {
        name: Ident,
        params: Vec<Ident>,
        constraints: Vec<Constraint>,
    },
    Lemma {
        name: Ident,
        params: Vec<Ident>,
        constraints: Vec<Constraint>,
        lets: Vec<(Pattern, Expr)>,
        ensures: Expr,
        proof: Option<Block>,
    },
    Const {
        name: Ident,
        value: Expr,
    },
    Check {
        expr: Expr,
    },
}

#[derive(Clone, Debug)]
pub struct Block {
    pub stmts: Vec<Stmt>,
    pub result: Box<Expr>,
    pub span: Span,
}

#[derive(Clone, Debug)]
pub enum Stmt {
    Let(Pattern, Expr),
    Have(Expr),
    /// `pat <- f a c` (D29)
    Bind(Pattern, Expr),
    /// `when x = c, … using sched` + block (D30)
    When(When),
}

#[derive(Clone, Debug)]
pub struct When {
    pub binds: Vec<(Ident, Expr)>,
    pub sched: Ident,
    pub body: Block,
    pub span: Span,
}

#[derive(Clone, Debug)]
pub struct Expr {
    pub kind: ExprKind,
    pub span: Span,
}

#[derive(Clone, Debug)]
pub enum Lit {
    Int(String),
    Byte(u8),
    Char(char),
    Str(String),
    Bytes(Vec<u8>),
}

#[derive(Clone, Debug)]
pub enum ExprKind {
    /// lower-case name
    Var(String),
    /// Upper-case name: constructor, type, or constant (resolved later, D26)
    Con(String),
    Lit(Lit),
    Unit,
    Tuple(Vec<Expr>),
    List(Vec<Expr>),
    App(Box<Expr>, Box<Expr>),
    Binary(Op, Box<Expr>, Box<Expr>),
    /// Function type `a -> b`
    Arrow(Box<Expr>, Box<Expr>),
    Neg(Box<Expr>),
    /// `(+)`
    OpRef(Op),
    /// `(x +)`
    SectionL(Op, Box<Expr>),
    /// `(+ x)`
    SectionR(Op, Box<Expr>),
    /// glued `e.name`
    Field(Box<Expr>, Ident),
    /// glued `e[i]`
    Index(Box<Expr>, Box<Expr>),
    If(Box<Expr>, Box<Expr>, Box<Expr>),
    Match(Box<Expr>, Vec<Arm>),
    Lambda(Vec<Pattern>, Box<Expr>),
    Try(Box<Expr>),
    Block(Block),
    Auto,
    Admit,
    /// Placeholder for a token the lexer rejected.
    Error,
}

#[derive(Clone, Debug)]
pub struct Arm {
    pub pat: Pattern,
    pub guard: Option<Expr>,
    pub body: Expr,
    pub span: Span,
}

#[derive(Clone, Debug)]
pub struct Pattern {
    pub kind: PatKind,
    pub span: Span,
}

#[derive(Clone, Debug)]
pub enum PatKind {
    Wild,
    Var(String),
    Lit(Lit),
    Neg(String),
    Unit,
    Con(Ident, Vec<Pattern>),
    Tuple(Vec<Pattern>),
    List(Vec<Pattern>),
    Cons(Box<Pattern>, Box<Pattern>),
    Or(Vec<Pattern>),
    /// `Ctor { a, b = p }` (D32)
    Record(Ident, Vec<(Ident, Pattern)>),
}
