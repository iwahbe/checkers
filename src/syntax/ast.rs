//! Surface AST (§9.2). Names are not yet resolved; `json.parse` is a
//! `Field` on `Var("json")` until name resolution decides it is qualified.

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
    /// `x~comptime T`: known at compile time (§8.9, D59).
    Comptime,
}

#[derive(Clone, Debug)]
pub enum Constraint {
    /// `x~T`, `x~ghost T`, `x~own T`
    Typed { name: Ident, mult: Mult, ty: Expr },
    /// A Bool/Prop predicate.
    Pred(Expr),
    /// `name: p`, a precondition with a name, which may contain `forall`
    /// (D137); used in the body by `have name a b …`.
    Named(Ident, Expr),
}

/// `(param~dom, preds…)`, or with `arrow`, `(param~dom -> result~cod, preds…)`.
#[derive(Clone, Debug)]
pub struct RefineTy {
    pub param: Option<Ident>,
    pub dom: Expr,
    pub arrow: Option<(Option<Ident>, Expr)>,
    pub preds: Vec<Expr>,
}

impl RefineTy {
    /// The names it binds.
    pub fn binders(&self) -> Vec<String> {
        let mut v: Vec<String> = self.param.iter().map(|p| p.name.clone()).collect();
        if let Some((Some(r), _)) = &self.arrow {
            v.push(r.name.clone());
        }
        v
    }

    /// Its type expressions (the parameter's, then the result's).
    pub fn types(&self) -> Vec<&Expr> {
        let mut v = vec![&self.dom];
        if let Some((_, t)) = &self.arrow {
            v.push(t);
        }
        v
    }
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
    /// `class Ord a` and what each instance must supply (D136).
    Class {
        name: Ident,
        param: Ident,
        members: Vec<ClassMember>,
    },
    /// `instance Ord (List a) : Ord a` (D136).
    Instance {
        class: Ident,
        ty: Expr,
        context: Vec<Expr>,
        members: Vec<InstMember>,
    },
}

/// A requirement of a class: a function's signature, or a lemma's statement.
#[derive(Clone, Debug)]
pub enum ClassMember {
    Fn { name: Ident, params: Vec<Ident>, result: Option<Ident>, constraints: Vec<Constraint>, span: Span },
    Lemma { name: Ident, params: Vec<Ident>, constraints: Vec<Constraint>, lets: Vec<(Pattern, Expr)>, ensures: Expr, span: Span },
}

/// What an instance supplies: a function's body, or a lemma's proof.
#[derive(Clone, Debug)]
pub enum InstMember {
    Fn { name: Ident, params: Vec<Ident>, decreasing: Option<Expr>, body: Block, span: Span },
    Lemma { name: Ident, params: Vec<Ident>, proof: Option<Block>, span: Span },
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
    /// A bare expression line that is not the block's last; must be `Unit` (D35)
    Expr(Expr),
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
    /// A refinement type `(n~Int, n >= 5)` or a refined function type
    /// `(x~Int -> y~Int, x >= 5, y > x)` written inside a type (D82).
    Refine(Box<RefineTy>),
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
    /// `par (e1, …, en)` (D34)
    Par(Vec<Expr>),
    /// `fork using sched` + block; only as the right side of `<-` (D33)
    Fork(Ident, Block),
    /// `join x = f, … using sched` + block; only as the right side of `<-` (D33)
    Join(Vec<(Ident, Expr)>, Ident, Block),
    /// `forall x y : x~a, y~a, p x y` (D137): variables, then clauses that
    /// mention them, the last the conclusion.
    Forall(Vec<Ident>, Vec<Constraint>),
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
