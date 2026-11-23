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
    /// It has a template (#132): `std.string`, which declares the classes
    /// templates are built through, is loaded for it.
    pub templates: bool,
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
    /// `own` written on the parameter of a refined function type (D172 b).
    pub own: bool,
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
        /// `decreasing e`, the first line of the proof: the induction's
        /// measure (#76).
        decreasing: Option<Expr>,
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
    /// `class Ord a` and what each instance must supply (D136); a class may
    /// take several type parameters (`class Hole s h`, #145).
    Class {
        name: Ident,
        params: Vec<Ident>,
        members: Vec<ClassMember>,
    },
    /// `instance Ord (List a) : Ord a` (D136); a type for each of the
    /// class's parameters (`instance Hole Format a : Display a`, #145).
    Instance {
        class: Ident,
        tys: Vec<Expr>,
        context: Vec<Expr>,
        members: Vec<InstMember>,
    },
}

/// A requirement of a class: a function's signature, or a lemma's statement.
#[derive(Clone, Debug)]
pub enum ClassMember {
    /// `type Name`, or `type Name = T` with a default (#133); either may
    /// be followed by constraints on it (`: Ord Name`, `: u~Name, u < 256`,
    /// #176).
    Type { name: Ident, default: Option<Expr>, constraints: Vec<Constraint>, span: Span },
    Fn { name: Ident, params: Vec<Ident>, result: Option<Ident>, constraints: Vec<Constraint>, span: Span },
    Lemma { name: Ident, params: Vec<Ident>, constraints: Vec<Constraint>, lets: Vec<(Pattern, Expr)>, ensures: Expr, span: Span },
}

/// What an instance supplies: a function's body, or a lemma's proof.
#[derive(Clone, Debug)]
pub enum InstMember {
    /// `type Name = T`: the class's type at this instance (#133).
    Type { name: Ident, ty: Expr, span: Span },
    /// `sig`: a signature of its own, refining the class's (#225): the
    /// result's name and the constraints. `None`: the class's.
    Fn { name: Ident, params: Vec<Ident>, sig: Option<(Option<Ident>, Vec<Constraint>)>, decreasing: Option<Expr>, body: Block, span: Span },
    Lemma { name: Ident, params: Vec<Ident>, decreasing: Option<Expr>, proof: Option<Block>, span: Span },
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
    /// `have x~T`: `x` has type `T` (D170)
    HaveType(Ident, Expr),
    /// A bare expression line that is not the block's last; must be `Unit` (D35)
    Expr(Expr),
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
    /// Schedule a behaviour asynchronously; has type `Unit`.
    When(When),
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
    /// `forall x y : x~a, y~a, p x y` (D137): variables, then clauses that
    /// mention them, the last the conclusion.
    Forall(Vec<Ident>, Vec<Constraint>),
    /// `tag"text {e | o1, o2} text"` (#132): the tag, and the template's
    /// text and holes in order.
    Template(Box<Expr>, Vec<TemplatePiece>),
    /// Placeholder for a token the lexer rejected.
    Error,
}

/// A piece of a template (#132).
#[derive(Clone, Debug)]
pub enum TemplatePiece {
    /// Text, its escapes read, and where it is written.
    Text(String, Span),
    /// `{e | o1, o2}`: the value (None for `{}` and `{| …}`, a new
    /// parameter), the options, and the span of the hole, braces included.
    Hole { value: Option<Expr>, options: Vec<Expr>, span: Span },
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

impl TemplatePiece {
    /// The expressions in it: a hole's value, then its options.
    pub fn exprs(&self) -> impl Iterator<Item = &Expr> {
        let (v, os): (Option<&Expr>, &[Expr]) = match self {
            TemplatePiece::Text(..) => (None, &[]),
            TemplatePiece::Hole { value, options, .. } => (value.as_ref(), options),
        };
        v.into_iter().chain(os.iter())
    }
}

impl ClassMember {
    pub fn name(&self) -> &Ident {
        match self {
            ClassMember::Type { name, .. } | ClassMember::Fn { name, .. } | ClassMember::Lemma { name, .. } => name,
        }
    }

    pub fn span(&self) -> Span {
        match self {
            ClassMember::Type { span, .. } | ClassMember::Fn { span, .. } | ClassMember::Lemma { span, .. } => *span,
        }
    }
}

impl InstMember {
    pub fn name(&self) -> &Ident {
        match self {
            InstMember::Type { name, .. } | InstMember::Fn { name, .. } | InstMember::Lemma { name, .. } => name,
        }
    }
}
