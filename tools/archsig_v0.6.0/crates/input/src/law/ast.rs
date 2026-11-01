//! Law の構文木。式は arena に置き、`ExprId` で参照する。

pub type Span = (usize, usize);
pub type ExprId = usize;

/// 綴りと出現位置。`tok` は字句列での位置。
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Ident {
    pub name: String,
    pub span: Span,
    pub tok: usize,
}

/// `.` 区切りの名前の出現。
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct QName {
    pub parts: Vec<Ident>,
}

impl QName {
    pub fn span(&self) -> Span {
        (
            self.parts[0].span.0,
            self.parts[self.parts.len() - 1].span.1,
        )
    }

    pub fn text(&self) -> String {
        self.parts
            .iter()
            .map(|p| p.name.as_str())
            .collect::<Vec<_>>()
            .join(".")
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Builtin {
    Unit,
    Bool,
    Z,
    Q,
    Text,
}

#[derive(Debug, Eq)]
pub enum TypeAst {
    Builtin(Builtin, Span),
    Fp {
        modulus: String,
        span: Span,
    },
    Named {
        name: QName,
        index: Option<Ident>,
        span: Span,
    },
    Tuple(Vec<TypeAst>, Span),
    List(Box<TypeAst>, Span),
    Set(Box<TypeAst>, Span),
    Option(Box<TypeAst>, Span),
    Map(Box<TypeAst>, Box<TypeAst>, Span),
    Term(Vec<TypeAst>, Box<TypeAst>, Span),
    Path(QName, QName, Span),
}

impl TypeAst {
    pub fn span(&self) -> Span {
        match self {
            TypeAst::Builtin(_, s)
            | TypeAst::Fp { span: s, .. }
            | TypeAst::Named { span: s, .. }
            | TypeAst::Tuple(_, s)
            | TypeAst::List(_, s)
            | TypeAst::Set(_, s)
            | TypeAst::Option(_, s)
            | TypeAst::Map(_, _, s)
            | TypeAst::Term(_, _, s)
            | TypeAst::Path(_, _, s) => *s,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Field {
    pub name: Ident,
    pub ty: TypeAst,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum BinOp {
    Implies,
    Or,
    And,
    Eq,
    Ne,
    Lt,
    Le,
    Gt,
    Ge,
    In,
    Add,
    Sub,
    Mul,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum UnOp {
    Not,
    Neg,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum QuantKind {
    Forall,
    Exists,
}

#[derive(Debug, Eq)]
pub enum Pattern {
    Wild(Span),
    /// 引数のない名前。期待 data 型の constructor か、新しい束縛。
    Name(Ident),
    /// 修飾名、または引数を持つ constructor。
    Ctor {
        name: QName,
        args: Vec<Pattern>,
        span: Span,
    },
}

impl Pattern {
    pub fn span(&self) -> Span {
        match self {
            Pattern::Wild(s) | Pattern::Ctor { span: s, .. } => *s,
            Pattern::Name(i) => i.span,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Arm {
    pub pattern: Pattern,
    pub body: ExprId,
}

/// 構文解析の文脈。`no_in` は let 右辺の最上位で `in` を二項演算として読まない。
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Hash)]
pub struct Flags {
    pub no_in: bool,
}

/// 量化の域と本体の区切り(§4 の `.`)の読み。
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum QuantSplit {
    /// 区切りが決まった。
    Fixed { domain: QuantDomain, body: ExprId },
    /// 最上位の `.` のうち、域(型)と本体がどちらも読める区切りの候補。
    /// 核が、域が List/Set になる(型名になる)ただ一つの候補を選ぶ。
    Candidates(Vec<(QuantDomain, ExprId)>),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum QuantDomain {
    In(ExprId),
    Type(TypeAst),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ExprKind {
    Let {
        name: Ident,
        value: ExprId,
        body: ExprId,
    },
    If {
        cond: ExprId,
        then_branch: ExprId,
        else_branch: ExprId,
    },
    Match {
        scrutinee: ExprId,
        arms: Vec<Arm>,
    },
    Quant {
        kind: QuantKind,
        var: Ident,
        split: QuantSplit,
    },
    Binary {
        op: BinOp,
        lhs: ExprId,
        rhs: ExprId,
    },
    Unary {
        op: UnOp,
        operand: ExprId,
    },
    /// 先頭が名前の `.` 列。束縛変数・宣言名・射影の別は核が解決する。
    Dotted(Vec<Ident>),
    Field {
        base: ExprId,
        name: Ident,
    },
    Index {
        base: ExprId,
        index: usize,
        index_span: Span,
        dot_tok: usize,
    },
    Call {
        callee: ExprId,
        args: Vec<ExprId>,
    },
    With {
        base: ExprId,
        updates: Vec<(Ident, ExprId)>,
    },
    /// 合成演算の適用位置にある予約語 `then`。
    ThenOp,
    Int(String),
    Str(String),
    Bool(bool),
    Unit,
    Group(ExprId),
    Tuple(Vec<ExprId>),
    ListLit {
        ty: TypeAst,
        items: Vec<ExprId>,
    },
    SetLit {
        ty: TypeAst,
        items: Vec<ExprId>,
    },
    SetComp {
        elem: ExprId,
        var: Ident,
        domain: ExprId,
        filter: Option<ExprId>,
    },
    None(TypeAst),
    Some(ExprId),
    Fn {
        params: Vec<Field>,
        body: ExprId,
    },
    Family {
        name: QName,
        owner: ExprId,
    },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Expr {
    pub kind: ExprKind,
    pub span: Span,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Role {
    Required,
    Optional,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Constructor {
    pub name: Ident,
    pub args: Vec<TypeAst>,
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Alignment {
    pub source: QName,
    pub target: QName,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum DeclKind {
    Entity {
        params: Vec<Field>,
        members: Vec<Field>,
    },
    Arrow {
        params: Vec<Field>,
        members: Vec<Field>,
    },
    Correspondence {
        params: Vec<Field>,
        members: Vec<Field>,
        alignments: Vec<Alignment>,
    },
    Data {
        constructors: Vec<Constructor>,
    },
    View {
        params: Vec<Field>,
        returns: TypeAst,
        body: ExprId,
    },
    Law {
        role: Role,
        params: Vec<Field>,
        guard: Option<ExprId>,
        body: ExprId,
    },
    Local {
        params: Vec<Field>,
        guard: Option<ExprId>,
        reads: Vec<ExprId>,
    },
    Change {
        params: Vec<Field>,
        guard: Option<ExprId>,
        body: ExprId,
    },
    Relation {
        params: Vec<Field>,
        guard: Option<ExprId>,
        body: ExprId,
    },
}

impl DeclKind {
    pub fn name(&self) -> &'static str {
        match self {
            DeclKind::Entity { .. } => "entity",
            DeclKind::Arrow { .. } => "arrow",
            DeclKind::Correspondence { .. } => "correspondence",
            DeclKind::Data { .. } => "data",
            DeclKind::View { .. } => "view",
            DeclKind::Law { .. } => "law",
            DeclKind::Local { .. } => "local",
            DeclKind::Change { .. } => "change",
            DeclKind::Relation { .. } => "relation",
        }
    }

    pub fn is_primitive(&self) -> bool {
        matches!(
            self,
            DeclKind::Entity { .. }
                | DeclKind::Arrow { .. }
                | DeclKind::Correspondence { .. }
                | DeclKind::Data { .. }
        )
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Decl {
    pub name: Ident,
    pub kind: DeclKind,
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Use {
    pub reading: Ident,
    pub alias: Ident,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct VocabularyUse {
    pub namespace: Ident,
    pub version: String,
    pub digest: String,
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Reading {
    pub name: Ident,
    pub uses: Vec<Use>,
    pub vocabularies: Vec<VocabularyUse>,
    pub decls: Vec<Decl>,
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Header {
    pub format: String,
    pub semantics: String,
    pub span: Span,
}

/// 深い入れ子の型の構文木を、呼出し側のスタックの深さによらず解放する。
impl Drop for TypeAst {
    fn drop(&mut self) {
        let mut stack = Vec::new();
        take_children(self, &mut stack);
        while let Some(mut t) = stack.pop() {
            take_children(&mut t, &mut stack);
        }
    }
}

fn take_children(t: &mut TypeAst, stack: &mut Vec<TypeAst>) {
    let unit = || TypeAst::Builtin(Builtin::Unit, (0, 0));
    match t {
        TypeAst::Tuple(items, _) | TypeAst::Term(items, _, _) if !items.is_empty() => {
            stack.append(items);
            if let TypeAst::Term(_, r, _) = t {
                stack.push(std::mem::replace(&mut **r, unit()));
            }
        }
        TypeAst::Term(_, r, _)
        | TypeAst::List(r, _)
        | TypeAst::Set(r, _)
        | TypeAst::Option(r, _) => {
            stack.push(std::mem::replace(&mut **r, unit()));
        }
        TypeAst::Map(a, b, _) => {
            stack.push(std::mem::replace(&mut **a, unit()));
            stack.push(std::mem::replace(&mut **b, unit()));
        }
        _ => {}
    }
}

/// 深い入れ子の pattern を、呼出し側のスタックの深さによらず解放する。
impl Drop for Pattern {
    fn drop(&mut self) {
        let mut stack = Vec::new();
        if let Pattern::Ctor { args, .. } = self {
            stack.append(args);
        }
        while let Some(mut p) = stack.pop() {
            if let Pattern::Ctor { args, .. } = &mut p {
                stack.append(args);
            }
        }
    }
}

const RED_ZONE: usize = 64 * 1024;
const STACK_STEP: usize = 1024 * 1024;

/// 深い入れ子でも呼出し側のスタックを使い切らないよう、複製と比較は stacker を通す。
impl Clone for TypeAst {
    fn clone(&self) -> TypeAst {
        stacker::maybe_grow(RED_ZONE, STACK_STEP, || match self {
            TypeAst::Builtin(b, s) => TypeAst::Builtin(*b, *s),
            TypeAst::Fp { modulus, span } => TypeAst::Fp {
                modulus: modulus.clone(),
                span: *span,
            },
            TypeAst::Named { name, index, span } => TypeAst::Named {
                name: name.clone(),
                index: index.clone(),
                span: *span,
            },
            TypeAst::Tuple(items, s) => TypeAst::Tuple(items.clone(), *s),
            TypeAst::List(t, s) => TypeAst::List(Box::new((**t).clone()), *s),
            TypeAst::Set(t, s) => TypeAst::Set(Box::new((**t).clone()), *s),
            TypeAst::Option(t, s) => TypeAst::Option(Box::new((**t).clone()), *s),
            TypeAst::Map(a, b, s) => {
                TypeAst::Map(Box::new((**a).clone()), Box::new((**b).clone()), *s)
            }
            TypeAst::Term(args, r, s) => TypeAst::Term(args.clone(), Box::new((**r).clone()), *s),
            TypeAst::Path(a, b, s) => TypeAst::Path(a.clone(), b.clone(), *s),
        })
    }
}

impl PartialEq for TypeAst {
    fn eq(&self, other: &TypeAst) -> bool {
        stacker::maybe_grow(RED_ZONE, STACK_STEP, || match (self, other) {
            (TypeAst::Builtin(a, s), TypeAst::Builtin(b, t)) => a == b && s == t,
            (
                TypeAst::Fp {
                    modulus: a,
                    span: s,
                },
                TypeAst::Fp {
                    modulus: b,
                    span: t,
                },
            ) => a == b && s == t,
            (
                TypeAst::Named {
                    name: a,
                    index: i,
                    span: s,
                },
                TypeAst::Named {
                    name: b,
                    index: j,
                    span: t,
                },
            ) => a == b && i == j && s == t,
            (TypeAst::Tuple(a, s), TypeAst::Tuple(b, t)) => a == b && s == t,
            (TypeAst::List(a, s), TypeAst::List(b, t))
            | (TypeAst::Set(a, s), TypeAst::Set(b, t))
            | (TypeAst::Option(a, s), TypeAst::Option(b, t)) => **a == **b && s == t,
            (TypeAst::Map(a, b, s), TypeAst::Map(c, d, t)) => **a == **c && **b == **d && s == t,
            (TypeAst::Term(a, r, s), TypeAst::Term(b, q, t)) => a == b && **r == **q && s == t,
            (TypeAst::Path(a, b, s), TypeAst::Path(c, d, t)) => a == c && b == d && s == t,
            _ => false,
        })
    }
}

impl Clone for Pattern {
    fn clone(&self) -> Pattern {
        stacker::maybe_grow(RED_ZONE, STACK_STEP, || match self {
            Pattern::Wild(s) => Pattern::Wild(*s),
            Pattern::Name(i) => Pattern::Name(i.clone()),
            Pattern::Ctor { name, args, span } => Pattern::Ctor {
                name: name.clone(),
                args: args.clone(),
                span: *span,
            },
        })
    }
}

impl PartialEq for Pattern {
    fn eq(&self, other: &Pattern) -> bool {
        stacker::maybe_grow(RED_ZONE, STACK_STEP, || match (self, other) {
            (Pattern::Wild(a), Pattern::Wild(b)) => a == b,
            (Pattern::Name(a), Pattern::Name(b)) => a == b,
            (
                Pattern::Ctor {
                    name: a,
                    args: x,
                    span: s,
                },
                Pattern::Ctor {
                    name: b,
                    args: y,
                    span: t,
                },
            ) => a == b && x == y && s == t,
            _ => false,
        })
    }
}
