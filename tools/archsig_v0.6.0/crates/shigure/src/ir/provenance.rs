//! 由来（OriginKind・SourceRef）と SHIGURE 紙上証明条項への安定参照。

use archsig_common::canonical::{Json, JsonObject};

/// 観測・読解・採用の由来種別。
/// LLM の読解候補・静的解析・実行観測・人間採用を型で区別し混同を防ぐ。
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum OriginKind {
    /// 静的解析による観測事実。
    StaticAnalysis,
    /// 実行観測による事実。
    RuntimeObservation,
    /// LLM による読解候補（確定事実ではない）。
    LlmCandidate,
    /// 人間が採用・確認した宣言または事実。
    HumanAdopted,
}

impl OriginKind {
    pub fn wire(self) -> &'static str {
        match self {
            OriginKind::StaticAnalysis => "static_analysis",
            OriginKind::RuntimeObservation => "runtime_observation",
            OriginKind::LlmCandidate => "llm_candidate",
            OriginKind::HumanAdopted => "human_adopted",
        }
    }

    pub fn from_wire(s: &str) -> Option<Self> {
        match s {
            "static_analysis" => Some(OriginKind::StaticAnalysis),
            "runtime_observation" => Some(OriginKind::RuntimeObservation),
            "llm_candidate" => Some(OriginKind::LlmCandidate),
            "human_adopted" => Some(OriginKind::HumanAdopted),
            _ => None,
        }
    }
}

/// 元の Atom 定義・Law・ArchMap の位置への由来参照。
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct SourceRef {
    pub origin_id: String,
    pub kind: OriginKind,
    pub source_id: Option<String>,
    pub path: Option<String>,
    pub span: Option<(u64, u64)>,
    pub atom_ref: Option<String>,
    pub law_declaration: Option<String>,
}

impl SourceRef {
    pub fn new(origin_id: impl Into<String>, kind: OriginKind) -> Self {
        Self {
            origin_id: origin_id.into(),
            kind,
            source_id: None,
            path: None,
            span: None,
            atom_ref: None,
            law_declaration: None,
        }
    }

    pub fn with_location(
        mut self,
        source_id: impl Into<String>,
        path: impl Into<String>,
        span: Option<(u64, u64)>,
    ) -> Self {
        self.source_id = Some(source_id.into());
        self.path = Some(path.into());
        self.span = span;
        self
    }

    pub fn with_atom_ref(mut self, atom_ref: impl Into<String>) -> Self {
        self.atom_ref = Some(atom_ref.into());
        self
    }

    pub fn with_law_declaration(mut self, decl: impl Into<String>) -> Self {
        self.law_declaration = Some(decl.into());
        self
    }

    pub fn to_json(&self) -> Json {
        let mut obj = JsonObject::from([
            ("origin_id".into(), Json::str(&self.origin_id)),
            ("kind".into(), Json::str(self.kind.wire())),
        ]);
        if let Some(src) = &self.source_id {
            obj.insert("source_id".into(), Json::str(src));
        }
        if let Some(path) = &self.path {
            obj.insert("path".into(), Json::str(path));
        }
        if let Some((start, end)) = self.span {
            obj.insert(
                "span".into(),
                Json::Arr(vec![Json::Nat(start), Json::Nat(end)]),
            );
        }
        if let Some(atom) = &self.atom_ref {
            obj.insert("atom_ref".into(), Json::str(atom));
        }
        if let Some(decl) = &self.law_declaration {
            obj.insert("law_declaration".into(), Json::str(decl));
        }
        Json::Obj(obj)
    }
}

/// 有限特殊化が対応する SHIGURE 紙上証明条項の安定識別子。
/// 出力にリポジトリローカルパスを露出せず、安定 ID を用いる。
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum MathClause {
    /// G-139 P0–P1, G-140 P0.1: 原始表示と型付き affine / 多項式 term の評価一致。
    G139P0P1,
    G140P0Dot1,
    /// G-140 A2, P1, P3–P5: 意味保存射・操作語翻訳による全許可有限語の保存と商環状態 Law 閉性。
    G140A2,
    G140P1,
    G140P3P5,
    /// G-140 E1–E2, P6: 条件付き解空間 F_{a,H,P} と復元。
    G140E1E2,
    G140P6,
    /// G-141 D1, D4, D5: 有限還元、F_p / アフィン、Q 上 Gröbner・Rabinowitsch・商環所属。
    G141D1,
    G141D4,
    G141D5,
    /// G-141 F10–F12: 座標面支持による相互作用参加変数数 r と極小不成立部分族。
    G141F10F12,
}

impl MathClause {
    pub fn stable_id(self) -> &'static str {
        match self {
            MathClause::G139P0P1 => "shigure:G-139:P0-P1",
            MathClause::G140P0Dot1 => "shigure:G-140:P0.1",
            MathClause::G140A2 => "shigure:G-140:A2",
            MathClause::G140P1 => "shigure:G-140:P1",
            MathClause::G140P3P5 => "shigure:G-140:P3-P5",
            MathClause::G140E1E2 => "shigure:G-140:E1-E2",
            MathClause::G140P6 => "shigure:G-140:P6",
            MathClause::G141D1 => "shigure:G-141:D1",
            MathClause::G141D4 => "shigure:G-141:D4",
            MathClause::G141D5 => "shigure:G-141:D5",
            MathClause::G141F10F12 => "shigure:G-141:F10-F12",
        }
    }
}

/// 入力や計算結果に付随する由来と数学対応条項の束。
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Provenance {
    pub origins: Vec<SourceRef>,
    pub clauses: Vec<MathClause>,
}

impl Provenance {
    pub fn new(origins: Vec<SourceRef>, clauses: Vec<MathClause>) -> Self {
        Self { origins, clauses }
    }

    pub fn to_json(&self) -> Json {
        Json::obj([
            (
                "origins",
                Json::Arr(self.origins.iter().map(SourceRef::to_json).collect()),
            ),
            (
                "clauses",
                Json::Arr(
                    self.clauses
                        .iter()
                        .map(|c| Json::str(c.stable_id()))
                        .collect(),
                ),
            ),
        ])
    }
}
