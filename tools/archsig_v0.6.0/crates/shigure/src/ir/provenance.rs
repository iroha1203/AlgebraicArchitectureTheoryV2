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
    /// G-140 F1, F1.1–F1.2: 固定図式の独立全補完と 2-fiber（四角形・鎖・一般有限図式）。
    G140F1,
    G140F1Dot1,
    G140F1Dot2,
    /// G-140 F2, F3, F3.1: 一段変更から生成する経路、細分化 fiber、係数曲線反例。
    G140F2,
    G140F3,
    G140F3Dot1,
    /// G-140 台帳特殊化 P5.1–P5.3: Boolean 4 順序、Idle 切替 phase protocol、Busy 状態移送失敗。
    G140P5Dot1,
    G140P5Dot2,
    G140P5Dot3,
    /// G-140 G1–G3: 合法状態移送 lift、共通操作語保存、fiber product 移送合成。
    G140G1,
    G140G2,
    G140G3,
    /// G-140 E3–E5.1, P7: 複数解釈族、共有規則候補、3 量化、全係数移送安定性、reading 比較。
    G140E3,
    G140E4,
    G140E5,
    G140E5Dot1,
    G140P7,
    /// G-141 D6–D7: 構成可能な幾何的像、共有候補の Chevalley 四分類。
    G141D6,
    G141D7,
    /// G-142 G1–G7: 観測に相対的な判定、全係数移送、reading 比較、追加観測 kernel 条件、全包含極小観測、四分類。
    G142G1,
    G142G2,
    G142G3,
    G142G4,
    G142G5,
    G142G6,
    G142G7,
    /// G-141 E1–E8, C8–C9: 全 syzygy 平方零 lift・相対障害・宣言被覆比較・有限 étale 被覆 cocycle descent。
    G141E1,
    G141E2,
    G141E3,
    G141E4,
    G141E5,
    G141E6,
    G141E7,
    G141E8,
    G141C8,
    G141C9,
    /// G-141 F1–F9: 原始消去・全局所 Artin 試験・検出次数 ν・構文次数上界 D・一般係数冪零商 base change。
    G141F1,
    G141F2,
    G141F3,
    G141F4,
    G141F5,
    G141F6,
    G141F7,
    G141F8,
    G141F9,
    /// G-141 G1–G5: 有限連結単純グラフ実 adapter・SAGA 比較・制約付き全修復。
    G141G1,
    G141G2,
    G141G3,
    G141G4,
    G141G5,
    /// G-141 指定例 H1–H8, H10, H12。
    G141H1,
    G141H2,
    G141H3,
    G141H4,
    G141H5,
    G141H6,
    G141H7,
    G141H8,
    G141H10,
    G141H12,
    /// G-142 A1–A3, B1–B6, C1–C4, D1–D3: 整数診断複体・診断層 B_π・合流 Mayer–Vietoris・診断次元実現。
    G142A1,
    G142A2,
    G142A3,
    G142B1,
    G142B2,
    G142B3,
    G142B4,
    G142B5,
    G142B6,
    G142C1,
    G142C2,
    G142C3,
    G142C4,
    G142D1,
    G142D2,
    G142D3,
    /// G-142 E1–E6, F1–F7: 指定診断類 κ_b・Atlas 細分化 Condition C0–C6・評価条件付き全修復 fiber。
    G142E1,
    G142E2,
    G142E3,
    G142E4,
    G142E5,
    G142E6,
    G142F1,
    G142F2,
    G142F3,
    G142F4,
    G142F5,
    G142F6,
    G142F7,
    /// G-142 指定例 W1–W3, W5。
    G142W1,
    G142W2,
    G142W3,
    G142W5,
    /// AAT 第VI部 第17章（出現の同定と観測語彙）。
    AatCh17Thm17Dot2,
    AatCh17Def17Dot4,
    AatCh17Thm17Dot6,
    AatCh17Ex17Dot7,
    AatCh17Thm17Dot10,
    AatCh17Thm17Dot11,
    /// AAT 第VI部 第18章（部分提示・欠測と開領域の確定評価）。
    AatCh18Def18Dot1,
    AatCh18Thm18Dot3,
    AatCh18Def18Dot4,
    AatCh18Thm18Dot6,
    AatCh18Prop18Dot9,
    AatCh18Prop18Dot11,
    AatCh18Thm18Dot12,
    AatCh18Prop18Dot14,
    AatCh18Thm18Dot16,
    AatCh18Thm18Dot18,
    /// AAT 第VI部 第19章（観測の改訂・無効化範囲と多源統合）。
    AatCh19Prop19Dot2,
    AatCh19Thm19Dot4,
    AatCh19Thm19Dot7,
    AatCh19Thm19Dot9,
    AatCh19Thm19Dot11,
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
            MathClause::G140F1 => "shigure:G-140:F1",
            MathClause::G140F1Dot1 => "shigure:G-140:F1.1",
            MathClause::G140F1Dot2 => "shigure:G-140:F1.2",
            MathClause::G140F2 => "shigure:G-140:F2",
            MathClause::G140F3 => "shigure:G-140:F3",
            MathClause::G140F3Dot1 => "shigure:G-140:F3.1",
            MathClause::G140P5Dot1 => "shigure:G-140:P5.1",
            MathClause::G140P5Dot2 => "shigure:G-140:P5.2",
            MathClause::G140P5Dot3 => "shigure:G-140:P5.3",
            MathClause::G140G1 => "shigure:G-140:G1",
            MathClause::G140G2 => "shigure:G-140:G2",
            MathClause::G140G3 => "shigure:G-140:G3",
            MathClause::G140E3 => "shigure:G-140:E3",
            MathClause::G140E4 => "shigure:G-140:E4",
            MathClause::G140E5 => "shigure:G-140:E5",
            MathClause::G140E5Dot1 => "shigure:G-140:E5.1",
            MathClause::G140P7 => "shigure:G-140:P7",
            MathClause::G141D6 => "shigure:G-141:D6",
            MathClause::G141D7 => "shigure:G-141:D7",
            MathClause::G142G1 => "shigure:G-142:G1",
            MathClause::G142G2 => "shigure:G-142:G2",
            MathClause::G142G3 => "shigure:G-142:G3",
            MathClause::G142G4 => "shigure:G-142:G4",
            MathClause::G142G5 => "shigure:G-142:G5",
            MathClause::G142G6 => "shigure:G-142:G6",
            MathClause::G142G7 => "shigure:G-142:G7",
            MathClause::G141E1 => "shigure:G-141:E1",
            MathClause::G141E2 => "shigure:G-141:E2",
            MathClause::G141E3 => "shigure:G-141:E3",
            MathClause::G141E4 => "shigure:G-141:E4",
            MathClause::G141E5 => "shigure:G-141:E5",
            MathClause::G141E6 => "shigure:G-141:E6",
            MathClause::G141E7 => "shigure:G-141:E7",
            MathClause::G141E8 => "shigure:G-141:E8",
            MathClause::G141C8 => "shigure:G-141:C8",
            MathClause::G141C9 => "shigure:G-141:C9",
            MathClause::G141F1 => "shigure:G-141:F1",
            MathClause::G141F2 => "shigure:G-141:F2",
            MathClause::G141F3 => "shigure:G-141:F3",
            MathClause::G141F4 => "shigure:G-141:F4",
            MathClause::G141F5 => "shigure:G-141:F5",
            MathClause::G141F6 => "shigure:G-141:F6",
            MathClause::G141F7 => "shigure:G-141:F7",
            MathClause::G141F8 => "shigure:G-141:F8",
            MathClause::G141F9 => "shigure:G-141:F9",
            MathClause::G141G1 => "shigure:G-141:G1",
            MathClause::G141G2 => "shigure:G-141:G2",
            MathClause::G141G3 => "shigure:G-141:G3",
            MathClause::G141G4 => "shigure:G-141:G4",
            MathClause::G141G5 => "shigure:G-141:G5",
            MathClause::G141H1 => "shigure:G-141:H1",
            MathClause::G141H2 => "shigure:G-141:H2",
            MathClause::G141H3 => "shigure:G-141:H3",
            MathClause::G141H4 => "shigure:G-141:H4",
            MathClause::G141H5 => "shigure:G-141:H5",
            MathClause::G141H6 => "shigure:G-141:H6",
            MathClause::G141H7 => "shigure:G-141:H7",
            MathClause::G141H8 => "shigure:G-141:H8",
            MathClause::G141H10 => "shigure:G-141:H10",
            MathClause::G141H12 => "shigure:G-141:H12",
            MathClause::G142A1 => "shigure:G-142:A1",
            MathClause::G142A2 => "shigure:G-142:A2",
            MathClause::G142A3 => "shigure:G-142:A3",
            MathClause::G142B1 => "shigure:G-142:B1",
            MathClause::G142B2 => "shigure:G-142:B2",
            MathClause::G142B3 => "shigure:G-142:B3",
            MathClause::G142B4 => "shigure:G-142:B4",
            MathClause::G142B5 => "shigure:G-142:B5",
            MathClause::G142B6 => "shigure:G-142:B6",
            MathClause::G142C1 => "shigure:G-142:C1",
            MathClause::G142C2 => "shigure:G-142:C2",
            MathClause::G142C3 => "shigure:G-142:C3",
            MathClause::G142C4 => "shigure:G-142:C4",
            MathClause::G142D1 => "shigure:G-142:D1",
            MathClause::G142D2 => "shigure:G-142:D2",
            MathClause::G142D3 => "shigure:G-142:D3",
            MathClause::G142E1 => "shigure:G-142:E1",
            MathClause::G142E2 => "shigure:G-142:E2",
            MathClause::G142E3 => "shigure:G-142:E3",
            MathClause::G142E4 => "shigure:G-142:E4",
            MathClause::G142E5 => "shigure:G-142:E5",
            MathClause::G142E6 => "shigure:G-142:E6",
            MathClause::G142F1 => "shigure:G-142:F1",
            MathClause::G142F2 => "shigure:G-142:F2",
            MathClause::G142F3 => "shigure:G-142:F3",
            MathClause::G142F4 => "shigure:G-142:F4",
            MathClause::G142F5 => "shigure:G-142:F5",
            MathClause::G142F6 => "shigure:G-142:F6",
            MathClause::G142F7 => "shigure:G-142:F7",
            MathClause::G142W1 => "shigure:G-142:W1",
            MathClause::G142W2 => "shigure:G-142:W2",
            MathClause::G142W3 => "shigure:G-142:W3",
            MathClause::G142W5 => "shigure:G-142:W5",
            MathClause::AatCh17Thm17Dot2 => "aat:part6:17.2",
            MathClause::AatCh17Def17Dot4 => "aat:part6:17.4",
            MathClause::AatCh17Thm17Dot6 => "aat:part6:17.6",
            MathClause::AatCh17Ex17Dot7 => "aat:part6:17.7",
            MathClause::AatCh17Thm17Dot10 => "aat:part6:17.10",
            MathClause::AatCh17Thm17Dot11 => "aat:part6:17.11",
            MathClause::AatCh18Def18Dot1 => "aat:part6:18.1",
            MathClause::AatCh18Thm18Dot3 => "aat:part6:18.3",
            MathClause::AatCh18Def18Dot4 => "aat:part6:18.4",
            MathClause::AatCh18Thm18Dot6 => "aat:part6:18.6",
            MathClause::AatCh18Prop18Dot9 => "aat:part6:18.9",
            MathClause::AatCh18Prop18Dot11 => "aat:part6:18.11",
            MathClause::AatCh18Thm18Dot12 => "aat:part6:18.12",
            MathClause::AatCh18Prop18Dot14 => "aat:part6:18.14",
            MathClause::AatCh18Thm18Dot16 => "aat:part6:18.16",
            MathClause::AatCh18Thm18Dot18 => "aat:part6:18.18",
            MathClause::AatCh19Prop19Dot2 => "aat:part6:19.2",
            MathClause::AatCh19Thm19Dot4 => "aat:part6:19.4",
            MathClause::AatCh19Thm19Dot7 => "aat:part6:19.7",
            MathClause::AatCh19Thm19Dot9 => "aat:part6:19.9",
            MathClause::AatCh19Thm19Dot11 => "aat:part6:19.11",
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
