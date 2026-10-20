//! 元 byte 列と検査済み三表を同じ定義 identity の下で保持する。

mod comparison;

use super::control::{CheckFailure, Checkpoint, Control, StopReason};
use crate::{
    archmap::{CheckedArchMap, check_archmap_controlled},
    canonical::{Json, sha256_digest},
    definition::{
        CheckedDefinitions, PrimitiveDeclaration, Vocabulary, check_definitions_controlled,
    },
    issue::{Code, Details, Issue, Location},
    json::InputError,
    law::{CheckedLaw, check_law_controlled, model::DeclarationInfo},
    result::{InputIdentity, ResultIssue, metadata_wire},
};

/// 読込み済み入力。識別と元 byte 列は bundle 構成後に変更できない。
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct InputBytes {
    id: String,
    bytes: Vec<u8>,
}

impl InputBytes {
    pub fn new(id: impl Into<String>, bytes: impl Into<Vec<u8>>) -> Self {
        Self {
            id: id.into(),
            bytes: bytes.into(),
        }
    }
    pub fn id(&self) -> &str {
        &self.id
    }
    pub fn bytes(&self) -> &[u8] {
        &self.bytes
    }
}

/// 明示された順の定義ファイル列、Law、ArchMap。全入力を開始時に所有する。
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct InputSources {
    definitions: Vec<InputBytes>,
    law: InputBytes,
    archmap: InputBytes,
}

impl InputSources {
    pub fn new(definitions: Vec<InputBytes>, law: InputBytes, archmap: InputBytes) -> Self {
        Self {
            definitions,
            law,
            archmap,
        }
    }

    /// 結果仕様の固定 ID を指定順に割り当てる。
    pub fn from_bytes(definitions: Vec<Vec<u8>>, law: Vec<u8>, archmap: Vec<u8>) -> Self {
        Self::new(
            definitions
                .into_iter()
                .enumerate()
                .map(|(i, b)| InputBytes::new(format!("definition{i}"), b))
                .collect(),
            InputBytes::new("law", law),
            InputBytes::new("archmap", archmap),
        )
    }
    pub fn definitions(&self) -> &[InputBytes] {
        &self.definitions
    }
    pub fn law(&self) -> &InputBytes {
        &self.law
    }
    pub fn archmap(&self) -> &InputBytes {
        &self.archmap
    }

    // 失敗表示にも必要な全 read 行を準備する。digest の計算・入力検査は含めない。
    fn identity_rows(&self) -> Vec<InputIdentity> {
        let mut ids: Vec<_> = self
            .definitions
            .iter()
            .enumerate()
            .map(|(i, _)| InputIdentity {
                id: format!("definition{i}"),
                kind: "atom_definition",
                read: true,
                bytes_digest: None,
                model_digest: None,
                path: None,
            })
            .collect();
        for (id, kind) in [("law", "law"), ("archmap", "archmap")] {
            ids.push(InputIdentity {
                id: id.into(),
                kind,
                read: true,
                bytes_digest: None,
                model_digest: None,
                path: None,
            });
        }
        ids.sort_by(|a, b| a.id.cmp(&b.id));
        ids
    }
}

/// 入力段階の失敗。算法非対応を版非対応へ読み替えない。
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum InputStatus {
    Invalid,
    Unsupported,
    Interrupted,
    Error,
}

impl InputStatus {
    pub fn wire(self) -> &'static str {
        match self {
            Self::Invalid => "invalid",
            Self::Unsupported => "unsupported",
            Self::Interrupted => "interrupted",
            Self::Error => "error",
        }
    }
}

/// 入力が完成しなくても段階規則に従う metadata と停止原因を保持する。
#[derive(Debug)]
pub struct InputFailure {
    status: InputStatus,
    sources: InputSources,
    inputs: Vec<InputIdentity>,
    declarations: Vec<DeclarationInfo>,
    primitives: Vec<PrimitiveDeclaration>,
    vocabularies: Vec<Vocabulary>,
    issues: Vec<Json>,
}

impl InputFailure {
    pub fn status(&self) -> InputStatus {
        self.status
    }
    pub fn sources(&self) -> &InputSources {
        &self.sources
    }
    pub fn inputs(&self) -> &[InputIdentity] {
        &self.inputs
    }
    pub fn declarations(&self) -> &[DeclarationInfo] {
        &self.declarations
    }
    pub fn primitives(&self) -> &[PrimitiveDeclaration] {
        &self.primitives
    }
    pub fn vocabularies(&self) -> &[Vocabulary] {
        &self.vocabularies
    }
    pub fn issues(&self) -> &[Json] {
        &self.issues
    }

    /// 内部段階の結果。CLI の command/exit_code/配送情報は含めない。
    pub fn wire(&self) -> Json {
        let mut wire = Json::Obj(metadata_wire(
            &self.inputs,
            &self.declarations,
            &self.primitives,
            &self.vocabularies,
        ));
        let Json::Obj(fields) = &mut wire else {
            unreachable!()
        };
        fields.insert("status".into(), Json::str(self.status.wire()));
        fields.insert("issues".into(), Json::Arr(self.issues.clone()));
        for name in ["requests", "answers", "nodes"] {
            fields.insert(name.into(), Json::Arr(vec![]));
        }
        wire
    }

    fn checked(self, error: CheckFailure<Box<Issue>>, control: &Control) -> Self {
        match error {
            CheckFailure::Input(issue) => self.input_with_control(*issue, control),
            CheckFailure::Stopped(reason) => self.stopped(reason),
        }
    }

    fn input(mut self, issue: Issue) -> Self {
        self.status = if issue.code == Code::UnsupportedVersion {
            InputStatus::Unsupported
        } else {
            InputStatus::Invalid
        };
        self.issues.push(ResultIssue::Input(issue).wire());
        self
    }
    fn input_with_control(self, issue: Issue, control: &Control) -> Self {
        let mut failure = self.input(issue);
        if let Some(reason @ StopReason::BudgetExhausted { .. }) = control.stop_reason() {
            // 全入力 Issue code より budget_exhausted が辞書順で先。
            // 既知の入力不正の優先状態を保ち、併発した停止理由も出力に残す。
            failure.issues.insert(0, reason.wire());
        }
        failure
    }
    fn stopped(mut self, reason: StopReason) -> Self {
        self.status = InputStatus::Interrupted;
        self.issues.push(reason.wire());
        self
    }
    // 検査で既に得た digest を失敗時の表示へ写す finalize。意味検査を開始しない。
    fn digest(&mut self, id: &str, digest: Option<String>) {
        if let Some(input) = self.inputs.iter_mut().find(|i| i.id == id) {
            input.model_digest = digest;
        }
    }
}

/// 評価はこの不変 bundle を借用し、検査を繰り返さず三表を利用する。
#[derive(Debug)]
pub struct CheckedInputs {
    sources: InputSources,
    inputs: Vec<InputIdentity>,
    definitions: CheckedDefinitions,
    law: CheckedLaw,
    archmap: CheckedArchMap,
}

impl CheckedInputs {
    pub fn sources(&self) -> &InputSources {
        &self.sources
    }
    pub fn inputs(&self) -> &[InputIdentity] {
        &self.inputs
    }
    pub fn definitions(&self) -> &CheckedDefinitions {
        &self.definitions
    }
    pub fn law(&self) -> &CheckedLaw {
        &self.law
    }
    pub fn archmap(&self) -> &CheckedArchMap {
        &self.archmap
    }
    pub fn metadata_wire(&self) -> Json {
        Json::Obj(metadata_wire(
            &self.inputs,
            &self.law.infos,
            self.definitions.declarations.values(),
            self.definitions.vocabularies.values(),
        ))
    }

    fn into_failure(self, clear_law: bool) -> InputFailure {
        InputFailure {
            status: InputStatus::Invalid,
            sources: self.sources,
            inputs: self.inputs,
            declarations: if clear_law { vec![] } else { self.law.infos },
            primitives: if clear_law {
                vec![]
            } else {
                self.definitions.declarations.into_values().collect()
            },
            vocabularies: if clear_law {
                vec![]
            } else {
                self.definitions.vocabularies.into_values().collect()
            },
            issues: vec![],
        }
    }

    /// 外部の検査済み表を採用するときだけ元 byte 列へ照合する。
    /// 現行の表は公開 field を持つため digest の一致だけを証拠にしない。
    #[allow(clippy::result_large_err)]
    pub fn from_checked(
        sources: InputSources,
        definitions: CheckedDefinitions,
        law: CheckedLaw,
        archmap: CheckedArchMap,
        control: &mut Control,
    ) -> Result<Self, InputFailure> {
        let verified = check_inputs(sources, control)?;
        if let Err(error) = BundleError::checkpoint(control, Checkpoint::InputBundle) {
            return Err(verified.into_failure(false).checked(error, control));
        }
        let mut law_comparison = comparison::Comparison::new(
            control,
            Location::Law {
                span: (0, verified.sources.law.bytes.len()),
            },
        );
        let law_result = (|| {
            law_comparison.eq(&definitions, &verified.definitions)?;
            law_comparison.eq(&law.definitions, &definitions)?;
            law_comparison.eq(&law, &verified.law)
        })();
        let bad_law = law_comparison.mismatched;
        // 比較前の停止は不一致を確定しない。比較で得た不一致の段階だけを保持する。
        let result = match law_result {
            Err(error) => Err(error),
            Ok(()) => {
                let mut map_comparison = comparison::Comparison::new(
                    control,
                    Location::ArchMap {
                        pointer: String::new(),
                        span: None,
                    },
                );
                map_comparison.eq(&archmap, &verified.archmap)
            }
        };
        if let Err(error) = BundleError::finish(result, control, Checkpoint::InputBundle) {
            return Err(verified.into_failure(bad_law).checked(error, control));
        }
        // 公開 field を照合した後も、元 byte 列から得た表だけを採用する。
        Ok(verified)
    }
}

type BundleError = CheckFailure<Box<Issue>>;

/// 定義→Law→ArchMap の全検査。どの段階の中断にも同じ制御を渡す。
#[allow(clippy::result_large_err)]
pub fn check_inputs(
    sources: InputSources,
    control: &mut Control,
) -> Result<CheckedInputs, InputFailure> {
    let mut failure = InputFailure {
        status: InputStatus::Invalid,
        inputs: sources.identity_rows(),
        sources,
        declarations: vec![],
        primitives: vec![],
        vocabularies: vec![],
        issues: vec![],
    };
    // 全入力の byte 列は取得済み。未計算の SHA は optional のまま残し、
    // 停止を観測した後に次の入力の原始演算を開始しない。
    for index in 0..failure.inputs.len() {
        if let Err(error) = BundleError::checkpoint(control, Checkpoint::InputBundle) {
            return Err(failure.checked(error, control));
        }
        let id = failure.inputs[index].id.as_str();
        let bytes = match id {
            "law" => failure.sources.law.bytes(),
            "archmap" => failure.sources.archmap.bytes(),
            _ => {
                let index = id
                    .strip_prefix("definition")
                    .unwrap()
                    .parse::<usize>()
                    .unwrap();
                failure.sources.definitions[index].bytes()
            }
        };
        failure.inputs[index].bytes_digest = Some(sha256_digest(bytes));
        if let Err(error) = BundleError::finish(Ok(()), control, Checkpoint::InputBundle) {
            return Err(failure.checked(error, control));
        }
    }
    let invalid_id = || {
        let location = if failure.sources.definitions.is_empty() {
            Location::Law { span: (0, 0) }
        } else {
            Location::Definition {
                input: "definition0".into(),
                pointer: String::new(),
                span: None,
            }
        };
        CheckFailure::Input(Box::new(Issue {
            code: Code::Reference,
            message: "入力 ID は指定順の definition0,…、law、archmap でなければならない".into(),
            location,
            details: Details::Empty,
        }))
    };
    // ID 照合は実際の検査であり、失敗する一回にも事後確認を行う。
    for index in 0..failure.sources.definitions.len() + 2 {
        if let Err(error) = BundleError::checkpoint(control, Checkpoint::InputBundle) {
            return Err(failure.checked(error, control));
        }
        let (actual, expected) = if index < failure.sources.definitions.len() {
            (
                failure.sources.definitions[index].id(),
                format!("definition{index}"),
            )
        } else if index == failure.sources.definitions.len() {
            (failure.sources.law.id(), "law".into())
        } else {
            (failure.sources.archmap.id(), "archmap".into())
        };
        let result = if actual == expected && !failure.sources.definitions.is_empty() {
            Ok(())
        } else {
            Err(invalid_id())
        };
        if let Err(error) = BundleError::finish(result, control, Checkpoint::InputBundle) {
            return Err(failure.checked(error, control));
        }
    }
    if let Err(reason) = control.checkpoint(Checkpoint::BeforeDefinitions) {
        return Err(failure.stopped(reason));
    }
    let mut files = Vec::with_capacity(failure.sources.definitions.len());
    for input in &failure.sources.definitions {
        if let Err(error) = BundleError::checkpoint(control, Checkpoint::InputBundle) {
            return Err(failure.checked(error, control));
        }
        files.push((input.id(), input.bytes()));
        if let Err(error) = BundleError::finish(Ok(()), control, Checkpoint::InputBundle) {
            return Err(failure.checked(error, control));
        }
    }
    let definitions = match check_definitions_controlled(&files, control) {
        Ok(d) => d,
        Err(CheckFailure::Input(f)) => {
            for identity in f.inputs {
                failure.digest(&identity.input, identity.model_digest);
            }
            return Err(failure.input_with_control(f.issue, control));
        }
        Err(CheckFailure::Stopped(reason)) => return Err(failure.stopped(reason)),
    };
    for identity in &definitions.inputs {
        failure.digest(&identity.input, identity.model_digest.clone());
    }
    for point in [Checkpoint::AfterDefinitions, Checkpoint::BeforeLaw] {
        if let Err(reason) = control.checkpoint(point) {
            return Err(failure.stopped(reason));
        }
    }
    let law = match check_law_controlled(failure.sources.law.bytes(), &definitions, control) {
        Ok(law) => law,
        Err(CheckFailure::Input(f)) => {
            failure.digest("law", f.model_digest);
            return Err(failure.input_with_control(f.issue, control));
        }
        Err(CheckFailure::Stopped(reason)) => return Err(failure.stopped(reason)),
    };
    failure.digest("law", Some(law.model_digest.clone()));
    failure.declarations = law.infos.clone();
    failure.primitives = definitions.declarations.values().cloned().collect();
    failure.vocabularies = definitions.vocabularies.values().cloned().collect();
    for point in [Checkpoint::AfterLaw, Checkpoint::BeforeArchMap] {
        if let Err(reason) = control.checkpoint(point) {
            return Err(failure.stopped(reason));
        }
    }
    let archmap =
        match check_archmap_controlled(failure.sources.archmap.bytes(), &definitions, control) {
            Ok(map) => map,
            Err(CheckFailure::Input(f)) => return Err(failure.input_with_control(f.issue, control)),
            Err(CheckFailure::Stopped(reason)) => return Err(failure.stopped(reason)),
        };
    failure.digest("archmap", Some(archmap.model_digest.clone()));
    if let Err(reason) = control.checkpoint(Checkpoint::AfterArchMap) {
        return Err(failure.stopped(reason));
    }
    Ok(CheckedInputs {
        sources: failure.sources,
        inputs: failure.inputs,
        definitions,
        law,
        archmap,
    })
}
