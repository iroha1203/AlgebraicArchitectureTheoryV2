# ArchSig 供給slot残債完遂 PRD(Issue #3859)

親 tracking: #3858(ArchSig大改修: 入力トライアドへの縮退)。
対象: 供給slot台帳(`archsig_v0_5_2_supplied_slot_ledger.md`)の残2行
(refactor morphism / refinement data)の三分法処分と、rename 類の周辺整理。

## 問い

残2行が解禁している結論は、入力トライアドの二系統(ArchMap=観測 / LawPolicy=法・方程式)から
**同じ結論として立て直せるか**。立て直せない結論は**沈黙へ戻せるか**。

採否の判定規律: 本 PRD の各要求は、この問いへの答え(導出化または沈黙化)を実現するものだけを採る。
供給面の純増、結論語彙の水増し、instance 依存の法側帰属は採らない
(refutation-checklist §8: 供給面の純増は返済ではない、法側帰属は instance 非依存の書き直しに限る)。

## 背景: 実読調査(2026-07-31)

### refactor morphism 行の実体

- validator(`tools/archsig/src/refactor.rs` `validate_refactor_morphism_v1`)は **shape 検査のみ**。
  `contextMap` / `coverMap` / `lawPairs` / `variableMap` は非空配列検査だけで、
  実在する ArchMap contexts・law surface・witness variables との照合は一切ない。
- 消費(`ag_measurement.rs` `refactor_transport_readings`)は、観測 atom
  (axis=`refactor`、predicate=`transportWitness` / `functorialityWitness`)を既存 verdict 行へ結び、
  結論コード `VERDICT_PRESERVED_UNDER_DECLARED_REFACTOR` を出す。名前が自認する通り
  **declared 読み**であり、供給 artifact の互換性主張は検証されないまま結論語彙を解禁している。
- 出荷 fixture(`tests/fixtures/ag_measurement/refactor_morphism.json`)は
  contextMap / coverMap / lawPairs / variableMap の**全対が恒等写像**であり、
  非自明な transport の実証例はリポジトリに存在しない(#3805 が指摘した退化 presentation と同型の構図)。

### refinement data 行の実体

- 結論コード `CLASS_ZERO_TRANSPORTED_UNDER_CHECKED_REFINEMENT` の実計算
  (`compare.rs` の transport 節)は「両 run の**導出済み** residual class が共に零」の判定であり、
  #3820 返済後は既に二系統から導出される値だけで立っている。
- 供給 artifact(`refinement-comparison/v0.5.4`)が追加する内容のうち、
  `complexFingerprint` の両 run binding は実検査だが、`zeroTransport.checked: true` は
  **宣言 boolean**(`map` は不透明文字列)で情報量ゼロ(#3805 の教訓:
  情報量ゼロの制約を認証条件に混ぜない)。
- 台帳が引く理論典拠「命題4.10」は、現行 canonical 本文に**該当番号の statement が存在しない**
  (`part_4_obstruction_cohomology.md` に 4.10 のアンカーなし。refinement 安定性の記述は
  479行・716行付近の散文)。anchor 自体が漂流しており、処分と同時に是正する。

## 裁定

### R1. refactor morphism 行 = 沈黙化

理由:

1. declared 契約は検証ゼロであり、解禁される結論は宣言の反復にすぎない。
2. 検証を実装しても morphism artifact 自体が第三入力チャネルとして残る。
   個別の rename map は instance 依存であり、法側帰属の資格(instance 非依存)を満たさない。
3. 唯一の fixture が恒等写像で、撤去によって失われる実証済みの価値がない。
4. 定理 7.3(第VIII部 Refactor Invariance under Equivalence)の形式化の家は Lean であり、
   refactor 後の run は直接 analyze できる。run 対の読みは compare の導出
   `residualDifferenceReading` が既に提供している(#3822 と同じ処分構図)。

処分内容:

- `analyze` の `--refactor-morphism` flag、`validate_refactor_morphism_v1`、
  `refactor_transport_readings`、結論コード `VERDICT_PRESERVED_UNDER_DECLARED_REFACTOR`、
  `ag.refactor-transport` evaluator 分岐(law policy registry 含む)、
  fixture `refactor_morphism.json`、対応テストを撤去する。
- ArchMap の axis=`refactor` 観測 atom は層 B の生値として正当な観測であり、受理を維持する。
  撤去するのは供給 artifact と、それが解禁していた transport 結論語彙だけである。

将来の再導入条件: 観測(refactor 対応の実測 atom)と法側検証から ArchSig が互換性を
**自分で検査して導出**できる設計が立つ場合に限り、新規 Issue として起こす。本 PRD では扱わない。

### R2. refinement data 行 = 導出化

理由: 結論の実計算は既に導出値だけで立つ。供給 artifact が担っていた残りは
(a) 宣言 boolean(情報量ゼロ、撤去)、(b) 両 run の binding(既存の実検査で維持可能)、
(c) coarse-to-fine の精細化関係の宣言、の三つで、(c) は両 run が記録している観測
(site / cover / chart 構造)から計算可能な述語である。

処分内容:

- `compare` の `--refinement` flag と `refinement-comparison` 供給 artifact を廃する。
- compare が両 run の記録から cover 精細化関係を**導出・検査**する。精細化述語の定義
  (fine cover の各 chart が coarse cover のいずれかの chart に含まれる、等)は、
  実装時に数学本文の refinement 記述(第IV部)の前提へ一致させて確定し、
  同時に台帳・出力の理論 anchor を実在する statement へ再帰属する(存在しない「命題4.10」は使わない)。
- 検査が立つ run 対に限り、従来と同じ結論コード `CLASS_ZERO_TRANSPORTED_UNDER_CHECKED_REFINEMENT`
  を出す(CHECKED の意味は「supplied boolean」から「ArchSig が導出・検査した」へ変わる。
  schema 記述と docs をこの意味で同期する)。
- 導出に必要な構造が run 記録に不足する場合は、run 記録側(ArchSig 自身の出力)を拡張する。
  これは第三入力の追加ではない。
- 精細化関係が導出不能または不成立の run 対は、named reason 付きの fail-closed silence とする。

検討した代替(沈黙化)の棄却理由: 結論の実体が既に導出済み値で立つため、
沈黙化は「導出できる結論を捨てる」過剰返済であり、三分法の優先順位(導出化が第一)に反する。

### R3. rename 類の周辺整理(#3817 積み残し)

- `docs/tool/ag_measurement_evidence_contract.md` の名称是正
  (供給時代の "evidence contract" 読み替え語彙からの rename)と、
  参照元 fixture / tests(`sourceRef.path`)の追随更新。
- website 配下の viewer artifact(`axisMapping` の "evidence contract" 軸ラベル等)を
  返済後の語彙で再生成する。
- `tools/archsig/examples/practical-rust-service/README.md` の Boundary 節を
  二系統入力の記述へ改める。

### R4. 台帳の最終確定

- R1 / R2 の処分結果を台帳の該当行へ反映し、負債告知を「残債ゼロ(本台帳は歴史記録)」へ更新する。
- 理論典拠列の漂流 anchor(命題4.10)を R2 で確定した実在 anchor へ差し替える。

## 受け入れ要件

- [ ] **R1**: 供給系の flag・validator・reading・結論コード・evaluator 分岐・fixture・テストが
      撤去され、`VERDICT_PRESERVED_UNDER_DECLARED_REFACTOR` が出力・schema catalog に現れない。
      axis=`refactor` 観測 atom の受理は維持されている(生値として)
- [ ] **R2 正例**: 供給 artifact なしで、精細化が成立する run 対に
      `CLASS_ZERO_TRANSPORTED_UNDER_CHECKED_REFINEMENT` が導出で立つテスト
- [ ] **R2 負例**: 精細化不成立・導出不能・片側非零の各 run 対が named reason 付き
      fail-closed silence になるテスト
- [ ] **R3**: rename 一式・viewer 軸ラベル再生成・README Boundary 節の是正
- [ ] **R4**: 台帳が処分結果と一致し、負債告知が更新され、漂流 anchor が解消している
- [ ] 診断階段の一次 workflow(analyze / compare / gate)が二系統入力で再現する
- [ ] 凍結証拠束(`docs/reports`)は byte 不変。fixture の expected 更新はテストで検証
- [ ] `cargo test --manifest-path tools/archsig/Cargo.toml` 全 pass
- [ ] `git diff --check` / hidden Unicode scan
- [ ] 返済差分が refutation-checklist §8 の資格を満たす(供給面の純増なし。
      本 PRD に法側帰属の行はない)

**縮小禁止**: R1〜R4 はいずれも後続 Issue への送り出し不可。裁定の変更が必要になった場合は
実装を止めて #3858 へエスカレーションする(スコープの黙った縮小・宣言落としを均衡点にしない)。

## スコープ外

- 証拠束の再計測: #3858 で全子完了後に一回だけ実施する。本 PRD では行わない。
- cost model 行・観測行・law equation grounded surface 行・diagnostic ceiling 行:
  台帳が二系統帰属の正規入力と裁定済みであり、対象外。
- モジュール分割(#3861)・外部帰属スイープ(#3862)との PR 混在禁止:
  本 PRD は語彙・境界を変えるため、挙動不変リファクタと同一 PR にしない。

## 実装順序の提案

R1(撤去)→ R2(導出化)→ R4(台帳)。R3 は独立に並行可。
R2 の精細化述語の確定は数学本文の実読を伴うため、実装 PR の冒頭で anchor 裁定を記録してから進める。
