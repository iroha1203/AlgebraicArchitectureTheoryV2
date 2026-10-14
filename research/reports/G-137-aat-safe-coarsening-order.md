# G-137 証明記録

固定GOAL・設計・共通基準: `d6d19ba0b199d499e1aa0239b60d71c50aa4bee4`。
GOAL blob: `00278db46e595fbe30762a1bb969230f77828f4f`。
既存宣言の参照版: `f3ae0eab35186e2259fa030eb23fb4657180a868`。
追跡: [#5358](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/5358)。

## 現 proof obligation

T0・A–Eを固定したまま進める。Cycle 1はT0とAの原始商・因子化・原始比較の
恒等と合成の受理候補である。全GOALは `target-proof-checkpoint`。
Aの二段商の同型、実cochain/H¹合成とLaw/G-135接続、B–Eは未完了。
P_G・P_J・P_N、W1・W2の指定評価は未判定。Formalへの蒸留は未実施。

## Cycle 1 selection

selectionは実装前に[開始コメント](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/5358#issuecomment-6167942871)で固定した。

```yaml
ledger_type: target_cycle_result
goal: G-137-aat-safe-coarsening-order
cycle: 1
goal_blob_sha: 00278db46e595fbe30762a1bb969230f77828f4f
base_oid: 38178c6e86f4e8f353f7b05d7b6e9b7db7ac40e4
tracking_issue: 5358
report_path: research/reports/G-137-aat-safe-coarsening-order.md
selection:
  proof_state_ref: tracking Issueの未着手記録と開始コメント
  proof_dag_predecessors: [RI.TargetSupportedNerve, RI.TargetSupportedNerveMorphism, RI.comparisonFactor_unique, FRS.ofHereditary, ADC.comparisonComp, mathlib.Setoid]
  milestone: T0とAの原始商・因子化・原始比較の恒等と合成
  proof_obligations: [全分割対からの商readingと台と有向辺, 全Rの原始比較, 関係包含と可換二因子の同値, 任意R≤R'の比較, 原始直接比較と合成の全record等号, 恒等比較の全計算成分]
  exit_criteria: [任意Rの商生成, 原始端点と支持条件の放電, le_iff_factors, quotientMorphism_factorとfactorMorphism_comp, 恒等chartとedgeと空face, focused checkと全宣言公理監査]
  selection_reason: B以後の全分割対分類が使う商と実比較の原始入力を生成する
  expected_result_type: proof-obligation-discharged
  lean_targets: [PrimitiveInput.lean, QuotientNerve.lean, Factorization.lean, PrimitiveExamples.lean]
  risks: [逆向き辺の誤併合, 元商写像を忘れた同一視, 結論の入力fieldへの移動, 原辺台の像とK1商台の混同]
  unchecked: [正式PR査読]
```

## 宣言と条項の対応

namespaceは `AAT.AG.SafeCoarseningOrder`。cycle scaffoldはない。
各行の公開API、structureの生成宣言、instance chainも受理対象とする。

| 条項 | ファイル・実宣言 | 入力・構成と使用先 |
| --- | --- | --- |
| T0 原始表 | `PrimitiveInput`, `PrimitiveInput.reading`, `Edge`, `nerve`, `supported`, `mem_edgeSupport`, `edge_endpoints_ne` | 全射q、対角を含まない辺、非空台だけを保持。既存reading・K1 nerveに接続。S/T/Vの有限非空条件は固定T0であり、汎用補助APIは条件を使わない場合より一般の型でも成立する。 |
| T0 全粗化と順序 | `Coarsening` | mathlibの全 `Setoid T × Setoid V`。関係包含の積complete lattice。安全性による入力候補の削減をしない。 |
| 任意Rの商 | `quotientReading`, `quotientSupport`, `quotientSupport_mk`, `quotientSupport_nonempty`, `quotientEdge`, `QuotientEdge`, `quotientNerve`, `quotientSupported`, `mem_quotient_edgeSupport` | chart fiber内の合併の像とK1交差、有向順序対の存在から全商を生成。平行辺の生成証拠はProp。 |
| fineから商への原始比較 | `quotient_coarser`, `quotient_factor`, `quotientEdgeMap`, `quotientEdgeMap_eq_none`, `quotientEdgeMap_eq_some`, `quotientMorphism`, `quotientComparison` | target商写像をcanonical factorと同定し、chart・部分edge・空faceと全支持条件を放電。G-134へ同じ比較を埋め込む。 |
| 因子化の必要十分 | `Coarsening.factor`, `factor_mk`, `factor_unique`, `le_iff_factor`, `le_iff_factors`, `factor_refl`, `factor_comp` | 元T/Vからの商写像と可換な二因子の存在を関係包含と同値にする。二因子の一意性と恒等・合成も証明。 |
| 全R≤R'の原始比較 | `factor_coarser`, `factor_comparisonFactor`, `factor_support`, `factorEdgeMap`, `factorEdgeMap_eq_none`, `factorEdgeMap_eq_some`, `factorMorphism` | 包含からtarget/chart因子と原始部分セル像を生成。台輸送と空面条件を入力表から放電。 |
| 全record合成と恒等 | `quotientEdgeMap_factor`, `morphism_ext`, `quotientMorphism_factor`, `factorEdgeMap_comp`, `factorMorphism_comp`, `factorMorphism_refl_chart`, `factorMorphism_refl_edge` | 直接辺像はOption.bindと一致。chart/edge/faceの全計算成分を照合して既存G-133比較合成と全record等号を示す。face成分は空型。 |
| 発火と対角除外 | `w0`, `w0Edge`, `w0_top_edge_none`, `w0_bot_edge_not_none`, `primitive_no_diagonal` | W0の原始表で全関係による縮約と恒等分割での保持を同時に評価。対角を含む表がT0に入らないことを示す。W0のH¹・安全順序・定数Law評価は後続。 |

## 前提・構成と再利用

| 前提 | 分類 | 出所・使用先・状態 |
| --- | --- | --- |
| S/T/Vの有限非空性、全射q、対角除外、有向辺、非空台、空面 | ambient-boundary / 本文由来 | T0。セルの有限性、reading、非空商台、原始nerveを生成。W0では全条件を構成。 |
| 任意の分割対R、R≤R' | ambient-boundary / 本文由来 | T0・A。mathlib Setoidの全関係と包含。因子と部分セル像を生成。 |
| 商reading・商台・商辺・原始比較と支持輸送 | discharge-required / 放電済み候補 | 上表のquotient/factor producer。比較同型・rank・安全元一覧を入力に置いていない。 |
| 原始因子化の逆方向と恒等・合成 | discharge-required / 放電済み候補 | le_iff_factors、全record合成、恒等成分。実cochain/H¹への接続は後続義務。 |
| 二段商の同型、全Law同値とG-135、B–E | discharge-required / 未完了 | 本cycleの受理主張に含めない。全GOALの未完了として保持。 |

既存宣言の関連5 sourceは参照版とbaseで差分なし。
`RI.TargetSupportedNerve` の全有限セル・K1台・空面端点条件、
`TargetSupportedNerveMorphism` の部分セル像・支持輸送を実型で確認した。
`comparisonFactor_unique` はreading全射から一意性を示し、今回の標準商因子へ適用する。
`FRS.ofHereditary` は同じchart/edge/faceをincidence比較に埋め込む。
`ADC.comparisonComp` はchart合成とedge/faceのOption.bindを持ち、今回の原始直接比較と等しい。
受理記録は[G-133 PR #5269](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5269#issuecomment-6007700344)と
[G-134 PR #5287](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5287#issuecomment-6030258596)。
G-135/G-136の[Research完了](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/5290#issuecomment-6078348119)・
[完了同期](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/5321#issuecomment-6117232196)は確認済み。
その同じ実H¹と有限判定、W3比較への接続は後続cycleで行う。
Lean v4.28.0、mathlib `8f9d9cff6bd728b17a24e163c9402775d9e6a365`のSetoid complete latticeと標準商APIを用いる。

## Cycle 1 result proposal

```yaml
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: 全Rの原始商、分割包含と二可換因子の同値、原始比較生成と全record恒等・合成
  exit_criteria_status: [全4sourceの個別検証, le_iff_factors, quotientMorphism_factor, factorMorphism_comp, 恒等成分評価, W0縮約と保持]
  split_reason: none
  completion_candidate: no
  lean_artifacts: [PrimitiveInput.lean, QuotientNerve.lean, Factorization.lean, PrimitiveExamples.lean]
  evidence: [宣言と条項の対応表]
  claim_mapping:
    theorem_names: [le_iff_factors, quotientMorphism_factor, factorMorphism_comp, factorMorphism_refl_chart, factorMorphism_refl_edge]
    source_labels: [T0, A 原始商と因子化と原始比較]
    conjuncts: [上記対応表]
    undischarged_assumptions: []
    acceptance_point: 任意分割対と任意包含からの全原始比較を生成し全計算成分を照合
    port_status: unported
audits:
  premise_delta:
    discharged: [商非空台, 原始比較の全incidenceと支持条件, 関係包含と因子化, 原始恒等と合成]
    remaining: [Aの二段商同型と実比較とLawとG-135接続, B–E]
  certificate_provenance:
    discharged: [quotientMorphismとfactorMorphismを元表から生成, w0の原始表]
    unresolved: []
  proof_use:
    used: [q全射→商全射とcanonical factor一意性, 元非空台→全商非空台, 分割包含→target/chart因子, 原始辺存在→商辺, 原始端点→全record合成]
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs: [個別focusedと公理監査はPR証跡に固定]
  blocking_findings: [標準PR独立査読前]
  next_obligation: Aの二段商同型と実cochain/H¹とLaw/G-135接続
```

正式受理、固定head、review evidence、CI、mergeと次義務はPR監査とtracking Issueに記録する。
Research検証はこの到達点の個別sourceと単一監査fileに限定する。
本体・Researchの全体build、Research aggregate検証、Formal移植は実施しない。
