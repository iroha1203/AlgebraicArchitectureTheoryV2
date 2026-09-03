# G-116-aat-idempotent-exchange-structure — exchange 反例の背後にある冪等正規化構造

- `id`: `G-116-aat-idempotent-exchange-structure`(旧 id `G-116-aat-gr4-capstone`。
  番号は同じ)
- `status`: `draft`
- `priority`: `high`
- `research mode`: `target-theorem`
- `program context`: Gr4 系列。G-110 の generated comparison が同型にならない
  理由を、比較射に含まれる冪等な正規化因子の数学的な正体として同定する。
  Gr4 達成記録(旧 O19)、旧 O12 のうち G-114 refinement mate と G-115
  `upperDecisionSolution` の決定、義務台帳 O1–O20 は、Gr4 を閉じるカード(別途、
  番号は先取りしない)が担う。本カードは Gr4 の最後のカードではない。先行カード
  (G-111〜G-115)の本文にある「義務台帳は G-116」「O12 は G-116」「successor G-116」
  という記述は、完了時点の記録として据え置き、Gr4 を閉じるカードを指すと読む。
  依存する reviewed カード(G-110、G-113)の statement が改訂された場合は、本カード
  を draft へ差し戻して再固定する。
- `predecessor`: G-110(完遂済み。canonical mate の同型性、generated comparison、
  finite axis-fold witness、MateCoherentRel 正負対)、G-113(完遂済み。transport
  equivalence O13・O18)。
- `tracking issue`: 未起票(active 昇格時に起票)
- `source note`: [n1008](../../docs/note/n1008_aat_idempotent_exchange_structure_program.md)
  (§1 反例の形、§2 中心定理候補、§3 骨格)、
  [n1005](../../docs/note/n1005_aat_semantic_geometry_route_after_g107.md)(§4.3)、
  [n1007](../../docs/note/n1007_aat_sakura_gr4_completion_design.md)(§3 旧義務台帳の
  設計元)、[G-110 カード](G-110-aat-doctrine-fiber-product.md)。
- `research aim`: generated comparison を、可逆な canonical mate と冪等な
  normalization projector に分解する。raw exactness が壊れる場所を projector の
  非自明性で分類する。Karoubi の像と、選んだ reading の上で exactness が回復する
  ことを、有限 witness つきで決める。
- `core tension`: 既証明と未証明の分界にある。canonical mate `α` は同型、cell ごとの
  成分式 `β_c = α_c ≫ E_c`、選択子と `N_P` の成分の対応、replacement に関する
  自然性、finite axis-fold の firing cell で `E_c` が同型でないこと、object 写像
  `n_P` の冪等性、までは証明済み。未証明の核は package 射 `N_P` の冪等性
  `N_P ≫ N_P = N_P` で、`PackageTotalHom.ext` と `SignedExactCoreReadingHom.ext` の
  条件のうち `EquationSystemExactTransport` の `HEq` 一つに帰着する見込みである。
  これが立てば Karoubi の像で `β_c` が可逆になり、立たなければ具体の不成立等式が
  残る。分裂像を package 圏の内部に作ることは no-go の見込みで、定理になれば
  分裂像の置き場は Karoubi の像になる(普遍性までは主張しない)。observable の層
  では、一般の関数に対する `E_c` 不変性の implication は結合律だけの補題で中身が
  なく、AAT の中身は選んだ reading の admissibility field と transport にだけある。
- `rival`: Beck–Chevalley 条件の古典論と、冪等射の分裂の古典論(Karoubi 一般論)。
  差は、diagnostic による選択、admissibility、選んだ reading の分離を (c1)(f)(h) の
  証明の中で実際に使う点に置く((e2) は admissibility を使わない)。
- `claim boundary`: 記号を次で固定する。
  - package と object: `P Q : AATCorePackage U`、射は total category
    `PackageTotalCategory U` の `PackageTotalHom`。`U(h) := h.upper.objectMap`
    (fiber の射 `E_c` では `E_c.1.upper.objectMap`)。`π x := x.configuration`(`P` に
    依存しない)、`s_P c := P.reading.objectReading.object c`、`n_P := canonicalObjectNormalization P
    = s_P ∘ π`、`Fix(n_P) := {x // n_P x = x}`、configuration の核の関係
    `x ≈ y :↔ π x = π y`(`P` に依存しない)。
    `adm : CanonicalObjectNormalizationAdmissible P`、
    `N_P := canonicalObjectNormalizationTotal P adm : P ⟶ P`。
  - 比較射: `input : AuthoredBCDatumSquare U`、`cochain : DefectCochain
    input.toTransportData`、cell `c` は `input.context.Category` の対象で、その
    support package は `P := input.context.supportPackage c.as`。
    `D := authoredSupportDirectRoute input.context`、
    `V := authoredSupportViaBaseRoute input.context`、
    `α := authoredSupportCanonicalMate input.context : D ⟶ V`、
    `β := authoredDiagnosticObjectCollapseComparisonAtCochain input cochain : D ⟶ V`、
    `E_c := authoredViaBaseDiagnosticObjectCollapseComponentAtCochain input cochain c`。
    generated comparison は `cochain := initialRawDefectCochain input.toTransportData`。
    `V_c` の package を `P'_c` と書く。
  - 量化域: (a)(b)(c2)(e2) は任意の `P`(と `adm`)の上で、(e1) は任意の configuration
    の上で言う。(c1)(d)(f)(g)(g2) の cell ごとの主張は任意の `input`、`cochain`、`c` の
    上で言う。(g) の `β` 全体の非同型と (h) は fixture `finiteAxisFoldBCDatumSquare` と
    その generated cochain の上で言い、この fixture を動かさない。carrier `U` は任意
    だが、(g) の fixture theorem、(h)、(g2) の反例では当該 fixture の carrier に固定
    される。係数、law universe、coverage topology、site は動かさない。
  - 語らないもの: operation / invariant の dependent な因子化(後続カード)、G-114
    refinement mate と G-115 upper solution の同型性、localization(`W`-inversion)、
    fiber を貫く global modification `ν`(後続カード)、
    ArchSig の artifact と実装挙動(client route として分離し、AAT 側は observable
    predicate と theorem interface だけを定める)。
- `capability categories`: exactness、decision、counterexample、unification。
- `threshold policy`: SCORE は使わない。runtime state は tracking Issue に置く。
- `portfolio constraint`: 正の定理((d)(f))だけで完了と数えない。(e2) の no-go theorem
  と (h) の witness packet の両方を要求する。(e2) の blocker は checkpoint の事由で
  あって代替ではない。`E_c = 𝟙` となる cell(firing でない、または admissible でない)
  での成立は放電と数えない。
- `phase boundary criteria`: 未証明なら `target-proof-checkpoint`。型付いた fixed
  universal clause に反例 theorem が立てば `target-refuted`。例外は、正負二枝をあらかじめ
  固定した classification clause((g2))の qualified な負枝で、これはその clause の確定
  結果とする。全完了条件と final review を満たした場合だけ `target-theorem-proved`。
- `reward rubric`: `not-applicable (target-theorem mode)`。
- `dullness filter`: 次を弾く。mathlib の Karoubi API を包み直しただけの構成((d) は
  (c1) の theorem を instantiate した系として認め、独立の放電と数えない)。二点半束の
  lax law を単独で数える構成。一般の `q` に対する
  `q ∘ U(E_c) = q ⇒ q ∘ U(β_c) = q ∘ U(α_c)`(結合律だけで出る)を (f) の放電と数える
  構成。`q := π`、`π` との pairing、reading の後合成で (h) の separation を満たす
  構成。gate なしの「`E_c` = transport された `N_P`」(`E_c = 𝟙` の cell で偽)。
  `E_c` の transport field(`equationTransport` の `observableEquiv` / `equationEquiv` /
  `contextEquivalence` / `atomEquiv`)を名前付けするだけの (f)。後続カードの `ν` を
  前提にする構成。
- `frontier`: operation / invariant の dependent descent(`OperationDescentData` /
  `InvariantDescentData` 型の predicate と正負の枝を固定してから)、natural idempotent
  modification と lax projector law、comparator inertia test、`W`-inversion、係数 base
  change。候補の中身は n1008 §4・§6。

- `target theorem`: **Split Configuration Descent and Idempotent Beck–Chevalley
  Exactness**。次の (a)–(h) を Lean で構成または反証する。
  - **(a) configuration descent**(`Type` の水準、任意の `P`): `Fix(n_P) ≃
    AtomConfiguration U`。任意の `Y : Type` と `f : ArchitectureObject U → Y` について
    `f ∘ n_P = f ↔ ∃! f̄, f = f̄ ∘ π`。`ArchitectureObject U / ≈ ≃ AtomConfiguration U`。
    operation と invariant の dependent な因子化は本カードでは扱わない(frontier)。
  - **(b) package idempotence**(任意の `P adm`): total category の射の等式
    `N_P ≫ N_P = N_P`。`PackageTotalHom.ext` と `SignedExactCoreReadingHom.ext` を経由し、
    `EquationSystemExactTransport` の ext 補題と refl-trans の等式を名前付きの artifact
    として残す(後続カードが使う)。object 写像の等式で代替しない。
  - **(c1) projector idempotence**(任意の `input cochain c`): 既証明の
    `β_c = α_c ≫ E_c`、gate 込みの同定(`cochain c = 1` なら `E_c = 𝟙`、firing かつ
    admissible なら `E_c` は `N_P` の成分の transport / provenance iso による像)、
    replacement に関する自然性は、既存 theorem の参照として使う(再証明しない、新規
    放電に数えない)。新しく示すのは `E_c ≫ E_c = E_c` と、`E_c.1.upper.atomEquiv =
    Equiv.refl _`(`N_P` の `atomEquiv` が `Equiv.refl` であることの transport)。
  - **(c2) naturality of `n_P`**(任意の `f : P ⟶ Q`、total category): object 写像の
    水準で `U(f) ∘ n_P = n_Q ∘ U(f)`(`object_formation_eq` と `configuration_eq` から)。
  - **(d) image exactness**: (b)(c1) の theorem を使って、`β_c : (D_c, β_c ≫ inv α_c) ⟶
    (V_c, E_c)` が Karoubi の圏で同型。
  - **(e1) distinct objects lemma**(任意の `U`、任意の configuration `C`): 名前付きの
    補題 `∀ C, ∃ x y : ArchitectureObject U, x ≠ y ∧ π x = C ∧ π y = C`(`StructureMaps`
    の型を変えた装飾で構成する。fixture の `finiteAxisFoldBoolObject` と
    `finiteAxisFoldUnitObject_ne_boolObject` が一例)。
  - **(e2) internal split no-go**(固定した義務、total category、任意の `P Q adm`):
    `r : P ⟶ Q`、`i : Q ⟶ P` について `¬ (i ≫ r = 𝟙 Q ∧ r ≫ i = N_P)`。witness は (e1)
    から取る。(e1) が型不能または偽と判明した場合に限り、人間の判断で witness
    `x ≠ y ∧ π x = π y` を theorem の仮定に置く条件付きの形に改め、その仮定は fixture の
    上で (e1) の例により放電する。`CoreFiber` への制限で代替しない。
  - **(f) observable exactness**(任意の `input cochain c`、`cochain c ≠ 1` かつ `adm` の
    もとで): reading は equation residual と coordinate に限る。`adm` の field はそれ自身が
    `n_P` についての literal な等式である(`equationResidual_eq : ∀ W object index atom,
    residual W object index atom = residual W (n_P object) index atom`、
    `coordinate_eq : ∀ object axis, coordinate object axis = coordinate (n_P object) axis`)。
    示すのは、これを `P'_c` の同じ field と `U(E_c)` に置き換えた同じ形の等式である。
    `∀ W A index atom, P'_c.algebra.equationSystem.equationResidual W (U(E_c) A) index atom
    = P'_c.algebra.equationSystem.equationResidual W A index atom` と
    `∀ A axis, P'_c.reading.signatureReading.coordinate (U(E_c) A) axis =
    P'_c.reading.signatureReading.coordinate A axis`。index / atom / axis は両辺で同じ
    (equivalence 成分を含まない。(c1) の `atomEquiv = Equiv.refl` がこれを許す)。そこから
    同じ形で `residual W (U(β_c) A) index atom = residual W (U(α_c) A) index atom` と
    coordinate の対応式。`E_c = 𝟙` の cell は自明なので別 case とし、放電に数えない。
  - **(g) raw failure locus**: 任意の `input cochain c` で、(c1) の冪等性のもとで
    `IsIso β_c ↔ IsIso E_c ↔ E_c = 𝟙`。fixture `finiteAxisFoldBCDatumSquare` の generated
    comparison について、仮定なしの名前付き theorem
    `¬ IsIso (generatedAuthoredDiagnosticObjectCollapseComparison finiteAxisFoldBCDatumSquare)`
    (firing は `finiteAxisFold_initialRawDefect_second` で放電する)。
  - **(g2) transport identity-reflection classification**(completion に必須。正負二枝を
    あらかじめ固定した classification clause): 対象は、任意の `input cochain c`
    (`P := input.context.supportPackage c.as`)についての一般形
    `E_c = 𝟙 ↔ ¬ (cochain c ≠ 1 ∧ CanonicalObjectNormalizationAdmissible P ∧
    ¬ Function.Injective (canonicalObjectNormalization P))`。正枝: この一般形を theorem
    として証明する(直接、または G-113 `indexedDiagnosticTransportEquivalence` からの
    bridge 付きの導出)。負枝: 具体的な `input cochain c` を固定し、一般形の反例を仮定
    なしの名前付き theorem として証明する(非 identity presentation の fixture が要りうる。
    この枝に限り新 fixture を許す)。どちらの枝も qualified な classification result と
    して (g2) の放電と数える。`Classical.em` / `not_forall` / choice だけで枝を選ぶことは
    認めない。fixture の identity presentation 上では unitor で自明に成り立つので、それ
    だけでは正枝の放電と数えない。どちらの枝でも (g) の cell 水準の同値は変わらない。
  - **(h) witness packet**: fixture `finiteAxisFoldBCDatumSquare`、generated cochain、
    cell `second`、`P := supportPackage second`、reading は equation residual(この fixture
    では coordinate と invariant が object を読まない)に固定し、一本の conjunction
    theorem または structure の中で次を同時に示す。firing(`cochain second ≠ 1`)。
    admissibility(`adm`)。noninjectivity の対 `x₁ x₂`(`x₁ ≠ x₂`、`π x₁ = π x₂`、
    `n_P x₁ = n_P x₂`)。separation の対 `y₁ y₂`(`π y₁ ≠ π y₂` かつ、ある `W index atom` で
    `residual W y₁ index atom ≠ residual W y₂ index atom`)。`E_c ≠ 𝟙`。`¬ IsIso β_c`。(f) の
    literal 等式の `P'_c` での成立。fixture は動かさない。この fixture で成り立たない
    役割があれば failure policy に従う。
- `target theorem boundary`: Lean 置き場所は
  `research/lean/ResearchLean/AG/DoctrineFiberProduct/` 配下の新 module。G-110 / G-113
  の reviewed module は参照のみ。(a) と (f) の `Type` 水準の商と、(d) の圏水準の
  Karoubi は分けて扱い、`Type` の側の商を圏へ戻さない(`coforkReturn_not_isIso_of_ne`
  の障害)。量化域は claim boundary のとおり((g2) の反例 fixture だけ例外)。universe
  は F0 で確定する。
- `target proof artifacts`: (a)–(h) の theorem((g2) は正枝または負枝の theorem)、(b) の
  ext 補題群(名前付き)、(h) の witness packet、旧 O12 の disposition と declaration-level evidence map を含む report
  `research/reports/G-116-aat-idempotent-exchange-structure.md`。
- `target proof strategy`: F0 typing(`n_P` / `N_P` / `E_c` の型分離、ext 補題の
  signature、(f) の literal 等式の形)→ K1 (a)(b) → K2 (c1)(c2)(d) → K3 (e1)(e2) → K4 (f)(g)(g2)
  → K5 (h) と report。既存成果の利用 map: `canonicalObjectNormalization_idempotent`、
  `canonicalObjectNormalizationTotal_proof_irrel`、`ObjectReading.configuration_eq`、
  `SignedExactCoreReadingHom.object_formation_eq` / `configuration_eq`、
  `finiteAxisFoldPermutationTotal_comp`(ext 条件が `rfl` で閉じる前例)、
  `packageTotalHom_objectMap_injective_of_isIso`、
  `authoredDiagnosticObjectCollapseComparisonAtCochain_app`、
  `authoredDiagnosticObjectCollapseComponentAtCochain_eq_id` / `_eq_canonical`、
  `authoredViaBaseDiagnosticObjectCollapseComponentAtCochain_eq_provenance`、
  `generatedAuthoredDiagnosticObjectCollapseComparison_replacement`、
  `finiteAxisFold_initialRawDefect_second`、`finiteAxisFoldUnitObject_ne_boolObject`、
  `authoredViaBaseRawDefectComponent_isIso`(twist は既知の系として数える)、
  mathlib `Idempotents.Karoubi`。選択子の定義に沿う case 分析(`cochain c = 1`、`adm`)は
  許す。
- `target theorem completion criteria`: 全 artifact が sorry なしで `ResearchLean` に
  受理され、axiom / placeholder audit が clean であること。下記 ledger の
  `discharge-required` を放電し、provenance、proof-use、structure-field escape、route
  integrity を監査すること。二段 review gate(各実装 PR の fixed-head `$review-pr`、
  completion candidate での Lean / report / tracking Issue 同期と final review packet、
  独立 `$math-lean-review` 4 査読の全 `No major findings`)を通過すること。(e2)、(g2)、(h)
  を欠いた完了は認めない。Gr4 達成記録は完了条件に含めない。

**旧義務の行き先**:

| 旧義務 | 行き先 |
|---|---|
| O12 universal 枝 | finite axis-fold の firing cell で `E_c` が同型でないことは証明済み(`finiteAxisFold_viaBaseGeneratedObjectCollapseComponent_not_isIso`、前提 `cochain cell ≠ 1`)。`β` 全体の非同型は (g) の仮定なしの名前付き theorem にし、それをもって raw universal `IsIso` の反証として記録する |
| O12 named-failure 枝 | 固定 cell・固定 component・caller 供給の証明書禁止という評価は (g)(h) に残す。結論は上の構造定理に置き換える |
| O12 の G-114 / G-115 成分 | Gr4 を閉じるカードへ |
| O19(Gr4 達成記録、達成階梯対応表) | Gr4 を閉じるカードへ |
| 義務台帳 O1–O20 と、G-113 / G-115 の revision disposition | O19 とともに Gr4 を閉じるカードへ移す。移るまでの所在は改訂前カードの版(blob `be49fdeb2e1d2eeefd76c93aafb75541c02a79a0`)と n1007 §3。各 revision の記録は G-113 / G-115 の tracking Issue(#4204、#4250) |

**旧 O12 の disposition(履歴)**:

| id | 旧義務 | disposition |
|---|---|---|
| O12-r1 | actual mate-bearing sector / active refinement / active upper-stage regime 上で exchange-failure の存否を決定する | O10-r1 の global upper lift が `goal-defect` となり、全 active upper-stage solution 域は供給できなかった。人間承認 revision 2 は G-115 が caller-free に構成する単一の named `upperDecisionSolution` を upper summand へ供給し、O12 はその chosen-solution-relative な `UpperStageExchangeExact` を決定する形になった |
| O12-r3 | raw authored upper problem 全体の comparison を solution equivalence として upper summand へ運ぶ | endpoint cartesianness を持たない raw domain では逆比較を生成できず `goal-defect`。人間承認 revision 4 は raw 片方向 comparison を O12 外へ分類し、generated cartesian-compatible locus の canonical `upperDecisionSolution` だけを upper summand へ供給する形になった |
| O12-r4 | literal G-114 selected endpoint 上の cartesian-compatible solution を upper summand へ供給する | selected endpoint の geometry inverse が構成不能となり、当該 upper summand は未供給。revision 5 は raw selected route との接続を一方向 comparison と core square に限定し、explicit upper equivalence から構成する canonicalized `upperDecisionSolution` だけを O12 へ供給する形になった |
| O12(G-110 成分) | 本カードの (c1)–(h) に置き換える。upper summand の決定は Gr4 を閉じるカードへ |

**declaration-level evidence map**(module は `research/lean/ResearchLean/AG/DoctrineFiberProduct/` 配下):

| 対象 | 宣言 |
|---|---|
| canonical mate `α` と同型性 | `authoredSupportCanonicalMate`、instance `authoredSupportCanonicalMate_isIso`(`BCAuthoredSupportCanonicalMate`) |
| via-base collapse component `E_c` と選択子 | `authoredViaBaseDiagnosticObjectCollapseComponentAtCochain`、`authoredDiagnosticObjectCollapseComponentAtCochain`(`BCAuthoredDiagnosticObjectCollapseProducer`) |
| generated comparison と成分式 | `generatedAuthoredDiagnosticObjectCollapseComparison`、`authoredDiagnosticObjectCollapseComparisonAtCochain_app` |
| replacement naturality | `generatedAuthoredDiagnosticObjectCollapseComparison_replacement`、`mateCoherentRel_replacePresentation_iff` |
| normalization(object 写像・package 射・admissibility) | `canonicalObjectNormalization`、`canonicalObjectNormalizationTotal`、`CanonicalObjectNormalizationAdmissible`(`BCAuthoredCanonicalObjectNormalization`)、`packageTotalHom_objectMap_injective_of_isIso`(`BCAuthoredObjectCollapse`) |
| finite axis-fold witness | `finiteAxisFold_canonicalNormalizationAdmissibleAt`、`finiteAxisFoldCanonicalNormalizationSupportComponent_not_isIso`、`finiteAxisFold_viaBaseGeneratedObjectCollapseComponent_not_isIso`、`finiteAxisFoldBCDatumSquare_not_mateCoherentRel`、`finiteAxisFold_reselectEdges_not_mateCoherentRel`、`finiteAxisFold_replacePresentation_not_mateCoherentRel`(`BCAuthoredDiagnosticObjectCollapseProducerWitnesses`)、`finiteCanonicalObjectNormalizationTotal_not_isIso`、対照例 `auxiliarySensitiveCorePackage_not_admissible`(`BCAuthoredCanonicalObjectNormalizationWitnesses`)、`finiteAxisFold_initialRawDefect_second`(`BCDiagnosticAxisFoldComparisonWitnesses`) |
| twist と cofork の no-go(系として数える根拠) | `authoredViaBaseRawDefectComponent_isIso`(`BCAuthoredComparisonNoGo`)、`finiteAxisFold_viaBaseRawDefect_no_cofork`(`BCAuthoredFixedTargetCoforkNoGoWitnesses`)、`coforkReturn_not_isIso_of_ne`(`BCAuthoredFixedTargetQuotientNoGo`)、`BCAuthoredNonAxisCollapseAudit`(非可逆性が object 写像に住むことの監査) |

- `target premise discharge policy`: 入力(`input`、fixture の `AuthoredBCDatumSquare`
  data)だけを残せる。`cochain` は generated cochain に固定し、fixture の data として
  自由に選ばない。冪等性、同型性、no-go、firing、noninjectivity、separation、reading の
  保存は放電対象であり、結論相当のデータを供給として受けない。
- `target material premise ledger`(`discharge-required` 行の provenance は「入力 data と
  reviewed predecessor theorem から proof term が構成されること」、proof-use は「当該
  field / theorem が proof term に現れること」を要件とする):
  - `G-110 reviewed artifact`: `ambient-boundary`。参照のみ。固定参照 = 完了
    PR #4153(final head `a1471483`、merge `315a2537`)。宣言は上の evidence map。支える
    結論 = (c1) の既証明部分と (h) の fixture。結論相当でない理由 = `E_c` の冪等性、
    Karoubi での同型性、`β` 全体の非同型は既証明 artifact からは従わない。
  - `G-113 reviewed artifact`: `ambient-boundary`。参照のみ。固定参照 = 完了
    PR #4233(head `76e58611`、merge `7083db0d`)。宣言 =
    `indexedDiagnosticTransportEquivalence`(O13)と
    `indexedDiagnosticTransportPush_isEquivalence`(O18)。
    支える結論 = (g2) の正枝の導出候補。結論相当でない理由 = O13・O18 は
    `coreFiberTransportFunctor` 側の equivalence であり、`selectedCoreFiberReindexFunctor`
    との合成への bridge と、`E_c` の恒等性の反映は別に導く必要がある。
  - `finite axis-fold fixture`(`finiteAxisFoldBCDatumSquare`、`finiteAxisFoldSupportPackage`)
    と対照例 fixture(`auxiliarySensitiveCorePackage`): `ambient-boundary`(入力幾何)。
    支える結論 = (h) と非空虚性。結論相当でない理由 = fixture は object と square の
    data であり、非同型・admissibility・分離はいずれも theorem として放電する。
  - `adm : CanonicalObjectNormalizationAdmissible P`: `direction-hypothesis`(選択子の
    gate 条件)。非空虚性 = `auxiliarySensitiveCorePackage_not_admissible`(admissible で
    ない package が実在する)。fixture での放電 =
    `finiteAxisFold_canonicalNormalizationAdmissibleAt`。(f)(h) では対応する field の
    proof-use を要件とする。結論相当でない理由 = admissibility は選んだ reading が
    `n_P` を区別しないことであり、`E_c` の冪等性・非同型性・separation は含まない。
  - `firing : cochain c ≠ 1`: `direction-hypothesis`(cell ごとの主張 (f)(g))。fixture
    では `finiteAxisFold_initialRawDefect_second` で放電し、(g) の名前付き theorem と
    (h) では仮定に置かない。
  - `package idempotence (b)`: `discharge-required`。artifact = ext 補題と
    `N_P ≫ N_P = N_P`、または不成立等式の theorem。
  - `E_c ≫ E_c = E_c`、`atomEquiv = Equiv.refl` (c1) と `n_P` の自然性 (c2):
    `discharge-required`。artifact = 各 theorem。
  - `distinct objects (e1)` と `internal split no-go (e2)`: `discharge-required`。artifact =
    一様補題と no-go theorem。
  - `observable transport (f)`: `discharge-required`。artifact = `adm` の field の
    proof-use と、(f) の literal な等式の theorem。provenance 連鎖
    (`adm.<field>` → `canonicalObjectNormalizationEquationTransport` → `_eq_canonical` /
    `_eq_provenance`)を report に書く。
  - `named ¬ IsIso β (g)` と `witness packet (h)`: `discharge-required`。artifact = 仮定
    なしの fixture theorem と一本の conjunction theorem。
  - `transport identity-reflection classification (g2)`: `discharge-required`。artifact =
    (g2) の正枝または負枝の theorem。結論相当でない理由 = どちらの枝も (g) の cell 水準
    の同値と (h) を変えず、一般形の成否そのものが本カードの結論の一部である。
- `target route integrity gate`: (a)(b)(c2)(e1)(e2) の量化域は `AATCorePackage U`、
  `ArchitectureObject U`、`PackageTotalHom` の全体。(c1)(d)(f)(g)(g2)(h) の量化域は
  `AuthoredBCDatumSquare` の data から組み、cell の package は `input.context.supportPackage c.as`。witness は
  `finiteAxisFoldBCDatumSquare` 系 fixture と対照例 fixture に限る((g2) の反例のみ
  例外)。禁止経路: caller 供給の certificate、`Classical.em` / `not_forall` /
  choice だけによる分岐(選択子の定義に沿う case 分析は可)、mathlib API の包み直し
  による (d) の独立計上、`q := π` や pairing による (h) の放電、gate なしの
  `E_c = transport(N_P)`、`E_c` の transport field の名前付けによる (f) の放電、後続
  カードの `ν` を前提にした (c1)、`E_c = 𝟙` の cell での (f) の放電、fixture の
  `cochain` を firing が成り立つように選ぶこと、(e2) の `CoreFiber` への制限、(h) の
  fixture の差し替え。
- `target anti-weakening rule`: 冪等性、同型性、no-go、firing、noninjectivity、
  separation、reading の保存を theorem argument、typeclass、structure field、certificate
  field へ移して成功扱いしない(一般の `input` の定理で `firing` / `adm` を仮定に置く
  ことは可。fixture の theorem では不可)。`ambient-boundary` に残せるのは入力幾何と
  reviewed predecessor の成果だけである。
- `target failure policy`: fail-closed。証明が得られず具体の blocker(どの field の
  `HEq` か、どの等式か)が report に記録された状態は `target-proof-checkpoint`。同じ
  blocker が二 cycle 続けば `target-blocked`。型付いた fixed universal clause((a)(b)
  (c1)(c2)(d)(e1)(e2)(f)(g)(h))に反例 theorem が立てば `target-refuted`(fixed target の
  改訂は人間の別判断。(e1) が偽なら、(e2) を witness を仮定に置く条件付きの形に改める
  のがその改訂候補)。例外は (g2) の qualified な負枝で、これは (g2) の確定結果とし、
  `target-refuted` にしない。型不能、または指示対象の欠落は `goal-defect` で止め、
  人間の判断で target を改める(F0 の型不能を含む)。GOAL 改訂の提案は tracking Issue
  のコメントに置く。
