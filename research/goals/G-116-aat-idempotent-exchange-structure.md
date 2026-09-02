# G-116-aat-idempotent-exchange-structure — exchange 反例の背後にある冪等正規化構造

- `id`: `G-116-aat-idempotent-exchange-structure`(旧 id `G-116-aat-gr4-capstone`。
  番号は同じ)
- `status`: `draft`
- `priority`: `high`
- `research mode`: `target-theorem`
- `program context`: Gr4 系列。G-110 の generated comparison が同型にならない
  理由を、比較射に含まれる冪等な正規化因子の数学的な正体として同定する。
  Gr4 達成記録(旧 O19)と、旧 O12 のうち G-114 refinement mate と G-115
  `upperDecisionSolution` の決定は、Gr4 を閉じるカード(別途、番号は先取り
  しない)が担う。本カードは Gr4 の最後のカードではない。
- `predecessor`: G-110(完遂済み。canonical mate の同型性、generated comparison、
  finite axis-fold witness、MateCoherentRel 正負対)、G-113(完遂済み。transport
  equivalence O13・O18。clause (g) の conservativity の供給候補)。
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
  成分式 `β_c = α_c ≫ E_c`、finite axis-fold の firing cell で `E_c` が同型でない
  こと、object 写像 `n_P` の冪等性、までは証明済み。未証明の核は package 射
  `N_P` の冪等性 `N_P ≫ N_P = N_P` で、`SignedExactCoreReadingHom.ext` の 7 条件の
  うち `EquationSystemExactTransport` の `HEq` 一つに帰着する。これが立てば Karoubi
  の像で `β_c` が可逆になり、立たなければ具体の不成立等式が残る。分裂像を package
  圏の内部に作ることは no-go の見込みで、定理になれば Karoubi は意味の像を表す
  最小の完備化になる。observable の層では、一般の関数に対する `E_c` 不変性の
  implication は結合律だけの補題で中身がなく、AAT の中身は選んだ reading の
  admissibility field と transport にだけある。
- `rival`: Beck–Chevalley 条件の古典論と、冪等射の分裂の古典論(Karoubi 一般論)。
  差は、diagnostic による選択、admissibility、選んだ reading の分離を証明の中で
  実際に使う点に置く。
- `claim boundary`: G-110 sector の authored lax square。`input : AuthoredBCDatumSquare U`、
  `cochain : DefectCochain input.toTransportData`、cell `c` は `input.context.Category`
  の対象。`D := authoredSupportDirectRoute input.context`、
  `V := authoredSupportViaBaseRoute input.context`、`α := authoredSupportCanonicalMate
  input.context`、`β := authoredDiagnosticObjectCollapseComparisonAtCochain input cochain`、
  `E_c := authoredViaBaseDiagnosticObjectCollapseComponentAtCochain input cochain c`。
  generated comparison は `cochain := initialRawDefectCochain input.toTransportData`。
  `n_P := canonicalObjectNormalization P`(object 写像)、
  `N_P := canonicalObjectNormalizationTotal P adm`(package 射)、`U(h)` は package 射
  `h` の underlying object 写像。carrier `U` と係数は固定する。語らないもの:
  G-114 refinement mate と G-115 upper solution の同型性、localization
  (`W`-inversion)、fiber を貫く global modification `ν`(後続カード)、
  ArchSig の artifact と実装挙動(client route として分離し、AAT 側は observable
  predicate と theorem interface だけを定める)。
- `capability categories`: exactness、decision、counterexample、unification。
- `threshold policy`: SCORE は使わない。runtime state は tracking Issue に置く。
- `portfolio constraint`: 正の定理(Karoubi、observable)だけで完了と数えない。
  witness packet(下記 (h))と、no-go (e) または具体の blocker のどちらか一方を
  要求する。firing でない cell(`E_c = 𝟙`)での成立は放電と数えない。
- `phase boundary criteria`: 未証明なら `target-proof-checkpoint`、反証なら
  `target-refuted`、全完了条件と final review を満たした場合だけ
  `target-theorem-proved`。
- `reward rubric`: `not-applicable (target-theorem mode)`。
- `dullness filter`: 次を弾く。mathlib の Karoubi API を包み直しただけの構成。
  二点半束の lax law を単独で数える構成。一般の `q` に対する
  `q ∘ U(E_c) = q ⇒ q ∘ U(β_c) = q ∘ U(α_c)`(結合律だけで出る)を observable
  exactness の放電と数える構成。`q := π_P` で separation を満たす構成。gate なしの
  「`E_c` = transport された `N_P`」(firing でない cell で偽)。後続カードの `ν` を
  前提にする構成。
- `frontier`: natural idempotent modification と lax projector law(G-117 候補)、
  comparator inertia test(G-118 候補)、`W`-inversion、係数 base change。候補の
  中身は n1008 §4・§6。

- `target theorem`: **Split Configuration Descent and Idempotent Beck–Chevalley
  Exactness**。次の (a)–(h) を Lean で構成または反証する。
  - **(a) configuration descent**(`Type` の水準): `Fix(n_P) ≃ AtomConfiguration U`、
    `f ∘ n_P = f ↔ ∃! f̄, f = f̄ ∘ π_P`、`ArchitectureObject U / ≈_P ≃ AtomConfiguration U`
    (`x ≈_P y :↔ π_P x = π_P y`)。operation / invariant の dependent な因子化は
    「できる / できない」を決める。
  - **(b) package idempotence**: `N_P ≫ N_P = N_P`。`EquationSystemExactTransport` の
    ext 補題と refl-trans の等式を経由する。落ちた場合は、どの等式が成り立たないかを
    theorem の形で固定する。
  - **(c) factorization**: `β_c = α_c ≫ E_c`(証明済みの再繋留)、`E_c ≫ E_c = E_c`、
    firing かつ admissible の cell で `E_c` が `N_P` の成分を transport / provenance iso で
    運んだものであること(gate 込み)、replacement に関する自然性。
  - **(d) image exactness**: (b)(c) のもとで、`β_c : (D_c, β_c ≫ inv α_c) ⟶ (V_c, E_c)`
    が Karoubi の圏で同型。
  - **(e) internal split no-go**(固定した義務): 任意の `P Q`、
    `adm : CanonicalObjectNormalizationAdmissible P`、`r : P ⟶ Q`、`i : Q ⟶ P` と、
    同じ configuration の上の相異なる二つの `ArchitectureObject` の witness に対して、
    `¬ (i ≫ r = 𝟙 Q ∧ r ≫ i = N_P)`。
  - **(f) observable exactness**: firing かつ admissible の cell で、選んだ reading
    `ρ`(equation residual / operation / invariant / coordinate)について、admissibility
    の対応する field から `ρ ∘ n_P = ρ`、その transport `ρ'` について
    `ρ' ∘ U(E_c) = ρ'`、よって `ρ' ∘ U(β_c) = ρ' ∘ U(α_c)`。firing でない cell は
    `E_c = 𝟙` の別 case とする。
  - **(g) raw failure locus**: cell ごとに `IsIso β_c ↔ IsIso E_c ↔ E_c = 𝟙`。`β` 全体の
    `¬ IsIso` を名前付き theorem にする。「raw で壊れる ⟺ firing ∧ admissible ∧
    正規化が非自明」を cell の外の一般形で言うのに要る transport / reindex の
    conservativity は、「証明 / G-113 O13・O18 からの導出 / 不成立(反例を theorem
    に)」のどれかで決める。
  - **(h) witness packet**: finite axis-fold で carrier / firing / admissibility /
    noninjectivity / selected reading preservation / separation の六役割を備え、
    `q` は実際に選んだ reading に型付けして `q ∘ n_P = q` を admissibility field から
    導き、`E_c ≠ 𝟙`、`¬ IsIso β_c`、reading の保存を同時に示す。
- `target theorem boundary`: Lean 置き場所は `research/lean/ResearchLean/AG/
  DoctrineFiberProduct/` 配下の新 module。G-110 / G-113 の reviewed module は参照のみ。
  (a) と (f) の `Type` 水準の商と、(d) の圏水準の Karoubi は分けて扱い、`Type` の側の
  商を圏へ戻さない(`coforkReturn_not_isIso_of_ne` の障害)。universe は F0 で確定。
- `target proof artifacts`: (a)–(h) の theorem と finite witness packet、旧 O12 の
  disposition と declaration-level evidence map を含む report
  `research/reports/G-116-aat-idempotent-exchange-structure.md`。
- `target proof strategy`: F0 typing(`n_P` / `N_P` / `E_c` の型分離、ext 補題の
  signature)→ K1 (a)(b) → K2 (c)(d) → K3 (e) → K4 (f)(g) → K5 (h) と report。既存
  成果の利用 map: `canonicalObjectNormalization_idempotent`、
  `canonicalObjectNormalizationTotal_proof_irrel`、`ObjectReading.configuration_eq`、
  `SignedExactCoreReadingHom.object_formation_eq` / `configuration_eq`、
  `finiteAxisFoldPermutationTotal_comp`(ext 7 条件が `rfl` で閉じる前例)、
  `authoredDiagnosticObjectCollapseComparisonAtCochain_app`、
  `authoredDiagnosticObjectCollapseComponentAtCochain_eq_canonical`、
  `authoredViaBaseDiagnosticObjectCollapseComponentAtCochain_eq_provenance`、
  `generatedAuthoredDiagnosticObjectCollapseComparison_replacement`、
  `authoredViaBaseRawDefectComponent_isIso`(twist は既知の系として数える)、
  mathlib `Idempotents.Karoubi`。
- `target theorem completion criteria`: 全 artifact が sorry なしで `ResearchLean` に
  受理され、axiom / placeholder audit が clean であること。下記 ledger の
  `discharge-required` を放電し、provenance、proof-use、structure-field escape、route
  integrity を監査すること。二段 review gate(各実装 PR の fixed-head `$review-pr`、
  completion candidate での Lean / report / tracking Issue 同期と final review packet、
  独立 `$math-lean-review` 4 査読の全 `No major findings`)を通過すること。Gr4 達成
  記録は完了条件に含めない。

**旧義務の行き先**:

| 旧義務 | 行き先 |
|---|---|
| O12 universal 枝 | cell 水準では firing cell の `E_c` が同型でないことが証明済み(`finiteAxisFold_viaBaseGeneratedObjectCollapseComponent_not_isIso`、前提 `cochain cell ≠ 1`)。`β` 全体の `¬ IsIso` は (g) で名前付き theorem にし、それをもって raw universal `IsIso` の反証として記録する |
| O12 named-failure 枝 | 固定 cell・固定 component・caller 供給の証明書禁止という評価は (g)(h) に残す。結論は上の構造定理に置き換える |
| O12 の G-114 / G-115 成分 | Gr4 を閉じるカードへ |
| O19(Gr4 達成記録、達成階梯対応表) | Gr4 を閉じるカードへ |
| 義務台帳 O1–O20 と、G-113 / G-115 の revision disposition | O19 とともに Gr4 を閉じるカードへ移す。設計元は n1007 §3、各 revision の記録は G-113 / G-115 の tracking Issue(#4204、#4250) |

**旧 O12 の disposition(履歴)**:

| id | 旧義務 | disposition |
|---|---|---|
| O12-r1〜r4 | actual mate-bearing sector / active refinement / upper-stage regime での exchange-failure の存否決定 | upper-stage 側は G-115 の各 revision で named `upperDecisionSolution` へ縮小した。その成分の決定は Gr4 を閉じるカードへ。G-110 成分は本カードの (c)–(h) に置き換える |

**declaration-level evidence map**:

| 対象 | 宣言 |
|---|---|
| canonical mate `α` と同型性 | `authoredSupportCanonicalMate`(`BCAuthoredSupportCanonicalMate`) |
| via-base collapse component `E_c` と選択子 | `authoredViaBaseDiagnosticObjectCollapseComponentAtCochain`、`authoredDiagnosticObjectCollapseComponentAtCochain`(`BCAuthoredDiagnosticObjectCollapseProducer`) |
| generated comparison と成分式 | `generatedAuthoredDiagnosticObjectCollapseComparison`、`authoredDiagnosticObjectCollapseComparisonAtCochain_app` |
| replacement naturality | `generatedAuthoredDiagnosticObjectCollapseComparison_replacement`、`mateCoherentRel_replacePresentation_iff` |
| normalization(object 写像・package 射・admissibility) | `canonicalObjectNormalization`、`canonicalObjectNormalizationTotal`、`CanonicalObjectNormalizationAdmissible`(`BCAuthoredCanonicalObjectNormalization`) |
| finite axis-fold witness | `finiteAxisFold_canonicalNormalizationAdmissibleAt`、`finiteCanonicalObjectNormalizationTotal_not_isIso`、`finiteAxisFoldCanonicalNormalizationSupportComponent_not_isIso`、`finiteAxisFold_viaBaseGeneratedObjectCollapseComponent_not_isIso`、`finiteAxisFoldBCDatumSquare_not_mateCoherentRel`、`finiteAxisFold_reselectEdges_not_mateCoherentRel`、`finiteAxisFold_replacePresentation_not_mateCoherentRel`、対照例 `auxiliarySensitiveCorePackage_not_admissible` |
| twist と cofork の no-go(系として数える根拠) | `authoredViaBaseRawDefectComponent_isIso`、`finiteAxisFold_viaBaseRawDefect_no_cofork`、`coforkReturn_not_isIso_of_ne` |

- `target premise discharge policy`: 入力(`input`、`cochain`、witness fixture)だけを
  残せる。冪等性、同型性、no-go、reading の保存は放電対象であり、結論相当の
  データを供給として受けない。
- `target material premise ledger`:
  - `G-110 reviewed artifact`: `ambient-boundary`。参照のみ。固定参照 = 完了
    PR #4153(final head `a1471483`、merge `315a2537`)。支える結論 = (c) の既証明
    部分と (h) の fixture。結論相当でない理由 = `E_c` の冪等性、Karoubi での同型性、
    `β` 全体の非同型は既証明 artifact からは従わない。
  - `G-113 reviewed artifact`: `ambient-boundary`。参照のみ。固定参照 = 完了
    PR #4233(head `76e58611`、merge `7083db0d`)。支える結論 = (g) の conservativity の
    導出候補。結論相当でない理由 = O13・O18 は transport の equivalence であり、
    `E_c` の恒等性の反映はそこから別に導く必要がある。
  - `finite axis-fold fixture`: `ambient-boundary`(入力幾何)。支える結論 = (h)。
    結論相当でない理由 = fixture は object と cochain の data であり、非同型・
    admissibility・分離はいずれも theorem として放電する。
  - `package idempotence (b)`: `discharge-required`。artifact = ext 補題と
    `N_P ≫ N_P = N_P`、または不成立等式の theorem。
  - `internal split no-go (e)`: `discharge-required`。artifact = no-go theorem。
    失敗時は下記 failure policy。
  - `observable transport (f)`: `discharge-required`。artifact = 選んだ reading の
    admissibility field の proof-use と、transport 後の不変性の theorem。
  - `named reading witness (h)`: `discharge-required`。artifact = 実際の reading に
    型付けした `q` と separation theorem。
- `target route integrity gate`: 量化域は `AuthoredBCDatumSquare` の data からのみ
  組む。witness は finite axis-fold 系 fixture と対照例 fixture に限る。禁止経路:
  caller 供給の certificate、`Classical.em` / `not_forall` / choice だけによる分岐、
  mathlib API の包み直しによる (d) の放電、`q := π_P` による (h) の放電、gate なしの
  `E_c = transport(N_P)`、後続カードの `ν` を前提にした (c)、firing でない cell での
  (f) の放電。
- `target anti-weakening rule`: 冪等性、同型性、no-go、reading の保存を theorem
  argument、typeclass、structure field、certificate field へ移して成功扱いしない。
  `ambient-boundary` に残せるのは入力幾何と reviewed predecessor の成果だけである。
- `target failure policy`: fail-closed。(b) が落ちた場合は不成立等式を theorem に
  固定して `target-proof-checkpoint` で止め、人間の判断を待つ。(e) が偽・型不能・
  反例のときは成功枝へ移らず `goal-defect` で止め、人間の判断で target を改めてから
  構成 / no-go の二枝に戻す。(g) の conservativity が不成立なら反例を theorem に
  固定し、一般形は主張せず cell 水準の同値に範囲を併記する。F0 で型不能が判明した
  場合も `goal-defect` で止める。fixed target の変更は人間の別判断とする。
