# G-117-aat-lax-diagnostic-projector — 冪等 modification ν と診断選択子の lax law

- `id`: `G-117-aat-lax-diagnostic-projector`
- `status`: `draft`
- `priority`: `high`
- `research mode`: `target-theorem`
- `program context`: G-116 後続。G-116 が同定した冪等正規化因子を、admissible fiber を
  貫く一つの自然な対象(idempotent modification `ν`)へ束ね、診断選択子の合成法則を
  lax law として確定する。Gr4 は n1001 §3.5 の定義どおりには成り立たなかったため、
  Gr4 を閉じるカード・達成記録カードは作らない。先行カード(G-111〜G-116)の本文に
  ある「Gr4 を閉じるカード」への言及は完了時点の記録として据え置き、そのうち G-114
  refinement mate と G-115 `upperDecisionSolution` の同型判定は本カードの (i) が
  引き受ける。O19(Gr4 達成記録)と義務台帳 O1–O20 の統合は本カードの責務に含めない
  (台帳の所在は改訂前 G-116 カードの版 blob `be49fdeb` と n1007 §3 のまま)。依存する
  reviewed カード(G-116、G-109、G-113)の statement が改訂された場合は、本カードを
  draft へ差し戻して再固定する。
- `predecessor`: G-116(完遂済み。`N_P` / `E_c` の冪等性、ext 補題群、raw failure
  locus、transport identity-reflection classification、witness packet)、G-109(完遂
  済み。`coreFiberTransportFunctor` / `coreFiberCompositor` / `coreFiberUnitor`)、
  G-113(完遂済み。indexed diagnostic transport equivalence)、G-114 / G-115(完遂
  済み。(i) の決定対象の名前付き宣言)。
- `tracking issue`: 昇格時に起票する。
- `source note`: [n1008](../../docs/note/n1008_aat_idempotent_exchange_structure_program.md)
  (§4.1 義務の骨格、§4.3 三項 coherence、§6.1 一般論との切り分け)、
  [G-116 カード](G-116-aat-idempotent-exchange-structure.md)(記号と既証明の一覧)。
- `research aim`: 診断が生成する冪等正規化を、admissible fiber の上の idempotent
  modification `ν` として構成する。診断選択子 `χ` が defect 群の積を strict には保たず、
  冪等射の順序への lax な作用として合成することを、点ごとの同値と有限 witness で確定
  する。`E_c` が transport された `ν` の成分であることを gate 込みで同定し、G-114 /
  G-115 に残る同型判定を classification として閉じる。
- `core tension`: raw exchange の壊れの源が「可逆な defect 群と不可逆な冪等半束の積の
  不一致」という一般論に尽きるのか、それとも generated orbit が打ち消し対を実際に
  実現して AAT 固有の lax 現象が立つのか。`ν` が base arrow を貫いて自然なら、正規化は
  cell ごとの偶然ではなく fiber 束の大域的な構造になり、「package 圏は冪等完備でなく、
  Karoubi 包絡が configuration 層を付け加える」という読みの最初の判定材料が出る。
- `rival`: 群から冪等射への strict monoid 準同型の一般論(自明なものしかない)、Karoubi
  一般論、pseudofunctor / modification の一般論。差は、`χ` の gate(firing・
  admissibility)を実データ(`rawDefectCochain`)から取ること、`E_c` との同定、
  generated orbit での打ち消しの実現判定、(i) の名前付き決定を証明の中で実際に使う点に
  置く。
- `claim boundary`: 記号を次で固定する。
  - fiber と transport: `X Y : ExtractionInstance U`、`σ : X ⟶ Y`、`CoreFiber X`
    (`CrossStageCoherence/CorePseudofunctor`)、`T_σ := coreFiberTransportFunctor σ`、
    `transportAlong`(`AtomFoundation/Transport`)。
  - normalization: `P : AATCorePackage U`、
    `adm : CanonicalObjectNormalizationAdmissible P`、
    `N_P := canonicalObjectNormalizationTotal P adm`、
    `n_P := canonicalObjectNormalization P`。
  - selector: cell の defect 群は `DefectCochain` の値の型 `PackageFiberAut`。
    `χ_N(g)` は `g = 1` なら `𝟙`、それ以外は `N` を返す写像で、実装の指示対象は
    `authoredDiagnosticObjectCollapseComponentAtCochain` の選択である。順序は
    `e ⪯ f :↔ e ≫ f = e ∧ f ≫ e = e`(同一対象上の冪等射)。
  - 比較射: `input`、`cochain`、cell `c`、`α`、`β`、`E_c` は G-116 カードの claim
    boundary の記号をそのまま使う。
  - (i) の決定対象: `refinementBCMateAt`
    (`DoctrineFiberProduct/RefinementBaseChange/Mate`)と `upperDecisionSolution`
    (`DoctrineFiberProduct/UpperGeometryCompatibleDecisionFixtures`)。評価点
    (configuration / regime / fixture)は F0 で名前付き宣言に固定する。
  - 量化域: (a) は `transportAlong` の定義域の任意の arrow の上で言う。(b)(c)(d) は
    任意の `X Y σ` と admissible な `P` の上で言う。(e) は任意の `input cochain c` の
    上で言う。(f) は cell の defect 群と `N_P` の上で言う(抽象補題は support として
    許すが、放電は実 defect 群・実選択子での instantiation で数える)。(g) は fixture
    `finiteAxisFoldBCDatumSquare` とその generated cochain に固定する。(h) は実際の
    reselection / oriented pasting が生成する cochain の族の上で言う。(i) は F0 で
    固定した名前付き評価点の上で言う。係数、law universe、coverage topology、site は
    動かさない。
  - 語らないもの: comparator inertia と descent class(G-118 候補)、bisimplicial /
    mixed descent、`W`-inversion localization、operation / invariant の dependent
    descent、係数 base change、O19(Gr4 達成記録)、ArchSig の artifact と実装挙動
    (client route として分離し、AAT 側は theorem interface だけを定める)。
- `capability categories`: unification、decision、counterexample、interpretation。
- `threshold policy`: SCORE は使わない。runtime state は tracking Issue に置く。
- `portfolio constraint`: 構成((b)(c)(d)(e))だけで完了と数えない。(f) の strict 破れの
  theorem、(g)(h) の二本の witness lane、(i) の決定のすべてを要求する。抽象の群一般論は
  単独では放電と数えない。
- `phase boundary criteria`: 未証明なら `target-proof-checkpoint`。型付いた fixed
  universal clause に反例 theorem が立てば `target-refuted`。例外は (h)(i) の、
  成り立つ枝と成り立たない枝をあらかじめ固定した classification clause で、どちらの
  枝もその clause の確定結果とする。全完了条件と final review を満たした場合だけ
  `target-theorem-proved`。
- `reward rubric`: `not-applicable (target-theorem mode)`。
- `dullness filter`: 次を弾く。二点半束の lax law を群一般論のまま単独で数える構成
  (実 defect 群・実選択子への instantiation がないもの)。G-109 の pseudofunctor data
  を mathlib の Karoubi 持ち上げ API で包み直しただけの構成。gate なしの `E = ν`
  (firing でない cell で偽)。G-116 の ext 補題・冪等性・classification の再証明や
  repackage(参照のみ許す)。(h) で reverse 宣言(局所 defect `δ = u · φ⁻¹` に対する
  `δ_back = u⁻¹ · φ`)の存在だけをもって打ち消しの実現と数える構成(`δ_back` は
  `δ⁻¹ = φ · u⁻¹` と一般に一致しない)。(i) の同型性を field に持つ structure /
  certificate で受ける構成。
- `frontier`: 「AAT の結論の Morita 形」予想の statement 化(Karoubi 包絡と
  configuration 層)、垂直 strictness の統一定理(n1008 §4.2 Test A)、ordered
  groupoid / partial symmetry(n1008 §6.4)、semantic-analysis hysteresis(n1008
  §6.7)、comparator inertia(G-118 候補)。

- `target theorem`: **Natural Idempotent Modification and Lax Diagnostic Projector
  Theorem**。次の (a)–(i) を Lean で構成、または classification として確定する。
  - **(a) admissibility transport**(任意の `P adm` と `transportAlong` の定義域の
    任意の arrow `f`): `CanonicalObjectNormalizationAdmissible (transportAlong P f)`。
    量化は `transportAlong` 型の transport に限り、一般の `PackageTotalHom` へは
    広げない(像の外の object の reading に制約がなく、運べない)。自然性(G-116
    (c2)、全 hom)と admissibility(transport 限定)の一般性の食い違いは、この構造の
    記述の一部であり、弱化ではない。
  - **(b) admissible fiber**: `CoreFiber X` の admissible な package 上の full
    subcategory `AdmCoreFiber X` と、(a) による `coreFiberTransportFunctor σ` の制限
    `T_σ : AdmCoreFiber X ⥤ AdmCoreFiber Y` の構成。
  - **(c) fiber 内の自然性と冪等性**: `ν_X : 𝟭 (AdmCoreFiber X) ⟶ 𝟭 (AdmCoreFiber X)`、
    `ν_X.app P := N_P`。自然性 field の等式は G-116 の ext 補題群
    (`equationSystemExactTransport_hext`、
    `canonicalObjectNormalizationEquationTransport_comp_heq`、
    `canonicalObjectNormalizationUpper_comp`)へ帰着させる。冪等性
    `ν_X ≫ ν_X = ν_X` は成分ごとに `canonicalObjectNormalizationTotal_comp` を
    instantiate する(再証明しない)。
  - **(d) base arrow との両立**(任意の `σ : X ⟶ Y` と admissible `P`):
    `T_σ.map (ν_X.app P) = ν_Y.app (T_σ.obj P)`。G-109 の `coreFiberCompositor` /
    `coreFiberUnitor` との整合等式を合わせ、`ν` を idempotent modification として
    一本の structure に束ねる。等式は total category の射の等式で言い、`HEq` のまま
    残さない(`HEq` が残る場合は blocker として記録して止まる)。
  - **(e) `E_c` の同定**(任意の `input cochain c`): firing かつ admissible の cell
    で、`E_c` は transport / provenance iso で運ばれた `ν` の成分である(既存
    `_eq_canonical` / `_eq_provenance` の付け替え)。全 cell では gate 込みの
    `E_c = χ(ν)` の形でのみ主張し、gate なしの `E = ν` は主張しない(firing でない
    cell で偽)。fiber ごとの Karoubi completion の上で G-116 (d) の Karoubi iso を
    `ν` の像として再読する系を添える(独立の放電には数えない)。
  - **(f) selector の分類**(cell の defect 群 `G` と `N := N_P` の上):
    - (f1) `N ≫ N = N` と `N ≠ 𝟙` のもとで、点ごとの同値
      `χ_N(g) ≫ χ_N(h) = χ_N(gh) ↔ (g = 1 ∨ h = 1 ∨ gh ≠ 1)`。
    - (f2) `Nontrivial G` と `N ≠ 𝟙` のもとで、`χ_N` は積を保たない((f1) とは別の
      theorem として立てる)。
    - (f3) `⪯` が同一対象上の可換冪等射の順序であることと、すべての `g h` に対する
      lax law `χ_N(g) ≫ χ_N(h) ⪯ χ_N(gh)`。
    - (f4) 二段分解: `χ_N` は指示関数 `G → Bool` と埋め込み `Bool → End` の合成で
      あり、後段が monoid 射であることと `N ≫ N = N`、順序の埋め込みであることと
      `N ≠ 𝟙` が、それぞれ同値である。
    - (f5) 二元の projector 順序では三項の coherence が自動で閉じること(この lax law
      から 3-cocycle 型の残差が出ないことの theorem)。
  - **(g) witness lane 1(raw cochain の側)**: fixture `finiteAxisFoldBCDatumSquare`
    の firing 元 `g`(隣接 swap。`finiteAxisFoldSwapTotal_square` で `g` の二乗は
    恒等)について、`h := g` の自己打ち消し対で `χ(g) ≫ χ(g) = N ≠ 𝟙 = χ(g · g)` を
    評価し、(f1) の破れ条件が実データで満たされることを示す。pointwise の積 cochain
    は `DefectCochain` の型のまま入力にする。fixture は動かさない。
  - **(h) witness lane 2(generated orbit の側)**(成り立つ枝と成り立たない枝を
    あらかじめ固定した classification clause): 成り立つ枝 = 実際の reselection /
    oriented pasting が生成する cochain の族の中に、ある cell で `g ≠ 1`、`h ≠ 1`、
    `g · h = 1` となる対が現れることの構成。成り立たない枝 = 生成される族には
    現れないことの theorem。どちらの枝も qualified な確定結果として (h) の放電と
    数える。reverse 宣言の存在だけでは成り立つ枝の放電と数えない(dullness filter)。
  - **(i) summand 決定**(成り立つ枝と成り立たない枝をあらかじめ固定した
    classification clause、二本):
    - (i1) G-114 の `refinementBCMateAt` を F0 で固定した名前付き評価点で評価した
      成分の `IsIso` の成否。
    - (i2) G-115 の `upperDecisionSolution` の `IsIso` の成否。
    - 可能なら (e) の同定と G-116 の様式(`IsIso ↔ 恒等`、
      `authoredViaBaseDiagnosticObjectCollapseComponentAtCochain_eq_id_iff`)へ帰着
      させ、帰着できない場合は直接の theorem または反例で決める。どちらの枝も
      qualified な確定結果として数える。`Classical.em` / `not_forall` / choice だけで
      枝を選ぶことは認めない。
- `target theorem boundary`: Lean 置き場所は
  `research/lean/ResearchLean/AG/DoctrineFiberProduct/` 配下の新 module(fiber 側の
  構成が必要なら `CrossStageCoherence` 配下も可)。G-116 / G-109 / G-113 / G-114 /
  G-115 の reviewed module は参照のみ。universe、(b) の subcategory の実装形、(d) の
  modification の packaging、(f) の `χ_N` の domain の型、(i) の評価点は F0 で確定
  する。F0 で型不能なら `goal-defect` で止める。量化域は claim boundary のとおり。
- `target proof artifacts`: (a)–(g) の theorem、(h)(i) の classification theorem
  (どちらの枝で確定したかを statement で明示する)、(d) の modification structure、
  declaration-level evidence map と (i) の決定記録を含む report
  `research/reports/G-117-aat-lax-diagnostic-projector.md`。
- `target proof strategy`: F0 typing(`AdmCoreFiber` の実装形、`ν` の型、`χ_N` の
  domain、(i) の評価点)→ K1 (a)(b) → K2 (c)(d) → K3 (e) → K4 (f)(g) → K5 (h)(i) と
  report。既存成果の利用 map: G-116 ext 補題群と
  `canonicalObjectNormalizationTotal_comp`((c))、
  `canonicalObjectNormalization_natural`((a) の経路)、
  `authoredDiagnosticObjectCollapseComponentAtCochain_eq_id` / `_eq_canonical` /
  `authoredViaBaseDiagnosticObjectCollapseComponentAtCochain_eq_provenance`((e))、
  `finiteAxisFoldSwapTotal_square`、`finiteAxisFold_initialRawDefect_second`((g))、
  `finiteAxisFoldPermutationTotal_comp`(thin context で ext 条件が `rfl` で閉じる
  前例)、G-113 `indexedDiagnosticTransportEquivalence` と G-116
  `authoredViaBaseDiagnosticObjectCollapseComponentAtCochain_eq_id_iff`((i) の帰着
  候補)、mathlib `Idempotents.Karoubi`。選択子の定義に沿う case 分析(`cochain c = 1`、
  `adm`)は許す。
- `target theorem completion criteria`: 全 artifact が sorry なしで `ResearchLean` に
  受理され、axiom / placeholder audit が clean であること。下記 ledger の
  `discharge-required` を放電し、provenance、proof-use、structure-field escape、route
  integrity を監査すること。二段 review gate(各実装 PR の fixed-head `$review-pr`、
  completion candidate での Lean / report / tracking Issue 同期と final review packet、
  独立 `$math-lean-review` 4 査読の全 `No major findings`)を通過すること(二段 gate
  の正式な基準 = `target-goal-contract.md`)。(f2)、(g)、(h)、(i) を欠いた完了は
  認めない。
- `target premise discharge policy`: 入力(fixture data、reviewed predecessor の成果)
  だけを残せる。冪等性、自然性、両立等式、strict 破れ、打ち消しの実現、(i) の同型性は
  放電対象であり、結論相当のデータを供給として受けない。
- `target material premise ledger`(`discharge-required` 行の provenance は「入力 data
  と reviewed predecessor theorem から proof term が構成されること」、proof-use は
  「当該 field / theorem が proof term に現れること」を要件とする):
  - `G-116 reviewed artifact`: `ambient-boundary`。参照のみ。固定参照 = 完了 PR
    #4355(fixed head `2d6731df0`、merge `a9f135518`)。宣言 = ext 補題群、
    `canonicalObjectNormalizationTotal_comp`、`E_c` 系、
    `authoredViaBaseDiagnosticObjectCollapseComponentAtCochain_eq_id_iff`、witness
    packet。支える結論 = (c)(e)(g) の既証明部分。結論相当でない理由 = fiber を貫く
    自然性、modification 化、lax law、(h)(i) の決定は G-116 の artifact からは
    従わない。
  - `G-109 reviewed artifact`: `ambient-boundary`。参照のみ。宣言 =
    `coreFiberTransportFunctor`、`coreFiberCompositor`、`coreFiberUnitor`
    (`CrossStageCoherence/CorePseudofunctor` ほか)。支える結論 = (b)(d) の土台。
    結論相当でない理由 = pseudofunctor data は admissible への制限とも `ν` の両立とも
    独立である。
  - `G-113 reviewed artifact`: `ambient-boundary`。参照のみ。宣言 =
    `indexedDiagnosticTransportEquivalence` 系。支える結論 = (i) の帰着候補。結論相当
    でない理由 = equivalence は `refinementBCMateAt` / `upperDecisionSolution` の
    同型性を含まない。
  - `G-114 / G-115 reviewed artifact`: `ambient-boundary`。参照のみ。宣言 =
    `refinementBCMateAt`、`upperDecisionSolution`。支える結論 = (i) の決定対象の
    指示。結論相当でない理由 = 同型性の成否はどちらの完了 artifact にも含まれない
    ((i) はそれを決めるための義務である)。
  - finite axis-fold fixture(`finiteAxisFoldBCDatumSquare` 系)と対照例 fixture
    (`auxiliarySensitiveCorePackage`): `ambient-boundary`(入力幾何)。支える結論 =
    (g) と非空虚性。結論相当でない理由 = fixture は object と square の data であり、
    破れ・打ち消し・非同型はいずれも theorem として放電する。
  - `adm : CanonicalObjectNormalizationAdmissible P`: `direction-hypothesis`(gate
    条件)。非空虚性 = `auxiliarySensitiveCorePackage_not_admissible`。(a) は `adm` を
    仮定でなく結論の側でも扱う(transport 後の admissibility を構成する)。
  - `firing : cochain c ≠ 1`: `direction-hypothesis`((e) の gate)。fixture では
    `finiteAxisFold_initialRawDefect_second` で放電し、(g) では仮定に置かない。
  - `admissibility transport (a)`: `discharge-required`。artifact = transport 保存の
    theorem。
  - `admissible fiber (b)` と `naturality / idempotence (c)`: `discharge-required`。
    artifact = subcategory・制限 functor・`ν_X` の各構成と theorem。
  - `base-arrow compatibility (d)`: `discharge-required`。artifact = 両立等式と
    modification structure。
  - `E_c identification (e)`: `discharge-required`。artifact = gate 込みの同定
    theorem。
  - `selector classification (f)`: `discharge-required`。artifact = (f1)–(f5) の
    theorem(実 defect 群での instantiation を含む)。
  - `witness lane 1 (g)`: `discharge-required`。artifact = fixture 上の評価 theorem。
  - `witness lane 2 (h)` と `summand decisions (i)`: `discharge-required`。artifact =
    classification theorem(どちらの枝かを明示)。
- `target route integrity gate`: 許容経路 = reviewed predecessor の宣言と fixture data
  から proof term を構成すること。禁止経路: caller 供給の certificate、
  `Classical.em` / `not_forall` / choice だけによる枝選択((h)(i) を含む。選択子の
  定義に沿う case 分析は可)、gate なしの `E = ν`、G-116 補題の再証明・repackage に
  よる独立計上、抽象の群一般論の単独計上、(h) の reverse 宣言による代替、(i) の
  同型性を field に持つ structure / typeclass / certificate、fixture の差し替え、
  (d) の等式を `HEq` のまま等式と数えること。
- `target anti-weakening rule`: 冪等性、自然性、両立等式、strict 破れ、打ち消しの
  実現、(i) の同型性を theorem argument、typeclass、structure field、certificate
  field、opaque class membership へ移して成功扱いしない(一般 cell の定理で `firing` /
  `adm` を仮定に置くことは可。fixture の theorem では不可)。`ambient-boundary` に
  残せるのは入力幾何と reviewed predecessor の成果だけである。
- `target failure policy`: fail-closed。証明が得られず具体の blocker(どの field の
  等式か、どの評価点か)が report に記録された状態は `target-proof-checkpoint`。同じ
  blocker が二 cycle 続けば `target-blocked`。型付いた fixed universal clause
  ((a)–(g))に反例 theorem が立てば `target-refuted`(fixed target の改訂は人間の別
  判断。(a) が成り立たなければ、fiber ごとの projector の理論へ縮める改訂が候補)。
  (h)(i) は枝をあらかじめ固定した classification でどちらの枝も確定結果とし、
  `target-refuted` にしない。型不能、指示対象の欠落、(i) の評価点が F0 で一意に固定
  できない場合は `goal-defect` で止め、人間の判断で target を改める。GOAL 改訂の提案
  は tracking Issue のコメントに置く。
