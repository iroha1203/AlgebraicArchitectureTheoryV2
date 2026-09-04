# G-117-aat-lax-diagnostic-projector — 冪等 modification ν と診断選択子の lax law

- `id`: `G-117-aat-lax-diagnostic-projector`
- `status`: `active`
- `priority`: `high`
- `research mode`: `target-theorem`
- `program context`: G-116 後続。G-116 が同定した冪等正規化因子を、admissible fiber を
  貫く一つの自然な対象(idempotent modification `ν`)へ束ね、診断選択子の合成法則を
  lax law として確定する。Gr4 は n1001 §3.5 の定義どおりには成り立たなかったため、
  Gr4 を閉じるカード・達成記録カードは作らない。先行カード(G-111〜G-116)の本文に
  ある「Gr4 を閉じるカード」への言及は完了時点の記録として据え置き、そのうち G-114
  refinement mate と G-115 `upperDecisionSolution` の同型判定は本カードの (i) が
  引き受ける。O19(Gr4 達成記録)と義務台帳 O1–O20 の統合は本カードの責務に含めない
  (台帳の所在は改訂前 G-116 カードの版 blob `be49fdeb` と n1007 §3 のまま)。n1008
  §6.4 の conjugation regime(solution component が同型かで場合分けする読み)の成否の
  入力は、(i2) の決定が与える。依存する reviewed カード(G-106、G-109、G-110、G-113、
  G-114、G-115、G-116)の statement が改訂された場合は、本カードを draft へ差し戻し
  て再固定する。
- `predecessor`: G-116(完遂済み。`N_P` / `E_c` の冪等性、ext 補題群、raw failure
  locus、transport identity-reflection classification、witness packet)、G-109(完遂
  済み。`coreFiberTransportFunctor` / `coreFiberCompositor` / `coreFiberUnitor`)、
  G-110(完遂済み。fixed finite axis-fold fixture と非自明 reselection orbit)、
  G-113(完遂済み。indexed diagnostic transport equivalence)、G-114 / G-115(完遂
  済み。(i) の決定対象の名前付き宣言)。
- `tracking issue`: #4359
- `target revision`: 2026-09-05 の F0 typing で、(h2)(2) の
  `whiskerFiberAut` は fixture の cell 値を `singleDiskLeftPath` /
  `singleDiskRightPath` の始点に置けず型付け不能と確定した。人間の選択により、
  edge reselection が path の終点に生成する `pathReselectionTransition` と
  `rawTwoCellDefect_transition` の合成へ置き換えた。fixture、firing cell、orbit の
  量化域は変更しない。初回4査読で (h2)(1) の単純積が非可換 pasting の定義と一致
  せず、(h2)(3) が恒等 increment で空虚化すると確認されたため、(h2)(1) は canonical
  tail による共役付き再帰式、(h2)(3) は名前付き非恒等 increment と closed
  double-diamond pasting による branch 別の決定へ固定した。
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
  Karoubi 包絡が configuration 層を付け加える」という読み(本カードで立てる仮説)の
  最初の判定材料が出る。
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
    admissible な cell の上で、`χ_N(g)` は `g = 1` なら `𝟙`、それ以外は `N` を返す
    写像である。実装の指示対象は
    `authoredDiagnosticObjectCollapseComponentAtCochain` の選択で、実装は三分岐
    (`g = 1` なら `𝟙`、admissible なら正規化成分、それ以外は `𝟙`)を持ち、二分岐の
    記述は admissible な cell に限って実装と一致する。順序は
    `e ⪯ f :↔ e ≫ f = e ∧ f ≫ e = e`(同一対象上の冪等射。本カードで `⪯` により
    比較する冪等射は互いに可換なもの(`𝟙` と `N`)に限る)。
  - 比較射: `input`、`cochain`、cell `c`、`α`、`β`、`E_c` は G-116 カードの claim
    boundary の記号をそのまま使う。
  - (i) の決定対象: (i1) は評価済み宣言 `activeReverseMateComponent`
    (`RefinementBaseChange/Witnesses`。`refinementBCMateAt` を reviewed 宣言
    `activeReverseConfiguration` / `activeReverseSource` / `activeReverse_condition` /
    `activeReverseTargetPackage` で評価した成分。`refinementBCMateAt` は proof-use /
    unfolding の経路として使う)。非退化性の固定参照 =
    `activeReverse_pulledRefinement_atom_nonidentity`。(i2) は `upperDecisionProblem`
    (`DoctrineFiberProduct/UpperGeometryCompatibleDecisionFixtures`)上の
    `upperDecisionSolution` の vertical component 族
    `upperDecisionSolution.component`。評価点・問題 instance の新設や差し替えは
    認めない(Lean 上の束ね方だけを F0 で確定する)。
  - 量化域: (a) は任意の `P adm` と `transportAlong` の定義域の任意の arrow の上で
    言う。(b)(c)(d) は
    任意の `X Y σ` と admissible な `P` の上で言う。(e) は任意の `input cochain c` の
    上で言う。(f) は cell の defect 群と `N_P` の上で言う。抽象補題は support として
    許すが、放電は実 defect 群・実選択子での instantiation で数え、instantiation は
    fixture の firing cell で行う。実 `N_P` の instantiation では `N ≫ N = N` を
    `canonicalObjectNormalizationTotal_comp` で放電して仮定に残さず、`N_P ≠ 𝟙` と
    `Nontrivial G` は fixture の theorem(下記 ledger)で放電する。前提を仮定に残した
    specialization は (f) の instantiation と数えない。(f1) の instantiation は、
    破れ側(`g * h = 1` で等式が落ちる場合)と成立側(`g * h ≠ 1` で等式が立つ場合)
    の両方の実データ評価を含める。破れ側の評価定理は (g) と同一宣言でよく、その
    場合は report に二重計上である旨を明記する。(g) は fixture
    `finiteAxisFoldBCDatumSquare` とその generated cochain に固定する。(h1) の族は
    reselection orbit の membership 述語 `InReselectionOrbit`(fixture の transport
    data 上、全 `EdgeReselection` の `rawDefectCochain` の像)に固定する。edge
    reselection が path の終点に生成する gauge (`pathReselectionTransition`)と typed
    pasting (`orientedFaceDefect` / `pastingRawDefect`。reselection ごとに face /
    pasting の defect を評価する演算)はいずれも単一 endpoint automorphism を返し、
    族の生成演算に含めず (h2) の propagation の側で扱う(閉包に混ぜて逆元生成を族の
    定義側に埋め込まない)。(i) は上で固定した決定対象の上で言う。係数、law universe、
    coverage topology、site は動かさない。
  - 語らないもの: comparator inertia と descent class(G-118 候補)、bisimplicial /
    mixed descent、`W`-inversion localization、operation / invariant の dependent
    descent、係数 base change、O19(Gr4 達成記録)、ArchSig の artifact と実装挙動
    (client route として分離し、AAT 側は theorem interface だけを定める)。
- `capability categories`: unification、decision、counterexample、interpretation。
- `threshold policy`: SCORE は使わない。runtime state は tracking Issue に置く。
- `portfolio constraint`: 構成((b)(c)(d)(e))だけで完了と数えない。(f) の strict 破れの
  theorem、(g) と (h1)(h2) の witness lane、(i) の決定のすべてを要求する。抽象の群一般論は
  単独では放電と数えない。
- `phase boundary criteria`: 未証明なら `target-proof-checkpoint`。型付いた fixed
  universal clause に反例 theorem が立てば `target-refuted`。例外は (h1)(i) の、
  成り立つ枝と成り立たない枝をあらかじめ固定した classification clause で、どちらの
  枝もその clause の確定結果とする。全完了条件と final review を満たした場合だけ
  `target-theorem-proved`。
- `reward rubric`: `not-applicable (target-theorem mode)`。
- `dullness filter`: 次を弾く。二点半束の lax law を群一般論のまま単独で数える構成
  (実 defect 群・実選択子への instantiation がないもの)。G-109 の pseudofunctor data
  を mathlib の Karoubi 持ち上げ API で包み直しただけの構成。gate なしの `E = ν`
  (firing でない cell で偽)。G-116 の ext 補題・冪等性・classification の再証明や
  repackage(参照のみ許す)。(h1) で reverse 宣言(局所 defect `δ = u · φ⁻¹` に対する
  `δ_back = u⁻¹ · φ`)の存在だけをもって打ち消しの実現と数える構成(`δ_back` は
  `δ⁻¹ = φ · u⁻¹` と一般に一致しない)。(h1) で、自己打ち消し対(`q₁ c = q₂ c`。
  (g) と同じ対、その共役や gauge 移動を含む)をもって成り立つ枝の放電と数える構成。
  (h2) の propagation 等式だけをもって (h1) の放電と数える構成。(h2) で
  `pathReselectionTransition_singleEdge` / `_mul`、`rawTwoCellDefect_transition` /
  `rawDefectCochain_transition` を再輸出または fixture に specialization しただけで、
  二本の endpoint gauge の計算と orbit 値の変換式を一つの theorem に接続しない構成。
  (h2)(1) を一面 pasting の定義展開だけで閉じる構成。(h2)(3) で恒等 increment を選ぶ
  構成、または一面の `doubleDiamondPasting` だけを評価して closed double-diamond の
  二経路比較を使わない構成。(g) の statement の
  `g · g` を literal な
  `1` に置き換えた形(群水準の square 等式の proof-use を要件とする)。(i) で、mate
  成分や component が identity presentation / unitor により定義的に恒等となる評価点の
  成立だけをもって成り立つ枝の放電と数える構成。(i) の同型性を field に持つ
  structure / typeclass / certificate で受ける構成。
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
    記述の一部であり、弱化ではない。admissibility の各 field(equationResidual /
    coordinate / operation type / operation naturality / invariant)ごとに、使用する
    transport lemma と dependent cast / `HEq` の処理を F0 の artifact として記録
    する。
  - **(b) admissible fiber**: `CoreFiber X` の admissible な package 上の full
    subcategory `AdmCoreFiber X` と、(a) による `coreFiberTransportFunctor σ` の制限
    `T_σ : AdmCoreFiber X ⥤ AdmCoreFiber Y` の構成。
  - **(c) fiber 内の自然性と冪等性**: `ν_X : 𝟭 (AdmCoreFiber X) ⟶ 𝟭 (AdmCoreFiber X)`、
    `ν_X.app P := N_P`。自然性は object 写像の水準では
    `canonicalObjectNormalization_natural` を使い、残る field の等式は
    `PackageTotalHom.ext` / `SignedExactCoreReadingHom.ext` と
    `equationSystemExactTransport_hext` へ帰着させる。冪等性 `ν_X ≫ ν_X = ν_X` は
    成分ごとに `canonicalObjectNormalizationTotal_comp`(下請けの
    `canonicalObjectNormalizationEquationTransport_comp_heq` /
    `canonicalObjectNormalizationUpper_comp` を含む)を instantiate する(再証明
    しない)。等式が thin context の定義的簡約で閉じた場合も named theorem として
    成果に数え、その旨を report に明記する。
  - **(d) base arrow との両立**(任意の `σ : X ⟶ Y` と admissible `P`):
    `T_σ.map (ν_X.app P) = ν_Y.app (T_σ.obj P)`。idempotent modification として
    最低限含む法則をカードで固定する: 各 fiber の `ν_X`((c))、base-arrow 両立
    (この等式)、unitor 両立(`coreFiberUnitor` との整合)、compositor 両立
    (`coreFiberCompositor` との整合)、冪等性((c))。Lean 上の packaging は F0 で
    確定する。等式は total category の射の等式で言い、`HEq` のまま残さない(`HEq`
    が残る場合は blocker として記録して止まる)。等式が定義的簡約で閉じた場合も
    named theorem として成果に数え、report に明記する。
  - **(e) `E_c` の同定**(任意の `input cochain c`): firing かつ admissible の cell
    で、`E_c` は transport / provenance iso で運ばれた `ν` の成分である(既存
    `_eq_canonical` / `_eq_provenance` の付け替え)。全 cell の式は選択子の三分岐に
    一致させる: `cochain c = 1` なら `𝟙`、firing かつ admissible なら transport
    された `ν` の成分、firing かつ非 admissible なら `𝟙`。gate は firing と
    admissibility の両方を含む。`ν` の成分の指示は (b) の `T_σ` と (d) の
    modification data による像として書き、G-116 の provenance 経路はその橋渡しと
    してのみ使う(`E_c` の定義を経由して `ν` の成分を定義しない)。同定の正確な形
    は F0 で確定する。gate なしの `E = ν` は主張しない(firing でない cell で偽)。
    fiber ごとの Karoubi completion の上で G-116 (d) の Karoubi iso を `ν` の像と
    して再読する系を添える(独立の放電には数えない)。
  - **(f) selector の分類**(cell の defect 群 `G` と `N := N_P` の上):
    - (f1) `N ≫ N = N` と `N ≠ 𝟙` のもとで、点ごとの同値
      `χ_N(g) ≫ χ_N(h) = χ_N(gh) ↔ (g = 1 ∨ h = 1 ∨ gh ≠ 1)`。
    - (f2) `N ≫ N = N`、`Nontrivial G`、`N ≠ 𝟙` のもとで、`χ_N` は積を保たない
      ((f1) とは別の theorem として立てる)。
    - (f3) `⪯` が同一対象上の可換冪等射の順序であることと、すべての `g h` に対する
      lax law `χ_N(g) ≫ χ_N(h) ⪯ χ_N(gh)`。
    - (f4) 二段分解(固定形): 指示関数 `b : G → Bool` は `b g = true ↔ g = 1`。
      `Bool` 側は積 `&&`・単位 `true`・順序 `false ≤ true` で読む。埋め込みは
      `ι_N(true) = 𝟙`、`ι_N(false) = N`。順序の主張と `χ_N` の packaging では余域を
      二点 subtype `{𝟙, N}` に固定する(`N = 𝟙` の退化は各同値の否定側が引き受け
      る)。`χ_N = ι_N ∘ b`。示すのは、`b` が lax monoid map であること
      (`b g && b h ≤ b (g * h)`)、`ι_N` が積を保つこと(`∀ x y, ι_N (x && y) =
      ι_N x ≫ ι_N y`。endomorphism の等式として言う)と `N ≫ N = N` の同値、および
      `N ≫ N = N` のもとで `ι_N` が順序埋め込みであることと `N ≠ 𝟙` の同値(仮定を
      置かない形では右辺は `N ≫ N = N ∧ N ≠ 𝟙`。順序埋め込みの `(false, false)` 対
      が `N ⪯ N` すなわち `N ≫ N = N` を要求するため)。
    - (f5) 二元の projector 順序では三項の coherence が自動で閉じること。statement は
      「三項合成の両括弧づけの `⪯` 導出の値の一致」と「`⪯` の比較が Prop 値(thin)
      であることの明示」に型を固定し、この lax law から 3-cocycle 型の残差が出ない
      ことを結論として書く。主張の射程は二点 projector 順序への像が Prop 値である
      範囲に限る(G-118 / G-119 候補の mixed descent の残差についての主張では
      ない)。
  - **(g) witness lane 1(raw cochain の側)**: fixture `finiteAxisFoldBCDatumSquare`
    の firing 元 `g`(隣接 swap。`finiteAxisFoldSwapTotal_square` で `g` の二乗は
    恒等)について、`h := g` の自己打ち消し対で `χ(g) ≫ χ(g) = N ≠ 𝟙 = χ(g · g)` を
    評価し、(f1) の破れ条件が実データで満たされることを示す。proof term は (f1) の
    実 instantiation と、群水準の square 等式(`finiteAxisFoldSwapTotal_square` から
    の持ち上げ)を実使用する(proof-use)。statement の `g · g` を literal な `1` に
    置き換えない。pointwise の積 cochain は `DefectCochain` の型のまま入力にする。
    fixture は動かさない。
  - **(h) witness lane 2(generated orbit の側)**: 二段に分ける。
    - (h1) actual reselection orbit(成り立つ枝と成り立たない枝をあらかじめ固定した
      classification clause): 量化域は claim boundary で固定した reselection orbit
      (`InReselectionOrbit`)、cell は firing cell(`DoubleDiamondTwoCell.second`)
      に固定する。成り立つ枝 = orbit に属する `q₁ q₂ : DefectCochain` で、
      `q₁ c ≠ 1`、`q₂ c ≠ 1`、`q₁ c ≠ q₂ c`、`q₁ c * q₂ c = 1` を満たす対の構成。
      少なくとも一方は `initialRawDefectCochain` と異なり、生成した
      `EdgeReselection` を witness に含める。成り立たない枝 = この orbit に
      `q₁ c ≠ q₂ c` を満たすそのような対が存在しないことの theorem。どちらの枝も
      qualified な確定結果として (h1) の放電と数える。自己打ち消し対
      (`q₁ c = q₂ c`。(g) と同じ対、その共役や gauge 移動を含む)と reverse 宣言の
      存在だけでは、成り立つ枝の放電と数えない(dullness filter)。orbit の firing
      cell の値は defect 群を広く掃くので、相異なる相互逆元の対を実際の二つの
      reselection で構成できる見込みが高い。この条項は帰趨を開くためではなく、その
      構成を実データで要求するためにある。
    - (h2) propagation: (h1) の量化域の orbit 値が、edge reselection が left / right
      path の終点に生成する gauge (`pathReselectionTransition`)と typed pasting
      (`orientedFaceDefect` / `pastingRawDefect`)によりどう変換されるかの theorem。
      最低限次を含む: (1) 任意の reselection と任意の
      `RewritePasting`(長さ任意)に対する共役付き再帰式。nil pasting の raw defect は
      `1` とし、`pasting = .cons step tail` では
      `pastingRawDefect data reselection pasting` を
      `pastingRawDefect data reselection tail *
      (canonicalPastingComparator data reselection tail *
      orientedFaceDefect data reselection step.face *
      (canonicalPastingComparator data reselection tail)⁻¹)` と同定する。これにより
      canonical comparison factors を保った ordered product を固定し、局所 raw defect
      の単純積や可換化へ置き換えない。(2) fixture
      `data := finiteAxisFoldBCDatumSquare.toTransportData`、firing cell
      `c := DoubleDiamondTwoCell.second` とし、その
      `twoLeft c` / `twoRight c`(定義上 `singleDiskLeftPath` /
      `singleDiskRightPath`)について、`current increment : EdgeReselection` が生成する
      二本の `pathReselectionTransition` を明示的に計算し、その二式を
      `rawTwoCellDefect_transition` に代入して
      `rawDefectCochain data (increment * current) c` を
      `rawDefectCochain data current c` の left / right endpoint gauge 作用として表す
      等式。(3) 追加 reselection は既存の
      `finiteAxisFoldSecondFaceReselection` に固定し、その EdgeReselection としての
      非恒等性、baseline から firing-cell raw cochain を実際に変えること、二本の
      endpoint gauge、(2) の raw defect 変換を同じ theorem family で証明する。さらに
      `.first` の forward step と `.second` の backward step をこの順に合成した長さ2の
      named `RewritePasting` を fixed double diamond 上に構成する。その raw defect を
      (1) の非自明な cons case を proof term で使って baseline / shifted coordinate で
      評価し、値が保存されるか壊れるかを決定する。あわせて
      `DoubleDiamondThreeCell.comparison` の二つの一面 pasting を比較する
      `closedPastingRawObstruction` も同じ二座標で評価し、その値が保存されるか壊れるかを
      決定する。
      (h1) の成り立つ枝では、その二つの witness reselection `r₁ r₂` にも同じ固定
      increment を左から作用させ、変換後の
      `rawDefectCochain data (finiteAxisFoldSecondFaceReselection * r₁) c *
      rawDefectCochain data (finiteAxisFoldSecondFaceReselection * r₂) c` が `1` か否かを
      等式または反例で決定する。(h1) の成り立たない枝でも、上記の非恒等性、raw
      cochain の実変化、closed-pasting の決定は必須とする。
      `pathReselectionTransition_singleEdge` / `_mul`、`rawTwoCellDefect_transition` /
      `rawDefectCochain_transition`、既存 pasting 補題の再輸出・specialization だけでは
      放電と数えない。二本の endpoint gauge の計算、raw defect の変換、長さ2 pasting、
      二経路の closed obstruction を同じ fixed fixture 上で接続する。
      (h2) の propagation 等式だけでは (h1) の放電と数えない。
  - **(i) summand 決定**(成り立つ枝と成り立たない枝をあらかじめ固定した
    classification clause、二本):
    - (i1) `IsIso activeReverseMateComponent` の成否。`refinementBCMateAt` は
      proof-use / unfolding の経路として使い、評価点の新設は認めない。
    - (i2) `upperDecisionProblem` 上の `upperDecisionSolution` について
      `∀ i, IsIso (upperDecisionSolution.component i)` の成否(成り立たない枝は
      その否定と witness vertex)。問題の presentation の Vertex は単元なので実質は
      一成分の判定である。非退化性の固定参照 = `authored_comparator_ne_one` と
      `source_edge_ne_identity`。成り立つ枝が定義的簡約のみで閉じた場合は、非退化
      参照の proof-use を添えた named theorem として計上し、report に明記する。
      問題 instance は差し替えない。この形が型不能なら `goal-defect` で止める。
    - 可能なら (e) の同定と G-116 の様式(`IsIso ↔ 恒等`、
      `authoredViaBaseDiagnosticObjectCollapseComponentAtCochain_eq_id_iff`)へ帰着
      させ、帰着できない場合は直接の theorem または反例で決める。どちらの枝も
      qualified な確定結果として数える。`Classical.em` / `not_forall` / choice だけで
      枝を選ぶことは認めない。identity presentation / unitor による定義的成立だけでは
      成り立つ枝の放電と数えない(dullness filter)。
- `target theorem boundary`: Lean 置き場所は
  `research/lean/ResearchLean/AG/DoctrineFiberProduct/` 配下の新 module(fiber 側の
  構成が必要なら `CrossStageCoherence` 配下も可)。G-116 / G-109 / G-113 / G-114 /
  G-115 / G-110 の reviewed module は参照のみ。F0 で確定するのは universe、(a) の field 別
  transport artifact の一覧、(b) の subcategory の実装形、(d) の modification の
  packaging、(e) の gate 込み同定の正確な形、(f) の `χ_N` の domain の型と余域二点
  subtype の実装形、(h2) の propagation statement の形((h2) の最低限の内容はカード
  固定)、(i) の評価点の Lean 上の束ね方である。帰趨を左右する選択((h1) の族 =
  `InReselectionOrbit` と firing cell 固定、(i) の評価点・問題 instance・判定射)は
  claim boundary と target theorem で固定済みであり、F0 で変更しない。F0 で型不能
  なら `goal-defect` で止める。量化域は claim boundary のとおり。
- `target proof artifacts`: (a)–(g) の theorem、(h1)(i) の classification theorem
  (どちらの枝で確定したかを statement で明示する)、(h2) の propagation theorem、
  (d) の modification structure、
  declaration-level evidence map と (i) の決定記録を含む report
  `research/reports/G-117-aat-lax-diagnostic-projector.md`。
- `target proof strategy`: F0 typing(universe、(a) の field 別 transport
  artifact、`AdmCoreFiber` の実装形、(d) の `ν` の modification packaging、(e) の
  同定の形、`χ_N` の domain と余域 subtype の実装形、(h2) の propagation statement、
  (i) の評価点の束ね方)→
  K1 (a)(b) → K2 (c)(d) → K3 (e) → K4 (f)(g) → K5 (h)(i) と
  report。既存成果の利用 map: G-116 ext 補題群と
  `canonicalObjectNormalizationTotal_comp`((c))、
  `canonicalObjectNormalization_natural`((a) の経路)、
  `authoredDiagnosticObjectCollapseComponentAtCochain_eq_id` / `_eq_canonical` /
  `authoredViaBaseDiagnosticObjectCollapseComponentAtCochain_eq_provenance`((e))、
  `finiteAxisFoldSwapTotal_square`、`finiteAxisFold_initialRawDefect_second`((g))、
  `finiteAxisFoldPermutationTotal_comp`(thin context で ext 条件が `rfl` で閉じる
  前例)、G-106 `pathReselectionTransition_fac` / `_singleEdge` / `_mul`、
  `rawTwoCellDefect_transition` / `rawDefectCochain_transition`、
  `canonicalPastingComparator`、`closedPastingRawObstruction`((h2))、G-110
  `finiteAxisFoldSecondFaceReselection` / `finiteAxisFold_shiftedCochain_ne_initial`
  ((h2) の fixed nonidentity action)、G-113 `indexedDiagnosticTransportEquivalence` と G-116
  `authoredViaBaseDiagnosticObjectCollapseComponentAtCochain_eq_id_iff`((i) の帰着
  候補)、mathlib `Idempotents.Karoubi`。選択子の定義に沿う case 分析(`cochain c = 1`、
  `adm`)は許す。
- `target theorem completion criteria`: 全 artifact が sorry なしで `ResearchLean` に
  受理され、axiom / placeholder audit が clean であること。下記 ledger の
  `discharge-required` を放電し、provenance、proof-use、structure-field escape、route
  integrity を監査すること。二段 review gate(各実装 PR の fixed-head `$review-pr`、
  completion candidate での Lean / report / tracking Issue 同期と final review packet、
  独立 `$math-lean-review` 4 査読の全 `No major findings`)を通過すること(二段 gate
  の正式な基準 = `target-goal-contract.md`)。(f2)、(g)、(h1)、(h2)、(i) を欠いた
  完了は認めない。
- `target premise discharge policy`: 入力(fixture data、reviewed predecessor の成果)
  だけを残せる。冪等性、自然性、(a) の admissibility 保存、両立等式、strict 破れ、
  打ち消しの実現、(i) の同型性は放電対象であり、結論相当のデータを供給として
  受けない。
- `target material premise ledger`(`discharge-required` 行の provenance は「入力 data
  と reviewed predecessor theorem から proof term が構成されること」、proof-use は
  「当該 field / theorem が proof term に現れること」を要件とする):
  - `G-116 reviewed artifact`: `ambient-boundary`。参照のみ。固定参照 = 完了 PR
    #4355(fixed head `2d6731df0`、merge `a9f135518`)。宣言 = ext 補題群、
    `canonicalObjectNormalizationTotal_comp`、`E_c` 系、
    `authoredViaBaseDiagnosticObjectCollapseComponentAtCochain_eq_id_iff`、witness
    packet。支える結論 = (c)(e)(g) の既証明部分。結論相当でない理由 = fiber を貫く
    自然性、modification 化、lax law、(h1)(i) の決定と (h2) の propagation は G-116
    の artifact からは従わない。
  - `G-106 / transport-coherence reviewed artifact`: `ambient-boundary`。参照のみ。
    固定参照 = 完了同期 PR #4009(final reviewed head `d7b1d488`、merge
    `ae1ba0ea`)。宣言 = `InReselectionOrbit`、`EdgeReselection`、
    `rawDefectCochain`、`initialRawDefectCochain`、`pathReselectionTransition`(+`_fac` /
    `_singleEdge` / `_mul`)、`rawTwoCellDefect_transition` /
    `rawDefectCochain_transition`、`orientedFaceDefect`、`pastingRawDefect`、
    `canonicalPastingComparator`、`RewritePasting`、`doubleDiamondPasting`、
    `closedPastingRawObstruction`、`DoubleDiamondThreeCell.comparison`、
    `DoubleDiamondTwoCell`、`singleDiskLeftPath` / `singleDiskRightPath`
    (`TransportCoherence` 配下)。支える結論 = (h1) の量化域と (h2) の propagation の
    指示対象。結論相当でない理由 = これらは orbit の membership と transport の定義
    または一般変換則と名前付き入力であり、打ち消し対の存否、fixed fixture 上の二本の
    endpoint gauge 計算、orbit 値の変換、共役付き再帰、fixed nonidentity action、
    closed-pasting の二経路比較はいずれも新しい theorem として放電する。
  - `G-110 / finite axis-fold orbit reviewed artifact`: `ambient-boundary`。参照のみ。
    固定参照 = 完了 PR #4153(final head `a1471483`、merge `315a2537`)。宣言 =
    `finiteAxisFoldBCDatumSquare`、`finiteAxisFoldSecondFaceReselection`、
    `finiteAxisFoldSwap_ne_one`、`finiteAxisFold_shiftedCochain_ne_initial`、
    `finiteAxisFold_reselectionOrbit_nontrivial`。支える結論 = (g)(h) の fixed fixture と
    (h2)(3) の名前付き作用。結論相当でない理由 = EdgeReselection としての非恒等性、
    endpoint gauge、raw defect 変換、closed-pasting の baseline / shifted 決定、(h1) の
    witness pair への作用は G-110 の artifact からは従わない。
  - `G-109 reviewed artifact`: `ambient-boundary`。参照のみ。固定参照 = 完了 PR
    #4029(final reviewed head `b5ca4630`、merge `faaf7160`)。宣言 =
    `coreFiberTransportFunctor`、`coreFiberCompositor`、`coreFiberUnitor`
    (`CrossStageCoherence/CorePseudofunctor` ほか)。支える結論 = (b)(d) の土台。
    結論相当でない理由 = pseudofunctor data は admissible への制限とも `ν` の両立とも
    独立である。
  - `G-113 reviewed artifact`: `ambient-boundary`。参照のみ。固定参照 = 完了 PR
    #4233(head `76e58611`、merge `7083db0d`)。宣言 =
    `indexedDiagnosticTransportEquivalence` 系。支える結論 = (i) の帰着候補。結論相当
    でない理由 = equivalence は `refinementBCMateAt` / `upperDecisionSolution` の
    同型性を含まない。
  - `G-114 / G-115 reviewed artifact`: `ambient-boundary`。参照のみ。固定参照 =
    G-114 完了 PR #4246(fixed head `8f7ad8bf`、merge `3d26d993`)、G-115 完了 PR
    #4338(fixed head `1e95d8ff`、merge `cbae0b2e5`)。宣言 = `refinementBCMateAt`、
    `activeReverseConfiguration` / `activeReverseSource` / `activeReverse_condition` /
    `activeReverseTargetPackage`、`activeReverseMateComponent`、
    `activeReverse_pulledRefinement_atom_nonidentity`、
    `upperDecisionProblem`、`upperDecisionSolution`、`authored_comparator_ne_one`、
    `source_edge_ne_identity`。支える結論 = (i) の決定対象の
    指示。結論相当でない理由 = 同型性の成否はどちらの完了 artifact にも含まれない
    ((i) はそれを決めるための義務である)。
  - finite axis-fold fixture(`finiteAxisFoldBCDatumSquare` 系)と対照例 fixture
    (`auxiliarySensitiveCorePackage`): `ambient-boundary`(入力幾何)。支える結論 =
    (g) と非空虚性。結論相当でない理由 = fixture は object と square の data であり、
    破れ・打ち消し・非同型はいずれも theorem として放電する。
  - `adm : CanonicalObjectNormalizationAdmissible P`: `direction-hypothesis`(gate
    条件)。非空虚性 = `auxiliarySensitiveCorePackage_not_admissible`。fixture では
    `finiteAxisFold_canonicalNormalizationAdmissibleAt` で放電し、(g) では仮定に
    置かない。(a) は `adm` を仮定でなく結論の側でも扱う(transport 後の
    admissibility を構成する)。
  - `firing : cochain c ≠ 1`: `direction-hypothesis`((e) の gate)。fixture では
    `finiteAxisFold_generatedCochain_second_ne_one`(内部で
    `finiteAxisFold_initialRawDefect_second` と `finiteAxisFoldSwap_ne_one` を使う)
    で放電し、(g) では仮定に置かない。
  - `admissibility transport (a)`: `discharge-required`。artifact = transport 保存の
    theorem。
  - `admissible fiber (b)` と `naturality / idempotence (c)`: `discharge-required`。
    artifact = subcategory・制限 functor・`ν_X` の各構成と theorem。
  - `base-arrow compatibility (d)`: `discharge-required`。artifact = 両立等式と
    modification structure。
  - `E_c identification (e)`: `discharge-required`。artifact = gate 込みの同定
    theorem。
  - `selector classification (f)`: `discharge-required`。artifact = (f1)–(f5) の
    theorem(実 defect 群・実選択子での instantiation を含む)。
  - `N_P ≠ 𝟙`(fixture): `discharge-required`。artifact =
    `finiteCanonicalObjectNormalizationTotal_not_isIso` から導く named theorem
    (恒等射は同型なので、非同型から従う)。
  - `Nontrivial`(fixture の defect 群): `discharge-required`。artifact = swap 元の
    非自明性の named theorem(`finiteAxisFold_generatedCochain_second_ne_one` から
    導く)。
  - `witness lane 1 (g)`: `discharge-required`。artifact = fixture 上の評価 theorem
    ((f1) の実 instantiation と群水準の square 等式の proof-use を含む)。
  - `witness lane 2 (h1)(h2)` と `summand decisions (i)`: `discharge-required`。
    artifact = (h1)(i) は classification theorem(どちらの枝かを明示)、(h2) は
    transport theorem。
- `target route integrity gate`: 許容経路 = reviewed predecessor の宣言と fixture data
  から proof term を構成すること。禁止経路: caller 供給の certificate、
  `Classical.em` / `not_forall` / choice だけによる枝選択((h1)(i) を含む。選択子の
  定義に沿う case 分析は可)、gate なしの `E = ν`、G-116 補題の再証明・repackage に
  よる独立計上、抽象の群一般論の単独計上、(h1) の reverse 宣言による代替、(h1) の族
  の入力 datum の差し替えと `InReselectionOrbit` 以外への族の拡大・縮小
  (`pathReselectionTransition` / pasting を族の閉包に混ぜることを含む)、(i) の評価点・問題 instance の新設と
  差し替え、(i) の同型性を field に持つ structure / typeclass / certificate、
  fixture の差し替え、(d) の等式を `HEq` のまま等式と数えること。
- `target anti-weakening rule`: 冪等性、自然性、(a) の admissibility 保存、両立
  等式、strict 破れ、打ち消しの実現、(i) の同型性を theorem argument、typeclass、
  structure field、certificate field、opaque class membership へ移して成功扱い
  しない。一般 cell / 抽象 selector の定理で `firing` / `adm` / `N ≫ N = N` /
  `N ≠ 𝟙` / `Nontrivial G` を仮定に置くことは可、fixture の theorem では不可。
  (d) の modification structure は、field を証明で埋めた instance の構成が義務の
  放電であり、当該 structure を仮定・引数として受けることが禁止経路である。
  `ambient-boundary` に残せるのは入力幾何と reviewed predecessor の成果だけで
  ある。
- `target failure policy`: fail-closed。証明が得られず具体の blocker(どの field の
  等式か、どの評価点か)が report に記録された状態は `target-proof-checkpoint`。同じ
  blocker が二 cycle 続けば `target-blocked`。型付いた fixed universal clause
  ((a)–(g))に反例 theorem が立てば `target-refuted`(fixed target の改訂は人間の別
  判断。(a) または (d) が成り立たなければ、fiber ごとの projector の理論へ縮める
  改訂が候補)。(h1)(i) は枝をあらかじめ固定した classification でどちらの枝も確定
  結果とし、`target-refuted` にしない((h2) は構成義務で、(a)–(g) と同じ扱い)。
  型不能、指示対象の欠落、(h2) の propagation statement が F0 で型付けできない場合、
  (i) の評価点が claim boundary の固定どおりに束ねられない場合は `goal-defect` で
  止め、人間の判断で target を改める。GOAL 改訂の提案は tracking Issue のコメントに
  置く。
