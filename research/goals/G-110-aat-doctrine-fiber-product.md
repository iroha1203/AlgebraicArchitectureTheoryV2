# G-110-aat-doctrine-fiber-product — doctrine 圏の fiber product と base change

- `id`: `G-110-aat-doctrine-fiber-product`
- `status`: `active`
- `priority`: `high`
- `research mode`: `target-theorem`(mode 裁定済み 2026-08-18:
  (B)(D) は「条件同定+十分性+反例」の三点セット型 claim として
  target statement に固定する。score-phase への切替は採らない —
  n1005 §5「隊列」第4項の mode 裁定事項はこれで消化済み。**(D) の
  診断語彙は G-106 系 raw defect / reselection orbit に一本化**
  (G-104 / G-107 系 `J_A` defect profile への拡張は frontier —
  係数 base change カードとの接続点)
- `program context`: 登路上の位置は **Gr4(底の base change 完備)**
  (n1001 §3.5 達成階梯、n1005 §4.3)。「EGA 的な意味の相対性に届くのは
  Gr4」の当該カード。山頂前提の**係数** base change(ℚ→R)とは別軸で
  ある(n1005 §4.6)。隊列裁定(2026-08-15、Gr3/Gr4 系列先行)の
  第三手。Gr3(G-106+G-108+G-109 の三点セット)は完遂済み
  (G-109 = `target-theorem-proved`、2026-08-18。Gr3 達成の範囲記録は
  G-109 カード)。依存先は G-101 と G-106 のみ — **(E) のみ G-106 の
  合成 coherence に依存**(n1005 §4.3 の記載どおり)し、G-109 の
  成果には依存しない。着手条件は満たされている。
- `predecessor`: G-101(`Doct_U` / `ExtInst_U` / opcartesian 普遍性。
  完遂済み。`research/lean/ResearchLean/AG/AtomFoundation/` 配下、
  unported)、G-104 / G-107(「不変性+条件+反例」型の方法論資産。
  いずれも完遂済み)、G-106(閉性層 (E) の合成 coherence 素材。
  完遂済み = `target-theorem-proved`、2026-08-15。
  `research/lean/ResearchLean/AG/TransportCoherence/` 配下、unported。
  固定錨は下記 ledger 行)。先行考察はスキーム射幾何
  ノート(fiber product・derived fiber product・functor of points の
  各節)。
- `tracking issue`: 未起票(active 昇格はユーザー裁定済み
  2026-08-18。成立は本カード昇格 PR のマージをもって。起票はマージ後、
  `$target-theorem-loop` 起動前に行う)
- `source note`: [docs/note/n1005_aat_semantic_geometry_route_after_g107.md](../../docs/note/n1005_aat_semantic_geometry_route_after_g107.md)(§4.3 五層分解)、
  [docs/note/n1001_atom_is_all_you_need_discussion.md](../../docs/note/n1001_atom_is_all_you_need_discussion.md)(§10 ギャップ2)、
  [docs/note/aat_scheme_morphism_geometry_after_foundation.md](../../docs/note/aat_scheme_morphism_geometry_after_foundation.md)
- `research aim`: doctrine 圏 `Doct_U` に**相対的な**極限構造(fiber
  product)を立て、その上で輸送・診断が base change に対してどう
  振る舞うかを確定する。成果は5層 — (A) fiber product の構成と普遍性、
  (B) cartesian lift の存在条件、(C) Beck–Chevalley 型交換、(D) 診断の
  base change 可換性の成立条件、(E) pullback square の貼り合わせ閉性。
  これで相対的視点の全操作が doctrine 圏の中で閉じる(Gr4)。
- `core tension`: 最大リスクは自明化である — Boolean regime の零次元性に
  より fiber product が集合論的交わりへ退化し、(C) が「集合論的
  Beck–Chevalley の再証明」に堕ちる可能性が明記されている(n1005
  §4.3)。したがって非自明性は (C) の negative witness(交換が破れる
  非 pullback / lax square)と (D)(診断 base change の成立条件同定)に
  置く。(B) は `sourceMap` の非可逆性により存在自体が開いており、
  「構成」ではなく「存在条件の同定+非存在反例」が成果物形式になる。
  (D) は無条件では成立しない見立てで、成立条件の同定自体が定理 —
  G-104 / G-107 で確立した「不変性+条件+反例」型の方法論が効く、
  本カードの数学的重心である。
- `rival`: 圏論の極限の一般論(mathlib `CategoryTheory.Limits`)、
  古典的 Beck–Chevalley / base change 定理、スキーム論の fiber
  product。差は「終対象を置かない原理の下で本質的に相対的な引き戻し
  のみを立て、診断(障害・defect)の base change 可換性の成立条件と
  破れの witness まで Lean で固定する」点に置く。一般論の
  instantiation で済む部分は流用してよい。
- `claim boundary`: 固定した一般 carrier `U`、G-101 の `Doct_U` /
  `ExtInst_U` / package 総圏と輸送を対象とする。終対象・絶対積は
  導入しない(相対 pullback のみ)。carrier を動かす主張、係数 base
  change(ℚ→R。別カード)、nerve / cover 接続、`ObProblem` 段の
  class 構成の変更、derived fiber product(観察は frontier)は
  含めない。「flat」の語は lawful locus の既存命名 `Flat_U(X)` と
  衝突するため本カードでは使わない(語彙裁定済み 2026-08-18: 条件名は
  `H_cart` / `H_bc` の中立語彙のみで固定する。n1005 §4.3 (D) の
  注意)。
- `capability categories`: limit-structure、base-change、
  exchange-law、counterexample、closure。
- `threshold policy`: SCORE は使わない。runtime state は tracking Issue に
  置き、固定 statement と completion criteria だけで完了判定する。
- `portfolio constraint`: (A) の構成だけ、または (C)(D) の正例だけで
  完了扱いしない。構成・存在条件・交換・診断・閉性の五層すべてに
  Lean artifact を要求し、(C)(D) は正例(成立)と負例(破れ)の対を
  要求する。
- `phase boundary criteria`: 未証明なら `target-proof-checkpoint`、反証
  なら `target-refuted`、全完了条件と final review を満たした場合だけ
  `target-theorem-proved` とする。
- `reward rubric`: `not-applicable (target-theorem mode)`。各 cycle は
  proof obligation delta で評価する。
- `dullness filter`: 次を弾く。集合論的引き戻し+成分構造だけの
  「定義展開」fiber product(真部分 fiber 条件の witness と identity
  cone に制限しない普遍性を欠くもの。n1005 §4.3 (A) の dullness
  リスク)、(C) を fiber 側が Set 的 family fibration に還元される
  場合の古典事実の再証明で済ませ negative witness を欠く成果、(B) の
  存在条件を「lift が存在する」と同値な述語で立てる構成、(D) の成立
  条件を結論の言い換えで立てる構成、pullback square が退化(成分が
  恒等)して閉性が vacuous に立つ構成、診断が空(2-cell なし・障害
  恒零)の図式での base change 可換性の発火、**(C) の negative
  witness を hom 空間が空・成分が恒等・診断が恒零の退化 square で
  満たす構成**(安価な破れの排除)。
- `frontier`: derived fiber product の観察、係数 base change(ℚ→R)
  カードとの接続点の記述、bifibration(cartesian 側の一般論)への
  拡張、`ObProblem` 段の class naturality と (D) の関係の観察、
  G-109 (G) の core 押し出しが effectivity を保存する方向の**反射**
  (base-change / effectivity 保存反射 — G-109 report の frontier)と
  (D) の接続点の観察、
  jump-locus 相対幾何(n1005 §5「隊列」第4項の候補2)への含意、
  **(D) の `J_A` defect profile 枝**(G-104 / G-107 語彙への拡張。
  AtomFoundation doctrine 圏と K0 / K1 nerve 形式設定を結ぶ未建設の
  橋を要するため本カードの claim から外す — 立てば G-107 → 山頂
  直結路への supply となる)。

- `target theorem`: **Doctrine Fiber Product and Base Change
  Theorem**。G-101 の設定の上で:
  1. **(A) fiber product の構成と普遍性**: `Doct_U` の射の対
     `σ₁ : D₁ -> B`、`σ₂ : D₂ -> B` に対し fiber product
     `D₁ ×_B D₂` を構成し、identity cone に制限しない普遍性を証明
     する。あわせて真部分 fiber 条件の witness(fiber product が
     成分の直積にも交わりにも退化しない例)を構成する。
  2. **(B) cartesian lift の存在条件**: package 総圏の射影に対する
     cartesian lift の存在条件 `H_cart` を同定し、十分性定理と、
     `H_cart` を満たさず lift が存在しない反例(FiniteModel 上の
     非存在 Lean 証明)を対で構成する。
  3. **(C) Beck–Chevalley 型交換**: fiber product square 上の
     押し出し・引き戻しの canonical 比較射を構成し、pullback square
     での同型性を証明する。あわせて交換が破れる negative witness
     (非 pullback square または lax square 上での比較射の非同型)を
     構成する。
  4. **(D) 診断の base change 可換性**: 障害・defect の構成(**G-106
     語彙の raw defect / reselection orbit に一本化**。`J_A` defect
     profile への拡張は frontier)が base change と可換になる成立条件
     `H_bc` を同定し、`H_bc` 下の可換性定理と、`H_bc` を満たさず
     可換性が破れる反例を対で構成する。
  5. **(E) 閉性**: pullback square の貼り合わせ(水平・垂直合成)が
     再び pullback square であり、(C)(D) の比較射が貼り合わせと
     整合する(**G-106 の合成 coherence を消費**)ことを証明する。
- `target theorem boundary`: Lean 置き場所は
  `research/lean/ResearchLean/AG/DoctrineFiberProduct/` 配下(新設)。
  G-101 / G-106 のモジュールは参照のみ。完了面は (A)–(E)
  まで。(B)(D) の claim は「条件同定+十分性+反例」の三点セットで
  固定し、条件の必要十分化は frontier(G-107 の条件 C 必要十分化と
  同じ後続ハント様式)。derived 化・係数 base change・bifibration の
  一般論は主張しない。
- `target proof artifacts`: fiber product の構成と普遍性 theorem、真
  部分 fiber witness、`H_cart` の定義・十分性定理・非存在反例、
  Beck–Chevalley canonical 比較射・pullback での同型 theorem・
  negative witness、`H_bc` の定義・可換性定理・破れ反例、貼り合わせ
  閉性 theorem と比較射整合 theorem、report
  `research/reports/G-110-aat-doctrine-fiber-product.md`。
- `target proof strategy`: K0 fiber product 構成と普遍性・退化しない
  witness -> K1 cartesian lift の条件同定と反例 -> K2 Beck–Chevalley
  比較射と正負の対 -> K3 診断 base change の条件同定と正負の対 ->
  K4 閉性と整合。既存成果の利用 map: G-101 opcartesian 普遍性
  (比較射の生成)、G-104 / G-107 の「不変性+条件+反例」構成法
  (K3 の方法論)、G-106 の合成 coherence(K4 の素材)、
  `FiniteModel`(witness 計算)、スキーム射幾何ノートの fiber
  product 節(設計素材)。固定 statement と完了条件は本カードのみを
  正本とする。
- `target theorem completion criteria`: 全 artifact が sorry なしで
  `ResearchLean` に受理され、axiom / placeholder audit が clean で
  あること。下記 ledger の `discharge-required` を放電し、audit で
  provenance、proof-use、structure-field escape、route integrity を
  監査すること。Lean / report / tracking Issue を同期し、final review
  packet を作り、`$math-lean-review` の4査読がすべて
  `No major findings` であること。完遂時に Gr4 達成を report へ記録
  する。
- `target premise discharge policy`: 入力(doctrine の射の対、package、
  診断の図式データ)だけを残せる。普遍性、退化しない witness、
  `H_cart` / `H_bc` の十分性、比較射の同型性と破れ、閉性はすべて
  completion までに生成・証明する。存在・可換性の結論相当データを
  certificate や structure field で受け取るだけでは放電と数えない。
- `target material premise ledger`:
  - `carrier U / FiniteModel`: `ambient-boundary`。witness 計算のみ。
  - `G-101 / G-106 の reviewed artifact`: `ambient-boundary`。
    参照のみ、改変しない。固定錨: TransportCoherence(G-106)= PR
    #4004–#4009(fixed head `d7b1d488`、merge `ae1ba0ea`、最終同期 /
    formal review = Issue #3998 comment 5298897416)。
    AtomFoundation(G-101)= PR #3889(fixed head `db47ee9e`、merge
    `dd5e02b5`、最終固定 head 監査 = PR #3889 comment 5155944000)。
  - `fiber product の普遍性と非退化性`: `discharge-required`。集合論的
    交わりへの退化を真部分 fiber witness で排除する。
  - `H_cart / H_bc の十分性と反例対`: `discharge-required`。条件は
    構成データ側の述語として立て、結論との同値を禁じる。
  - `Beck–Chevalley 比較射の同型と negative witness`:
    `discharge-required`。比較射は普遍性から生成する。
  - `閉性と比較射整合`: `discharge-required`。G-106 coherence の
    消費は proof term として明示する。
- `target anti-weakening rule`: 結論相当の仮定(lift の存在、交換の
  同型性、診断可換性)を theorem argument、typeclass、structure
  field、certificate field へ移して成功扱いしない。`H_cart` / `H_bc` を
  結論と同値または片方向に近い述語で立てない(入力データの条件のみ)。
  (C)(D) の negative witness を省いた「正例のみの交換定理」は完了と
  数えない。`ambient-boundary` に残せるのは入力幾何だけである。
- `target failure policy`: (B) で cartesian lift が無条件に存在すると
  証明された場合は `H_cart` 節を存在定理へ置換する改訂を提案する
  (成功側の縮退であり refuted ではない)。(A) の fiber product が
  material class 上で常に集合論的交わりへ退化すると証明された場合、
  その退化定理を成果として `target-refuted` を宣言する(Boolean
  regime の零次元性の定理化として記録)。(D) の成立条件が同定に至らず
  停滞する場合は `target-blocked` とし、(D) を切り出した後続カードへの
  分割を改訂提案する。
