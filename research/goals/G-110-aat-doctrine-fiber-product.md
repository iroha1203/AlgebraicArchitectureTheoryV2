# G-110-aat-doctrine-fiber-product — doctrine 圏の fiber product と base change

- `id`: `G-110-aat-doctrine-fiber-product`
- `status`: `active`
- `priority`: `high`
- `research mode`: `target-theorem`(mode 裁定済み 2026-08-18:
  (B)(D) は「条件同定+十分性+反例」の三点セットを基本形として
  target statement に固定する。(B) は型の決まった網羅的 disjunction
  として単一命題で固定する(下記 (B))。`H_cart` / `H_bc` には資格
  条項(結論非参照・同型不変性・閉性・パラメトリック正例族・
  checker+bridge)を課す(下記 (B)(D))。score-phase への切替は
  採らない —
  n1005 §5「隊列」第4項の mode 裁定事項はこれで消化済み。**(D) の
  診断語彙は G-106 系 raw defect / reselection orbit に一本化**
  (G-104 / G-107 系 `J_A` defect profile への拡張は frontier —
  係数 base change カードとの接続点)
- `program context`: 登路上の位置は **Gr4(底の base change 完備)の
  exact-bottom sector**(n1001 §3.5 達成階梯、n1005 §4.3)。「EGA 的な意味の相対性に届くのは
  Gr4」の当該カード。山頂前提の**係数** base change(ℚ→R)とは別軸で
  ある(n1005 §4.6)。隊列裁定(2026-08-15、Gr3/Gr4 系列先行)の
  第三手。Gr3(G-106+G-108+G-109 の三点セット)は完遂済み
  (G-109 = `target-theorem-proved`、2026-08-18。Gr3 達成の範囲記録は
  G-109 カード)。依存先は G-101 と G-106 のみで、G-109 の成果には
  依存しない — **G-106 への定理依存は (E) のみ**(合成 coherence、
  n1005 §4.3 の記載どおり)であり、(C)(D) は G-106 の語彙 / API
  (comparator・raw defect・reselection orbit)を参照する語彙依存で
  定理は消費しない。着手条件は満たされている。本カードの達成範囲は
  **Gr4 の exact-bottom sector**(exact `Doct_U` / `ExtInst_U` /
  package 下層)であり、無修飾の Gr4 完遂ではない — Gr4 完遂 gate
  として refinement 系統(`RefinementDoctrineHom` の圏化と
  refinement base change)と上段(`GeomRead` / `ObProblem`)への
  base-change lift(Gr3 段横断輸送への接続 bridge)が後続カードに
  残る(n1001 §3.3 / §3.5 の relative stability 三系統)。
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
  これで exact 底層(`Doct_U` / `ExtInst_U` / package 下層)の相対
  操作が閉じる — Gr4 の exact-bottom sector。refinement 系統と上段
  への base-change lift は後続カードの範囲である(program context)。
- `core tension`: 最大リスクは自明化である — Boolean regime の零次元性に
  より fiber product が集合論的交わりへ退化し、(C) が「集合論的
  Beck–Chevalley の再証明」に堕ちる可能性が明記されている(n1005
  §4.3)。したがって非自明性は (C) の negative witness(lax square
  上の二経路比較射の不一致)と (D)(診断 base change の成立条件同定)に
  置く。(B) の cartesian 方向の存在は開いた問いである — `atomEquiv`
  共役(`transportCompositionReading` 系の逆向き輸送)による無条件
  構成が成立する経路と、上位輸送の前進成分(`objectMap` /
  `operationMap` 等。可逆性を持たない)が障害になる経路の両方が
  生きており、どちらに転んでも定理として固定できる網羅的
  disjunction を採る(下記 (B))。
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
  class 構成の変更、derived fiber product(観察は frontier)、
  refinement 射(`RefinementDoctrineHom`)の圏化(n1005 §4.3 の
  Gr4 残課題のうち本カードが解消するのは極限構造・base change
  交換・診断・閉性であり、refinement 圏化は frontier)は
  含めない。心臓圏の裁定(n1005 §4.3 の残課題): fiber product は
  `Doct_U` に立て、(C)(D) の輸送 square はそれを pointed 化した
  `ExtInst_U` 上で立てる(手続きは (C) に固定)。「flat」の語は
  lawful locus の既存命名 `Flat_U(X)` と
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
  要求する。(B) は枝によらず lift 実構成のパラメトリック正例族
  (右枝の場合は `H_cart` が相異なる非同型 instance で非空に成立
  する族)を要求する(vacuous / 単一 fixture 密着の `H_cart` の
  排除)。
- `phase boundary criteria`: 未証明なら `target-proof-checkpoint`、反証
  なら `target-refuted`、全完了条件と final review を満たした場合だけ
  `target-theorem-proved` とする。
- `reward rubric`: `not-applicable (target-theorem mode)`。各 cycle は
  proof obligation delta で評価する。
- `dullness filter`: 次を弾く。集合論的引き戻し+成分構造だけの
  「定義展開」fiber product(真部分 fiber 条件の witness と、cone の
  `atomEquiv` 成分を恒等に制限しない全 cone 上の普遍性(G-101
  opcartesian の base tail 非制限の類例)を欠くもの。n1005 §4.3 (A)
  の dullness リスク)、(C) を fiber 側が Set 的 family fibration に
  還元される場合の古典事実の再証明で済ませ negative witness を欠く
  成果、(B) の存在条件を「lift が存在する」と同値な述語または単一
  fixture との等式型述語で立てる構成、(D) の成立条件を結論の言い
  換えで立てる構成、pullback square
  が退化(成分が恒等)して閉性が vacuous に立つ構成、診断が空
  (2-cell なし・障害恒零)の図式での base change 可換性の発火、
  **(C) の negative witness を hom 空間が空・成分が恒等・診断が
  恒零・holonomy 恒等の退化 square で満たす構成、または不一致が
  定義展開で従う構成**(安価な破れの排除)、**(D) の負例を、共役
  不変な orbit / 共役類水準では自動保存される診断に対する raw 水準
  の同一視アーティファクト(同一視の取り方だけで作る破れ)で満たす
  構成**。
- `frontier`: derived fiber product の観察、係数 base change(ℚ→R)
  カードとの接続点の記述、bifibration(cartesian 側の一般論)への
  拡張、`ObProblem` 段の class naturality と (D) の関係の観察、
  G-109 (G) の core 押し出しが effectivity を保存する方向の**反射**
  (base-change / effectivity 保存反射 — G-109 report の frontier)と
  (D) の接続点の観察、
  refinement 射(`RefinementDoctrineHom`)の圏化と refinement base
  change(Gr4 完遂 gate の一)、上段(`GeomRead` / `ObProblem`)への
  base-change lift = Gr3 段横断輸送への接続 bridge(Gr4 完遂 gate の
  二)、
  jump-locus 相対幾何(n1005 §5「隊列」後続 draft 候補2 = 係数
  base change カードの jump-locus 案)への含意、
  **(D) の `J_A` defect profile 枝**(G-104 / G-107 語彙への拡張。
  AtomFoundation doctrine 圏と K0 / K1 nerve 形式設定を結ぶ未建設の
  橋を要するため本カードの claim から外す — 立てば G-107 → 山頂
  直結路への supply となる)。

- `target theorem`: **Doctrine Fiber Product and Base Change
  Theorem**。G-101 の設定の上で:
  1. **(A) fiber product の構成と普遍性**: `Doct_U` の射の対
     `σ₁ : D₁ -> B`、`σ₂ : D₂ -> B` に対し fiber product
     `D₁ ×_B D₂` を構成し、cone の `atomEquiv` 成分を恒等に制限
     しない全 cone 上の普遍性を証明する。あわせて真部分 fiber 条件の
     witness を**同型不変な形**で構成する — 有限 fixture 上で
     (i) source pullback から成分直積への canonical 射が全射でない
     こと、(ii) 両射影のいずれも同型でないこと、を証明する。選んだ
     carrier 表現の raw equality / inequality には依存させない
     (異なる `Source` 型の間には共通 ambient なしの「交わり」を
     定義しないため、その語は使わない)。
  2. **(B) cartesian lift の存在**: package 総圏の射影に対する強
     cartesian lift(G-101 の strong opcartesian の双対、mathlib
     `Functor.IsStronglyCartesian` 相当)について、**次の網羅的
     disjunction を単一の固定命題として証明する**: 「(左枝)全ての
     底射 `f : X -> Y` と `Y` 上の全ての package に対し強 cartesian
     lift が存在する」または「(右枝)資格条項を満たす `H_cart` の
     同定+十分性定理+`H_cart` を満たさず lift が存在しない有限
     反例(FiniteModel 上の非存在 Lean 証明)」。右枝を閉じる場合は
     反例が左枝を反証することも同時に証明する(排他性は反例が供給
     する)。**`H_cart` の資格条項**: (i) 入力型は底射と終点 package
     の構成データ(有限 presentation 水準)上の述語で、lift の存在と
     いう結論を参照しない、(ii) 入力データの同型で不変(同型不変性
     theorem を討ち取る)、(iii) 底射合成で閉じる(閉性 theorem)、
     (iv) fixture の tag・命名・特定 carrier 表現に依存しない(単一
     fixture との等式 `H t := t = good` 型は資格違反)、(v) 相異なる
     非同型 instance を含むパラメトリック正例族で非空発火する。
     いずれの枝でも lift の実構成正例を要求する(portfolio
     constraint)。
  3. **(C) Beck–Chevalley 型交換**: square は (A) の cospan
     `σ₁ : D₁ -> B <- D₂ : σ₂` の pullback `P = D₁ ×_B D₂`(射影
     `π₁ / π₂`)で向きを固定し、**compatible point cone**(各頂点の
     instance 選択と `ExtInstHom` 整合 — `source_eq` の proof-use を
     明示)による `ExtInst_U` square への pointed 化の上で立てる。
     compatible point cone は direction-hypothesis 入力である —
     Doct square だけからの全域持ち上げは主張しない(ledger 行)。
     押し出し(G-101 opcartesian 輸送)と引き戻し((B) の cartesian
     lift。(B) が右枝の場合、(C)(D) は `H_cart` 充足データ上で定式化
     し存在条件を継承する)に対し、canonical mate
     `(π₂)_! ∘ (π₁)^* -> (σ₂)^* ∘ (σ₁)_!`(向きはこの形で固定)を
     lift の普遍性(unit / counit)から **natural transformation
     として**構成し、自然性 theorem・cleavage(lift 選択)非依存性
     theorem・pullback square での同型性を証明する。あわせて交換が
     破れる negative witness を構成する — authored な lax 化データ
     (base change **前**の入力 presentation に属する G-106
     comparator 語彙の 2-cell datum。`Doct_U` は 2-cell を持たない
     ため型はこの語彙で固定する)を持つ具体 fixture 上で、**普遍性
     から生成された二経路の canonical 比較(natural transformation
     水準)が固定比較等式を満たさない**ことを theorem として証明
     する。comparator / holonomy を可換性破れの証拠として直接供給
     する構成、および供給 datum から定義展開で従う不一致は放電と
     数えない。正例(strict pullback square で mate が同型)と同一
     設定で対にする。
  4. **(D) 診断の base change 可換性**: まず**診断 base change 作用
     そのものを本カードで構成する** — 障害・defect の構成(**G-106
     語彙の raw defect / reselection orbit に一本化**。`J_A` defect
     profile への拡張は frontier)に対し、次を層別の Lean artifact
     として固定する: (d1) presentation の vertex / edge / cell map
     (base change に沿う presentation 引き戻し)、(d2) 各終点の
     `PackageFiberAut` 群準同型、(d3) transported admissible data の
     constructor(`edgeStrong`・`twoCellBase` は theorem として
     **導出**する — base change 後の同種 field の再供給は放電と
     数えない)、(d4) pointwise raw defect 保存 theorem、(d5)
     cochain map と reselection 作用の equivariance theorem、(d6)
     orbit map theorem。可換性等式の両辺を同一群に載せる診断比較
     写像は G-101 普遍性と (A)–(C) の構成から生成し、theorem
     argument・structure field・certificate として受け取らない。
     その上で、可換性が成立する条件 `H_bc` を同定し、**結論を
     vanishing 水準で固定した可換性定理**(`H_bc` 下で消滅
     (`TransportObstructionVanishes` 水準)が保存される。反射は
     frontier — G-109 effectivity 反射と同じ側)と、`H_bc` を満たさず
     保存が破れる反例を対で構成する。raw 等式だけの最弱可換性では
     完了と数えず、(d1)–(d6) 全層の artifact を要求する。`H_bc` の
     資格条項は (B) の (i)–(v) と同一(閉性は square の水平・垂直
     貼り合わせについて)。
  5. **(E) 閉性**: pullback square の貼り合わせ(水平・垂直合成)が
     再び pullback square であり、(C) の比較射および (D) の診断比較
     写像が貼り合わせと整合することを証明する。押し出し側の水平
     貼り合わせでは **G-106 の合成 coherence
     (`transportAlong_comp_coherence` 系)を消費**し、引き戻し側の
     合成 coherence は G-106 に存在しないため本カードで建設する。
- `target theorem boundary`: Lean 置き場所は
  `research/lean/ResearchLean/AG/DoctrineFiberProduct/` 配下(新設)。
  G-101 / G-106 のモジュールは参照のみ。完了面は (A)–(E)
  まで。(D) の claim は「条件同定+十分性+反例」の三点セットで
  固定し、(B) は上記の網羅的 disjunction 単一命題で固定する(右枝は
  同じ三点セット)。条件の必要十分化は frontier(G-107 の条件 C
  必要十分化と同じ後続ハント様式)。derived 化・係数 base change・
  bifibration の一般論は主張しない。
- `target proof artifacts`: fiber product の構成と普遍性 theorem、
  同型不変な真部分 fiber witness、(B) の disjunction 確定 artifact
  (左枝: 無条件存在定理/右枝: `H_cart` の定義・資格条項 theorem 群
  (同型不変性・閉性)・十分性定理・非存在反例)と lift 実構成の
  パラメトリック正例族、`H_cart` / `H_bc` の checker+soundness /
  completeness bridge、compatible point cone による pointed 化手続き
  と canonical mate(natural transformation)・自然性・cleavage
  非依存性・pullback での同型 theorem・破れ witness(生成比較の固定
  等式失敗)、診断 base change 作用の構成一式((D) (d1)–(d6) と
  診断比較写像)、`H_bc` の定義・資格条項 theorem 群・vanishing
  保存定理・保存破れ反例、貼り合わせ閉性 theorem・比較射整合
  theorem・引き戻し側合成 coherence、report
  `research/reports/G-110-aat-doctrine-fiber-product.md`。
- `target proof strategy`: K0 fiber product 構成と普遍性・退化しない
  witness -> K1 cartesian lift の disjunction 確定(存在定理または
  条件同定+反例) -> K2 pointed 化と Beck–Chevalley 比較射・正負の
  対 -> K3 診断 base change 作用の構成と条件同定・正負の対 ->
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
  `No major findings` であること。`H_cart` / `H_bc` それぞれに有限
  presentation 入力の checker 関数と soundness / completeness bridge
  theorem を artifact として含める(`FiniteModel` の有限性から一般
  decidability は従わないため、決定可能性は checker+bridge で操作化
  する)。完遂時の記録は **Gr4 exact-bottom sector 達成**に限定する
  — 無修飾の Gr4 / Gr 系列完遂を宣言せず、範囲根拠を併記する(達成
  は exact 底層の極限構造・base change 交換・診断可換性・閉性。
  refinement 系統の圏化・base change と上段への base-change lift は
  Gr4 完遂 gate として後続カードに残る。G-109 の Gr3 記録の範囲併記
  と同じ様式)。
- `target premise discharge policy`: 入力(doctrine の射の対、package、
  base change **前**の診断の図式データ)だけを残せる。引き戻し済み
  (transported)図式・診断比較写像の供給は放電と数えない。普遍性、
  退化しない witness、(B) の分岐確定、`H_cart` / `H_bc` の十分性、
  比較射の同型性と破れ、診断 base change 作用、閉性はすべて
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
  - `fiber product の普遍性と非退化性`: `discharge-required`。同型
    不変な真部分 fiber witness(canonical 射の非全射性・両射影の非
    同型性)で退化を排除する。
  - `compatible point cone(pointed 化の各頂点 instance 選択と
    ExtInstHom 整合)`: `direction-hypothesis`。入力資格。Doct
    square からの全域持ち上げは主張しない。
  - `H_cart / H_bc(条件そのもの)`: `direction-hypothesis`。十分性
    theorem の仮定として理論に残る(必要十分化は frontier)。資格
    条項 (i)–(v) と checker+bridge を伴う。
  - `(B) の disjunction 確定と H_cart / H_bc の十分性・反例対`:
    `discharge-required`。条件は構成データ側の述語として立て、結論
    との同値・単一 fixture 等式型を禁じる。
  - `Beck–Chevalley 比較射の同型と negative witness`:
    `discharge-required`。比較射(canonical mate)は普遍性から
    natural transformation として生成し、cleavage 非依存性 theorem
    を伴う。comparator / holonomy の自由供給による破れは放電と
    数えない。
  - `診断 base change 作用の構成`: `discharge-required`。(D)
    (d1)–(d6) の引き戻し輸送と診断比較写像は G-101 普遍性と
    (A)–(C) から生成する。引き戻し済み図式の入力供給、および base
    change 後の `edgeStrong` / `twoCellBase` / authored comparator の
    再供給は放電と数えない(authored field の資格は base change 前の
    入力 presentation に限る — G-106 の authored field と生成
    comparator の区別を維持する)。
  - `閉性と比較射整合`: `discharge-required`。G-106 coherence
    (`transportAlong_comp_coherence` 系)の消費は proof term として
    明示する。引き戻し側の合成 coherence は本カードで建設する
    (G-106 は押し出し側のみを供給する)。
- `target anti-weakening rule`: 結論相当の仮定(lift の存在、交換の
  同型性、診断可換性、診断比較写像そのもの)を theorem argument、
  typeclass、structure field、certificate field へ移して成功扱い
  しない。`H_cart` / `H_bc` は構成データ側の述語として立て、資格
  条項((B)(D) の (i)–(v))と checker+bridge(completion
  criteria)で操作化する(G-107 の decider 前例)。結論(lift の
  存在・可換性)との論理同値、および単一 fixture との等式型述語を
  禁じる — 十分性は述語から結論への含意 theorem として別立てする。
  (C) の negative witness を comparator / holonomy の自由供給で作る
  構成、(C)(D) の negative witness を省いた
  「正例のみの交換定理」、(B) 分岐 1 を強 cartesian より弱い lift
  概念で立てる構成は完了と数えない。`ambient-boundary` に残せるのは
  入力幾何だけである。
- `target failure policy`: fail-closed を原則とする — 中心 conjunct
  の反証は `target-refuted`、statement の不足の発見は `goal-defect`
  で停止し、fixed target の変更はいずれも人間の別判断とする(自動
  weakening をしない)。個別分岐: (B) は網羅的 disjunction の単一
  命題であり、どちらの枝の確定も成功である。左枝が反証され(非存在
  例が出る)かつ資格条項を満たす `H_cart` の同定に至らない場合は
  `target-blocked` で停止する。(A) の同型不変な真部分 fiber witness
  が存在し得ない(両射影が常に同型になる)ことが定理として示された
  場合、その退化定理を成果として `target-refuted` を宣言する
  (Boolean regime の零次元性の定理化として記録)。(C) の破れ
  witness が原理的に構成不能(固定比較等式が全ての資格入力で成立)
  と示された場合、および (D) の保存破れ反例が構成不能(`H_bc` 無
  条件縮退)と示された場合は、負例 conjunct の反証として
  `target-refuted` を宣言し、全可換性定理を反証成果として記録する
  (無条件定理への statement 置換は人間の改訂裁定に委ねる)。(D) の
  成立条件が同定に至らず停滞する場合は `target-blocked` とし停止
  する(後続カード分割の要否は人間裁定 — 停止記録に観察として添える
  に留める)。
