# G-110-aat-doctrine-fiber-product — doctrine 圏の fiber product と base change

- `id`: `G-110-aat-doctrine-fiber-product`
- `status`: `completed`
- `completion result`: `target-theorem-proved`。Doctrine Fiber Product
  and Base Change Theorem の固定5層 (A)–(E) を全放電
  ($target-theorem-loop Cycle 1–111、2026-08-20〜2026-08-25)。
  主要成果:
  (A) doctrine fiber product の構成と全 cone 上の普遍性+同型不変な
  真部分 fiber witness(`Nonempty` pullback・canonical 射の非全射性・
  両射影の非同型性・compatible / incompatible pair)、
  (B) carrier 大域の左枝で disjunction を確定 — 全 realization-image
  底射・全 target package に対する強 cartesian lift の存在定理+
  非同型・非可逆2成員の actual lift 族+型付き条件枝契約。左枝整合は
  `cartesianLiftNonexistence_isEmpty` で固定し、右枝専用の `H_cart`
  checker と `FiniteModelLift` は completion criteria の定めどおり
  `not-applicable`(放電扱いにしない)、
  (C) pointed Beck–Chevalley exactness(`pointedPullback_isPullback`・
  pullback reindexing functor・随伴・canonical mate・
  `packageProjection` 固有 support theorem)+authored 相対の正負
  canonicity 対(`MateCoherentRel`、replacement invariance と非自明
  orbit witness 付き)、
  (D) source-fiber-incidence 付き実 BC 二経路(direct / via-base)上の
  無条件 forward 診断共変性 (d1)–(d6)+named finite nonvacuity
  (初期 defect 非恒等・source reselection 非恒等・source / 両
  target coherence の同一 validated 入力上での同時発火)、
  (E) 水平・垂直 pasting 閉性+比較射整合+G-106 / G-109 coherence
  bridge の material proof-use。
  standard PR review は fixed head の4 lane findings を是正の上通過、
  独立 formal completion review(`$math-lean-review`)は4 lane 全て
  `No major findings`、exact-head CI 7/7・merge state
  `MERGEABLE/CLEAN`。正式判定は standard review
  ([PR #4153 コメント](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/4153#issuecomment-5409072091))、
  final completion packet
  ([PR #4153 コメント](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/4153#issuecomment-5409275633))、
  target completion audit
  ([PR #4153 コメント](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/4153#issuecomment-5409346364))
  と tracking Issue
  [#4034 完了記録コメント](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/4034#issuecomment-5409351478)
  で固定。fixed GOAL blob SHA `ed508ae5`(SHA-256
  `83f74d18d84f6f9afebdc7be28c7869845ea9a4c59b4ca7132d68c03c53d5bf5`)、
  final head `a1471483`、完了 PR
  [#4153](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/4153)
  (merge `315a2537`)。実装 PR 系列と cycle 履歴は tracking Issue
  #4034 を正本とする。公理監査は focused Lean check で standard
  axioms のみ pass、Research import direction 228 modules pass
  (Research aggregate / full build は hard rule に従い未実行)。
  **達成の記録は「有限 presentation 付き(realization 像)底層射上の
  全域 lift exact-bottom・diagnostic-covariant subcalculus 達成」に
  限定する**(左枝確定のため completion criteria の読み替えを適用)。
  **Gr4 達成の記録は本カードでは行わない** — coverage 拡張と
  full-domain 分類・refinement 系統・上段 lift・IsIso 水準
  exchange-failure 存否決定・diagnostic conservativity / reflection /
  orbit exactness は Gr4 完遂 gate(後続 gate カード群+capstone)に
  残る(program context)。`Formal/AG` への移植は未実施
  (porting status: `unported`)。
- `completed at`: `2026-08-25 JST`
- `priority`: `high`
- `research mode`: `target-theorem`(mode 裁定済み 2026-08-18、(D)
  statement 改訂 2026-08-24、(B) universe transport 改訂
  2026-08-25: (B) は「条件同定+十分性+反例」の
  型の決まった二枝 disjunction として単一命題で固定する(下記 (B))。
  `H_cart` には固定条件言語・結論非参照・同型不変性・閉性・非可逆
  入力を含むパラメトリック正例族・checker+非定義的 bridge の資格
  条項を課す。(D) は source-fiber-qualified な実 BC 経路上の無条件
  診断共変性と named finite nonvacuity で固定する。score-phase への
  切替は採らない —
  n1005 §5「隊列」第4項の mode 裁定事項はこれで消化済み。**(D) の
  診断語彙は G-106 系 raw defect / reselection orbit に一本化**
  (G-104 / G-107 系 `J_A` defect profile への拡張は frontier —
  係数 base change カードとの接続点)
- `program context`: 登路上の位置は **Gr4(底の base change 完備)の
  中間カード(第一手、exact-bottom sector)**(n1001 §3.5 達成階梯、
  n1005 §4.3)。「EGA 的な意味の相対性に届くのは
  Gr4」の当該カード。山頂前提の**係数** base change(ℚ→R)とは別軸で
  ある(n1005 §4.6)。隊列裁定(2026-08-15、Gr3/Gr4 系列先行)の
  第三手。Gr3(G-106+G-108+G-109 の三点セット)は完遂済み
  (G-109 = `target-theorem-proved`、2026-08-18。Gr3 達成の範囲記録は
  G-109 カード)。**直接依存は G-101 / G-106 / G-109 の3枚**
  (G-108 は G-109 経由の推移 import 依存)— G-106 への定理依存は
  (D) の reselection / coherence / vanishing equivalence と (E) の
  合成 coherence、G-109 へは
  **core pseudofunctor theorem package(`CoreFiber`・
  `coreFiberTransportFunctor`・compositor / unitor とその coherence
  theorem — G-109 の reviewed artifact)への declaration / proof
  依存**(**中心 obstruction theorem は不使用** — この区別を維持
  する)。消費箇所は (C) の fiber functor 経路と (E) の貼り合わせ
  (固定錨は下記 ledger 行。Gr3 成果の消費箇所の明示。G-101 からの
  再建はしない — 経路の一意化)。(C)(D) は G-106 の語彙 / API(comparator・raw defect・
  reselection orbit)も参照する。着手条件は満たされている。
  **本カードは Gr4 を閉じるカードではなく、Gr4 の中間カード
  (第一手)である**(再分類裁定 2026-08-19) — 達成範囲は exact
  `Doct_U` / `ExtInst_U` / package 下層の realization 像上の
  有限 presentation 付き(finite-code)底層射の finite
  subcalculus。Gr4 完遂 gate として
  (i) 全 semantic exact-bottom への coverage 拡張と**全域作用・分類**
  (左枝なら全域 lift、右枝なら `H_cart ↔ lift 存在` の必要十分化
  または最大 admissible class theorem — n1001 §3.5 の「相対的視点の
  全操作が閉じる」の忠実な転写。条件外入力の帰趨を決定する。(D)
  診断 base change の
  full-domain 化 = source-fiber incidence 資格の解除もこの項に
  含める — global / indexed base-change schema(全
  `ExtractionInstance` 上の base 作用・全 package の cocartesian
  保存 lift・実 BC 経路との制限比較)の建設を要する。義務の移管で
  あり削除ではない — 改訂裁定 2026-08-24)、
  (ii) refinement 系統
  (`RefinementDoctrineHom` の圏化と refinement base change)、
  (iii) 上段(`GeomRead` / `ObProblem`)への base-change lift(Gr3
  段横断輸送への接続 bridge)、(iv) **IsIso 水準の Beck–Chevalley
  exchange-failure の存否決定**(全同型定理または反例 — 存否は
  **未決定の問い**であり、本 sector と refinement / 上段 regime を
  含む設定で決定する。n1005 §4.3 の
  exchange-failure 義務の移管先であり削除ではない)、
  (v) **診断保守性・反射・orbit exactness の分類**(full-domain
  indexed action 上で `DiagnosticConservative` を構造的に生成する
  class を固定し、target vanishing から source vanishing への反射、
  reselection orbit の検出、class 外で非零 obstruction が消える有限
  witness、恒等・水平・垂直貼り合わせ閉性を証明する。生成診断部分圏
  上の `Full` + `Faithful` は十分条件候補として後続 gate カードで
  statement を固定する)が残り、
  これらを束ねる **Gr4 capstone カード(後続、番号は起草時に
  割当)が Gr4 達成を記録する**(依存順: 本カード -> gate カード群 -> capstone。Gr3 を
  G-106+G-108+G-109 の三点セットで閉じた前例と同じ複数カード
  分割。n1001 §3.3 / §3.5 の relative stability 三系統)。
- `predecessor`: G-101(`Doct_U` / `ExtInst_U` / opcartesian 普遍性。
  完遂済み。`research/lean/ResearchLean/AG/AtomFoundation/` 配下、
  unported)、G-104 / G-107(「不変性+条件+反例」型の方法論資産。
  いずれも完遂済み)、G-106((D) の reselection / coherence / vanishing
  equivalence と、閉性層 (E) の合成 coherence 素材。
  完遂済み = `target-theorem-proved`、2026-08-15。
  `research/lean/ResearchLean/AG/TransportCoherence/` 配下、unported。
  固定錨は下記 ledger 行)、G-109(core pseudofunctor API /
  coherence。完遂済み = `target-theorem-proved`、2026-08-18。
  `research/lean/ResearchLean/AG/CrossStageCoherence/` 配下、
  unported。中心 obstruction theorem へは非依存 — 固定錨は下記
  ledger 行)。先行考察はスキーム射幾何
  ノート(fiber product・derived fiber product・functor of points の
  各節)。
- `tracking issue`: #4034(runtime state 正本。proof state・cycle
  履歴・F0 で確定した schema signature の fixed head はここに同期する)
- `source note`: [docs/note/n1005_aat_semantic_geometry_route_after_g107.md](../../docs/note/n1005_aat_semantic_geometry_route_after_g107.md)(§4.3 五層分解)、
  [docs/note/n1001_atom_is_all_you_need_discussion.md](../../docs/note/n1001_atom_is_all_you_need_discussion.md)(§10 ギャップ2)、
  [docs/note/aat_scheme_morphism_geometry_after_foundation.md](../../docs/note/aat_scheme_morphism_geometry_after_foundation.md)
- `research aim`: doctrine 圏 `Doct_U` に**相対的な**極限構造(fiber
  product)を立て、その上で輸送・診断が base change に対してどう
  振る舞うかを確定する。成果は5層 — (A) fiber product の構成と普遍性、
  (B) cartesian lift の存在条件、(C) Beck–Chevalley exactness と
  canonicity obstruction、(D) 診断の base change 共変性、
  (E) pullback square の貼り合わせ閉性。
  これで exact 底層(`Doct_U` / `ExtInst_U` / package 下層)の
  有限 presentation 付き底層射の有限 subcalculus が立つ — 本カードは **Gr4 の中間
  カード(第一手)**であり、Gr4 の達成記録は行わない(capstone は
  後続カード。program context)。
- `core tension`: 最大リスクは自明化である — Boolean regime の零次元性に
  より fiber product が集合論的交わりへ退化し、(C) が「集合論的
  Beck–Chevalley の再証明」に堕ちる可能性が明記されている(n1005
  §4.3)。したがって非自明性は (C) の canonicity obstruction
  (lax square 上の二経路比較射の不一致。IsIso 水準の
  exchange-failure の存否は Gr4 gate 第四項へ移管)と (D)(診断
  base change 共変性の実経路構成と有限非自明性)に置く。(B) の cartesian 方向の存在は開いた問いである — `atomEquiv`
  共役(`transportCompositionReading` 系の逆向き輸送)による無条件
  構成が成立する経路と、上位輸送の前進成分(`objectMap` /
  `operationMap` 等。可逆性を持たない)が障害になる経路の両方が
  生きており、どちらに転んでも定理として固定できる二枝
  disjunction を採る(下記 (B))。
  (D) は Cycle 75 の `transportObstructionVanishes_map` と実 BC 二経路への
  特殊化により、source-fiber-qualified な作用が coherence と obstruction
  vanishing を無条件に送ることが確定した。したがって本カードの数学的
  重心は、この共変作用を canonical な (d1)–(d6) として組み立て、初期
  defect と reselection がともに非恒等な有限 witness 上で発火させることに
  置く。逆向きの検出能力は Gr4 gate 第五項が分類する。
- `rival`: 圏論の極限の一般論(mathlib `CategoryTheory.Limits`)、
  古典的 Beck–Chevalley / base change 定理、スキーム論の fiber
  product。差は「終対象を置かない原理の下で本質的に相対的な引き戻し
  のみを立て、診断(障害・defect)の canonical な base change 共変性と
  非自明な有限発火まで Lean で固定する」点に置く。一般論の
  instantiation で済む部分は流用してよい。
- `claim boundary`: 固定した一般 carrier `U`、G-101 の `Doct_U` /
  `ExtInst_U` / package 総圏と輸送を対象とする。終対象・絶対積は
  導入しない(相対 pullback のみ)。carrier を動かす主張、係数 base
  change(ℚ→R。別カード)、nerve / cover 接続、`ObProblem` 段の
  class 構成の変更、derived fiber product(観察は frontier)、
  full-domain 診断 base change 作用(source-fiber incidence 資格の
  解除 — frontier / Gr4 完遂 gate 第一項)、
  refinement 射(`RefinementDoctrineHom`)の圏化(n1005 §4.3 の
  Gr4 残課題のうち本カードが解消するのは極限構造・base change
  交換・診断・閉性であり、refinement 圏化は frontier)は
  含めない。心臓圏の裁定(n1005 §4.3 の残課題): fiber product は
  `Doct_U` に立て、(C)(D) の輸送 square はそれを pointed 化した
  `ExtInst_U` 上で立てる(手続きは (C) に固定)。「flat」の語は
  lawful locus の既存命名 `Flat_U(X)` と
  衝突するため本カードでは使わない(語彙裁定済み 2026-08-18: (B) の
  条件名は `H_cart` で固定する。n1005 §4.3 の注意)。
- `capability categories`: limit-structure、base-change、exchange-law、
  diagnostic-covariance、counterexample、closure。
- `threshold policy`: SCORE は使わない。runtime state は tracking Issue に
  置き、固定 statement と completion criteria だけで完了判定する。
- `portfolio constraint`: (A) の構成だけ、または (C) の正例だけで
  完了扱いしない。構成・存在条件・交換・診断・閉性の五層すべてに
  Lean artifact を要求し、(C) は正例(成立)と負例(破れ)の対を、(D) は
  無条件共変性と初期 defect・reselection がともに非恒等な named finite
  witness を要求する。(B) は枝によらず lift 実構成のパラメトリック正例族
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
  fixture との等式型述語で立てる構成、(D) を恒等 cochain・恒等
  reselection だけで発火させる構成、pullback square
  が退化(成分が恒等)して閉性が vacuous に立つ構成、診断が空
  (2-cell なし・障害恒零)の図式での base change 共変性の発火、
  **(C) の negative witness を hom 空間が空・成分が恒等・診断が
  恒零・holonomy 恒等の退化 square で満たす構成、または不一致が
  定義展開で従う構成**(安価な破れの排除)、(A) の非退化 witness を
  空 pullback で満たす構成、
  `H_cart` を同型安全域(同型な底射でのみ発火する)述語で立てる構成、
  checker bridge を定義的
  (`Iff.rfl`)に立てる構成。
- `frontier`: derived fiber product の観察、係数 base change(ℚ→R)
  カードとの接続点の記述、bifibration(cartesian 側の一般論)への
  拡張、`ObProblem` 段の class naturality と (D) の関係の観察、
  G-109 (G) の core 押し出しが effectivity を保存する方向の**反射**
  (base-change / effectivity 保存反射 — G-109 report の frontier)と
  (D) の接続点の観察、
  refinement 射(`RefinementDoctrineHom`)の圏化と refinement base
  change(Gr4 完遂 gate の二)、上段(`GeomRead` / `ObProblem`)への
  base-change lift = Gr3 段横断輸送への接続 bridge(Gr4 完遂 gate の
  三)、realization 像の coverage theorem = 全 semantic exact-bottom
  への拡張(Gr4 完遂 gate の一 — subcalculus から sector 全域への
  昇格。第一段 = 有限 carrier・有限 Source 上の同型までの coverage
  (有限 carrier では全抽出述語が有限集合で、全置換が有限 support を
  持つ)、第二段 = sector 全域)、
  full-domain 診断 base change 作用(source-fiber incidence 資格の
  解除 — 全 `ExtractionInstance` 上の base 作用・全 package の
  cocartesian 保存 lift・実 BC 経路との制限比較を伴う global /
  indexed base-change schema。一つの pullback square からは決まら
  ないため claim から外す — Gr4 完遂 gate 第一項へ移管)、
  diagnostic conservativity / reflection / orbit exactness の分類
  (full-domain indexed action 上で構造的な十分 class・反射 theorem・
  obstruction-killing finite witness・貼り合わせ閉性を揃える Gr4 完遂
  gate 第五項)、
  IsIso 水準の Beck–Chevalley exchange-failure の存否決定
  (Gr4 完遂 gate の四 — n1005 §4.3 の exchange-failure 義務の
  移管先)、
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
     witness を**同型不変な形**で構成する — realization 像内の有限
     fixture 上で(fixture の Source 型は (i)–(iii) が同時に立つ大きさ
     に選ぶ — 三つ組の Source が全て 2 元では両立しない)
     (i) pullback の `Source` が `Nonempty` であること、(ii) source
     pullback から成分直積への canonical 射が全射でないこと、(iii)
     両射影のいずれも同型でないこと、を証明し、具体的な compatible
     pair(pullback に属する)と、成分直積には属するが pullback には
     属さない incompatible pair の両方を構成する(空 pullback による
     空虚充足の排除)。選んだ carrier 表現の raw equality /
     inequality には依存させない(異なる `Source` 型の間には共通
     ambient なしの「交わり」を定義しないため、その語は使わない)。
  2. **(B) cartesian lift の存在**: package 総圏の射影に対する強
     cartesian lift(G-101 の strong opcartesian の双対、mathlib
     `Functor.IsStronglyCartesian` 相当)について、**次の二枝
     disjunction を単一の固定命題として証明する**: 「(左枝)全ての
     carrier `U`・全ての realization 付き底射 `f : X -> Y`・`Y` 上の
     全ての package に対し強 cartesian lift が存在する」または
     「(右枝)全 carrier で一様に定義された、資格条項を満たす
     `H_cart` の同定+一様十分性定理+`H_cart` を満たさず lift が
     存在しない有限反例(具体 FiniteModel carrier 上の非存在 Lean
     証明)」。**disjunction は carrier 大域で一本に固定する** —
     `∀ U, (左 U ∨ 右 U)` の per-carrier 分岐は採らない(右枝の
     `H_cart`・十分性は `U` に一様であり、反例は大域左枝を反証
     する)。右枝を閉じる場合は反例が左枝を反証することも同時に
     証明する(排他性は反例が供給する。網羅性(`¬左 -> 右`)は
     主張しない — 左枝が反証され資格付き `H_cart` の同定に至らない
     場合は `target-blocked`、failure policy 記載どおり)。
     **universe の固定**: 分岐・producer・regime は
     universe-polymorphic な完全 signature
     (`GlobalCartesianLift.{u}` / `RightBranch.{u}` /
     `RightBranchArtifact.{u}` /
     `DisjunctionArtifact.{u}` / `cartesianRegimeOfDisjunction.{u}`)
     で立てる。右枝の有限反例は universe 0 の `FiniteModel.carrier`
     上で構成する。**右枝を選択した場合に限り**、その固定有限
     fixture から named target package を内部生成し、任意 universe
     `u` にはその named package の canonical lift を生成する
     **`FiniteModelLift.{u}`**を discharge-required とする。これは
     任意 `AATCorePackage FiniteModel.carrier` の exact reindexing を
     要求しない一方、named package の全 component graph、任意の
     supplied high `StrongCartesianLift` を入力として実消費する low
     lift reflection、反例の非存在証明の移送を要求する。reflection
     producer は別の named positive fixture 上でも発火させ、空領域
     elimination を放電と数えない。左枝を選択した場合、右枝反例と
     `FiniteModelLift` は completion obligation ではない
     (`cartesianLiftNonexistence_isEmpty` による枝整合を記録する)。
     ただし universe-polymorphic signature 自体を弱めず、右枝時の
     暗黙の `u = 0` 限定はしない。任意 package の cross-universe
     exact reindexing はこの反例資格より強い Lean 表現上の補助
     artifact であり、G-110 にも Gr4 gate にも移管しない。Gr4 gate
     第一項に残る数学的義務は、各固定 carrier 内の全 package に対する
     cocartesian 保存 lift・full-domain indexed action・実 BC 経路との
     制限比較である。
     **右枝時の型付き結合を固定する**: 右枝を選択する実装は、bare
     `RightBranch` ではなく、選択した `right : RightBranch.{u}` と
     `RightFiniteModelLiftFamily.{u} right` を同時生成する
     `RightBranchArtifact.{u}` を conditional payload とする。これは
     任意 `right : RightBranch` を一つの反例へ同一視する全称 theorem
     ではない。同じ branch-local signature family に (i) fixed finite
     fixture data だけから生成する
     `finiteCounterexampleInput` と `finiteCounterexampleTargetPackage`、
     (ii) `RightBranch.finiteCounterexample.nonexistence` の input / target
     package がその2出力に一致する dependent endpoint theorem、
     (iii) `finiteModelLiftCounterexampleInput.{u}` と
     `finiteModelLiftCounterexampleTargetPackage.{u}`、(iv) supplied high
     lift を明示引数に取る
     `reflectFiniteModelCounterexampleLift.{u}`、(v) low / high input・
     package・total-hom の全 component graph を束ねる
     `FiniteModelLiftComponentGraph.{u}`、(vi) low `no_lift` と reflection
     から high `no_lift` を導く `finiteModelLift_noLift.{u}` を持つ。
     (i) の computational body は
     `RightBranch.finiteCounterexample.nonexistence.input` / `targetPackage`
     field を読まず、fixed fixture の finite data から生成する。(ii) が
     field-selected 反例と生成 package を結び、(iii)–(vi) は同じ
     (i) の output を index とする。別 fixture の graph / reflection と
     右枝反例を後から等置する実装は放電と数えない。このsignatureの
     dependent equality / `HEq` の最終Lean表現は右枝を選択する場合の
     typing obligation とし、tracking Issue に fixed head を記録する。
     declaration signature の下限は次から弱めない(`right` は同じ
     output package 内で生成された右枝証拠、transport先はその
     declaration の universe `u`):

     ```lean
     structure RightFiniteModelLiftFamily.{u} (right : RightBranch.{u}) where
       finiteCounterexampleInput : RealizableHom FiniteModel.carrier
       finiteCounterexampleTargetPackage :
         CoreFiber finiteCounterexampleInput.semantic.target
       finiteCounterexampleNoLift :
         ¬ HasStrongCartesianLift finiteCounterexampleInput.semantic
           finiteCounterexampleTargetPackage
       rightFiniteCounterexampleInput_eq :
         right.finiteCounterexample.nonexistence.input =
           finiteCounterexampleInput
       rightFiniteCounterexampleTargetPackage_heq :
         HEq right.finiteCounterexample.nonexistence.targetPackage
           finiteCounterexampleTargetPackage
       rightFiniteCounterexample_eq :
         right.finiteCounterexample.nonexistence =
           { input := finiteCounterexampleInput
             targetPackage := finiteCounterexampleTargetPackage
             no_lift := finiteCounterexampleNoLift }
       finiteModelLiftCounterexampleInput :
         RealizableHom finiteModelLiftCarrier.{u}
       finiteModelLiftCounterexampleTargetPackage :
         CoreFiber finiteModelLiftCounterexampleInput.semantic.target
       reflectFiniteModelCounterexampleLift :
         StrongCartesianLift finiteModelLiftCounterexampleInput.semantic
             finiteModelLiftCounterexampleTargetPackage →
           StrongCartesianLift finiteCounterexampleInput.semantic
             finiteCounterexampleTargetPackage
       componentGraph : FiniteModelLiftComponentGraph
         finiteCounterexampleInput finiteCounterexampleTargetPackage
         finiteModelLiftCounterexampleInput
         finiteModelLiftCounterexampleTargetPackage
         reflectFiniteModelCounterexampleLift
       finiteModelLift_noLift :
         ¬ HasStrongCartesianLift
           finiteModelLiftCounterexampleInput.semantic
           finiteModelLiftCounterexampleTargetPackage

     structure RightBranchArtifact.{u} where
       right : RightBranch.{u}
       finiteModelLift : RightFiniteModelLiftFamily.{u} right
     ```

     `DisjunctionArtifact.conditional` の最終 payload は bare
     `RightBranch` ではなく `RightBranchArtifact` とする。右枝 producer
     は `right` と `finiteModelLift` を同時に構成し、family fieldを
     caller-supplied certificateとして受け取らない。
     `FiniteModelLiftComponentGraph` は上記4 endpointとreflectionを
     indexに持ち、input/package/total-homのcanonical lift graphを保持する。
     `finiteCounterexampleNoLift` のproof termは right branch の
     `finiteCounterexample.nonexistence.no_lift` と2本の endpoint 一致を
     実消費し、`finiteModelLift_noLift` のproof termは
     `reflectFiniteModelCounterexampleLift` と
     `finiteCounterexampleNoLift` を実消費する。
     **二層の入力型と量化の
     固定**: presentation 層 `CartPresentation U`(底射の有限
     presentation データ)と semantic 層 `CartSemanticInput U`
     (**named structure** — field は `source : ExtInst_U`・
     `target : ExtInst_U`・`hom : source ⟶ target` の3本。nested
     `Sigma` は採らない — `.hom` 射影を型として保証する)を分離
     して本カードで定義し、realization
     `toSemanticCart : CartPresentation U -> CartSemanticInput U` で
     結ぶ。presentation は **raw code / validated の二段**で固定
     する — raw code(下記 field 4種の有限 code、`DecidableEq`
     付き)と well-formedness 述語による validated 部分型、decode =
     `toSemanticCart`(validated code 上)、および **realization
     soundness theorem**(decode の出力が実際に `ExactDoctrineHom` /
     `ExtInstHom` の公理(`normalize_eq`・`extraction_iff`・
     `source_eq`)を満たす)を完全 signature の discharge-required
     とする。**`H_cart` は realization witness 付き射の型
     `RealizableHom U`(semantic 射+その presentation witness)上の
     述語として固定する** — 大域 `MorphismProperty` は採らない
     (像外の値と closure の provenance が未固定になるため。恒等・
     合成・pullback 安定の closure は presentation constructor
     (`idPresentation` / `compPresentation` /
     `pullbackPresentation`)相対の theorem として立てる)。checker
     は presentation 層 `checkCart : CartPresentation U -> Bool` で、
     bridge は `checkCart P = true ↔
     H_cart (realizableHomOf P)`(validated `P` から `RealizableHom`
     を作る canonical 構成子経由)で型を固定する。**量化域の固定(realization 付き入力)**: 右枝の
     十分性・安定性・反例と (C)–(E) の regime 消費は、いずれも
     realization 付き入力(`P : CartPresentation U` とその
     `toSemanticCart P`)上で量化する — `toSemanticCart` の像の外の
     semantic 射は本カードの主張域外である(scope の明示。像外まで
     拘束する評価器は要求しない代わりに、主張域を realization 付き
     入力へ正確に限定する)。**presentation 取替え不変性 theorem**
     `toSemanticCart P = toSemanticCart P' -> checkCart P =
     checkCart P'` を discharge-required とする(同一 semantic 入力
     を表す presentation 間で評価が一致する — 像外差し替えによる
     結論符号化の排除)。**schema は有限 code 族として本カードで設計を
     固定し、signature は F0 で確定する** — カードが固定するのは
     field の役割と不変条件 (s1)–(s6) であり、Lean signature 水準の
     最終確定は F0 schema typing の proof obligation(elaboration の
     実フィードバック付き — `target proof strategy`)で行い、確定した
     signature は tracking Issue に fixed head として記録する(F0
     固定後の field / constructor 追加は改訂扱い)。**二層原理**: 底層
     (`Doct_U` / `ExtInst_U`)の対象と射は有限 code で presentation
     し、package 層(終点 package・lift・admissible data・comparator
     値)は G-106 `AdmissibleLiftData` / `AdmissibleTransportData` と
     同じく semantic interpretation として入力する(有限 code 化し
     ない — package 依存の `PackageFiberAut` と多 field の上位 hom は
     presentation の対象外)。**底層 code 族の不変条件**:
     (s1) **Source は presentation ごとに持つ有限型**(`Fintype`+
     `DecidableEq`)— pullback の Source は成分 Source の直積の
     decidable 部分型として成長するため、単一 fixture の固定 Source 型
     (`FiniteModel.ExtractionSource` 等)への錨止めはしない(code
     族は Source 型を閉性演算の下で持ち回る);
     (s2) doctrine code = Source 有限型・`normalize` の有限表・各
     source の抽出述語の有限 presentation(`U.Atom` の有限集合による
     inclusion / exclusion 表 — 有限 carrier 上では全述語を、無限
     carrier 上では finite / cofinite 述語を表す)。decode は
     `Vocabulary` / `SemanticReading` / `Resolution` を unit に固定し
     抽出を `semanticAllows` に載せる(`FiniteModel.extractionDoctrine`
     と同じ reviewed 構成法 — FiniteModel の fixture doctrine は
     realization 像の元(同型まで)であり、schema の錨ではない)。
     instance code = doctrine code+pointed source index(点は対象側
     `X.source` に属する);
     (s3) hom code = `sourceMap` の有限表(任意写像 — **非可逆を
     許す**。exact hom の `atomEquiv` は常に同型なので、底層の非可逆
     性の唯一の源泉は `sourceMap` である)+`atomEquiv` の
     finite-support 置換表(support 外恒等。decode と checker は
     `[DecidableEq U.Atom]` を presentation 層の instance 仮定とする
     — semantic 層の theorem には課さず、(B) 左枝の「全ての carrier」
     は realization 付き入力の量化域としてこの仮定込みで読む。
     witness fixture の carrier では既備)。hom code は `source_eq`
     (両端の pointed index の整合)を有限検査する;
     (s4) raw code は有限 field 4種(source instance code・target
     instance code・`sourceMap` 表・`atomEquiv` 表)。`DecidableEq` は
     等式原子の値型(Source code の値・`U.Atom`・表の成分)に課す —
     Source code を first-order(`n : ℕ` と `Fin n` 等)に取るか、
     pullback の Source を再列挙するかは F0 の選択に委ねる。validated
     部分型の well-formedness 述語 = decoder 全域性条件
     (`normalize_eq`・`extraction_iff`・`source_eq` の有限検査 —
     決定可能な十分条件でよく、像はその条件で正確に限定する。hom の
     逆は要求しない);
     (s5) **code 族は閉性 constructor(id / comp / pullback /
     pasting)の下で閉じる** — `pullbackPresentation` は Source の
     部分型(またはその再列挙)・抽出表の行の複写・置換表の合成と逆
     (`π₂` の `atomEquiv` は `σ₁.atomEquiv.trans σ₂.atomEquiv.symm`
     — finite-support 置換の逆は有限表で計算可能)で code 族の中に像
     を持ち、閉性は下記の閉性 constructor 節の discharge-required
     theorem として立てる(閉性が立たない code 族は schema として
     不可)。pullback の realization 整合 theorem は `IsPullback`
     水準(同型まで)でよく、id / comp / pasting は等式で立てる;
     (s6) semantic payload・結論寄り certificate・条件 bit の field は
     持たない。**realization 像 = 有限 presentation を持つ底層射
     (finite-code exact-bottom 射 — EGA の有限表示射とは無関係の
     語であり、英語注記は finite-code に限る)**であり、subcalculus の
     達成表示もこの語で限定する(下記 completion criteria)。
     `PackageFiberAut` の値(authored 割当表)は semantic
     interpretation であり、witness fixture(`FiniteModel.carrier`
     上)では G-106 `FiniteWitnesses` の既存 reviewed 取り扱いと同じく
     有限に列挙・判定可能である。`BCPresentation U` の **authored
     field は(cospan の `CartPresentation` 対・compatible point
     data の有限表・base change 前診断図式の有限 presentation
     (G-106 schema 参照))のみ**+well-formedness 述語で全列挙
     する — **pullback presentation と realization 等式は authored
     field に置かず、producer(`pullbackPresentation`)の出力と
     theorem として生成する**(計算済み pullback・certificate の
     caller 供給による structure-field escape の禁止)。
     `BCSemanticInput U` の field は(base change 前の square・
     compatible point data・base change 前の診断図式)のみとする — **regime は field に
     持たない**(theorem は producer 出力の regime で index する。
     conclusion-bearing な `CartesianRegime` を入力 field へ戻す
     経路の禁止。condition bit・結論 certificate の field も存在
     しない)。**realization 像の閉性 constructor を
     discharge-required とする**: `idPresentation`・
     `compPresentation`・`pullbackPresentation`((A) の構成から
     `π₁ / π₂` の presentation を生成する — (C) の `π₁^*` はこの
     presentation 上で構成する)・`pastePresentation`(square の
     水平・垂直貼り合わせ)と、各々の realization 整合 theorem
     (`toSemantic (comp P Q) = toSemantic P ≫ toSemantic Q` 等)。
     これにより (B)→(C)→(E) の出力が同じ calculus の次の入力へ
     戻る(realization 像内の id / comp / pullback / pasting
     閉性)。
     十分性定理は realization 付き semantic 底射 `f` について
     `H_cart f -> (∀ 終点上の package Q、強 cartesian lift が存在)`
     (endpoint package は全量化)の形で固定する。**分岐結果の持ち
     出し**: (B) の帰結は dependent structure `CartesianRegime U`
     (左枝: 全域 lift 供給/右枝: `H_cart`+資格 theorem 群+十分
     性)として package 化し、**producer theorem
     `cartesianRegimeOfDisjunction : DisjunctionArtifact ->
     ∀ U, CartesianRegime U` を discharge-required とする** — 左枝は
     大域存在定理の instantiation、右枝は一様 `H_cart`・十分性の
     instantiation であり、**反例からは生成しない**(反例の役割は
     大域左枝の反証のみ)。任意引数として供給される
     `CartesianRegime` は conclusion-equivalent であり放電と数え
     ない。(C)–(E) は producer から得た固定 regime
     `R : CartesianRegime U` の上で立てる。**`H_cart` の資格条項**: (i) **固定
     条件言語** — 許容原子式を列挙した named syntax 型
     `CartConditionSyntax`(presentation の構成 field 上の等式・
     所属・有限全称の原子式。原子式は lift 存在・消滅・mate 等の
     結論語彙を参照できない)と評価器を本カードの artifact として
     固定する。**vocabulary は本カードで完全列挙する**(後決めの
     named structural vocabulary に委ねない): 許容 projection =
     presentation field 4種の各成分値の読み出しのみ、operand 型 =
     各 field の有限 code 値型、許容定数 = 恒等 source 表・恒等(空
     support)置換・空 support 集合の named constants のみ(fixture の
     特定 source 値や係数定数は持たない)、許容関係 = 値の等式と、
     presentation 自身の field から導出される有限集合への所属のみ。
     外部有限集合・fixture 値・checker 出力・target 結果に由来する
     定数の持ち込みは禁止し、checker 由来 predicate を補助 lemma で
     包んで `H` とする構成も禁止する(route gate と ledger の依存
     規則)。**以後の projection / constant / relation / 有限集合の
     追加は target 改訂扱いとする**。その上で、`H_cart` はある syntax 項の評価と bridge で結ばれる形で
     のみ立てる(任意述語は不可。condition bit・lift / 比較
     certificate の presentation への埋め込み、`check := if H then true else false` 型の
     classical 決定は禁止)、結論(lift の存在)を参照しない、(ii)
     入力データの同型で不変(同型不変性 theorem)、(iii)
     **pullback-stable wide class をなす** — 恒等射を含み、合成で
     閉じ、pullback で安定する(closure は presentation
     constructor(`idPresentation` / `compPresentation` /
     `pullbackPresentation`)相対の theorem として立てる —
     `RealizableHom U` 上の述語であり大域 property ではない。(C) の
     脚 `π₁ / π₂` の admissibility は cospan の admissibility から
     この安定性 theorem で導き、脚ごとの証拠供給にしない)、
     (iv) fixture の tag・命名・特定 carrier 表現に依存しない(単一
     fixture との等式 `H t := t = good` 型は資格違反)、(v) **非恒等
     かつ非可逆な底射を含む**相異なる非同型 instance のパラメトリック
     正例族で非空発火する(`H_cart := 底射が同型` 型の同型安全域
     述語はこの項で資格違反)。checker は右枝のみの completion
     obligation とし、bridge は非定義的 theorem として立てる
     (`H P := check P = true` と定義して bridge を `Iff.rfl` で放電
     する構成は放電と数えない)。いずれの枝でも lift の実構成正例を
     要求する(portfolio constraint)。
  3. **(C) Beck–Chevalley exactness と canonicity obstruction**:
     square は (A) の cospan
     `σ₁ : D₁ -> B <- D₂ : σ₂` の pullback `P = D₁ ×_B D₂`(射影
     `π₁ / π₂`)で向きを固定し、**compatible point cone**(各頂点の
     instance 選択と `ExtInstHom` 整合 — `source_eq` の proof-use を
     明示)による `ExtInst_U` square への pointed 化の上で立てる。
     compatible point cone は direction-hypothesis 入力である —
     Doct square だけからの全域持ち上げは主張しない(ledger 行)。
     **pointed square が `ExtInst_U` の categorical pullback である
     こと自体を theorem として討ち取る** —
     `pointedPullback_isPullback : IsPullback π₁ π₂ σ₁ σ₂`
     (`ExtInst_U` 水準)を compatible point cone と (A) の具体
     Source pullback・`source_eq` から生成する(discharge-required。
     `IsPullback` を入力 field で供給する形は不可)。押し出し
     (G-101 opcartesian 輸送)と引き戻し((B) の producer から得た
     `CartesianRegime U` を消費する。右枝 regime では **membership
     の要求脚を固定する**: pointed cospan の脚 `σ₂` に `H_cart`
     membership を要求し、`pointedPullback_isPullback` と pullback
     安定性 theorem で `π₁` の membership を導出する — mate が消費
     する引き戻しは `(π₁)^*` と `(σ₂)^*` のこの2本であり、脚ごとの
     証拠供給はしない)に対し、canonical mate
     `(π₂)_! ∘ (π₁)^* -> (σ₂)^* ∘ (σ₁)_!`(向きはこの形で固定)を
     lift の普遍性(unit / counit)から **natural transformation
     として**構成する。このために **producer 由来の pullback
     reindexing functor `f^*` の構成・functor law(id / comp)・
     随伴 `f_! ⊣ f^*`(unit / counit)・compositor / unitor・
     cleavage(lift 選択)非依存性を明示の discharge artifact と
     する**(strong cartesian lift の存在だけからは従わない —
     G-109 が供給するのは共変押し出し側のみ)。自然性 theorem と
     pullback square での同型性を証明する — **pullback square 上の
     mate 同型は bifibration / pseudofunctor coherence の一般論から
     は従わないため、`packageProjection` 固有の Beck–Chevalley
     exactness support theorem を discharge-required とする**。
     あわせて交換の canonicity が破れる negative witness を構成
     する。**比較射は
     どちらの辺も入力 field に置かない** — 負例入力は
     `AuthoredBC2CellPresentation`(有限 raw field のみ。比較射・
     natural family・期待等式を field に持たず、その原子データから
     canonical mate や expected equality を符号化できない)とし、
     そこからの 2-cell family(成分量化+自然性)は**生成手続き**で
     構成する(G-106 の `AdmissibleTransportData.comparator` は単一
     endpoint package 上の値で成分量化を持たないため、字義流用では
     なく本カードで component 化する。`Doct_U` は 2-cell を持た
     ない)。**raw schema と生成域を本カードで固定する**:
     `AuthoredBC2CellPresentation` の field は G-106 の authored
     comparator 表と同形(指定有限 cell 集合上の `PackageFiberAut`
     元の有限割当表 — 既存 reviewed schema `AdmissibleTransportData`
     の authored field 部分への参照で固定)のみとする。**2-cell
     family は fiber 全対象へは拡張しない** — 点ごとの表から
     full-fiber natural family への canonical 拡張は存在しないため、
     負例の比較は **authored support(datum の載る pointed
     endpoint)上に制限**し、点ごとの割当表からの誘導比較の構成を
     discharge-required とする(相対述語の domain 制限 — 下記)。
     **負例の主張を「authored 比較に相対的な不一致」として正直に
     限定する**(相対障害への reframing — 割当表への新設 gauge の
     発明は撤回する。割当表への既存作用は存在せず、後決めの新設
     作用は target-fitting を型で防げないため): 対の述語は
     **相対述語 `MateCoherentRel`** — authored datum(G-106
     comparator 表と同型の割当表 — semantic interpretation。witness
     fixture 上で値は有限に列挙・判定可能)が誘導する比較と、普遍性から生成
     された canonical mate との、**authored support 上での一致** —
     とし、domain は authored datum 付き square(strict square =
     恒等 datum)で正負共通に型付けする(full fiber と有限部分圏の
     domain 不一致問題はこの相対化で消える)。この相対性は G-106 の
     raw defect(authored comparator と canonical comparator の相対
     不一致)と同じ型の障害であり、絶対的な BC 交換破れを僭称し
     ない。**不変性は実在する G-106 作用に錨止めする**: 負例の相対
     不一致は、`InReselectionOrbit`(raw cochain への実在
     reselection 作用)の**全軌道**で不変に非消滅であることを要求し
     (軌道の非自明性 witness — 軌道が一点でないことの concrete
     witness — を同一 fixture に義務化)、authored twist だけで作る
     見かけの不一致(orbit 一点で消えるもの)は放電と数えない。
     canonical / direct comparison の依存元は replacement-invariance
     theorem と proof-use audit で拘束する(identity wrapper・合成を
     介した authored comparator の再包装も同 audit の対象)。比較
     射・natural family・期待等式の field は存在せず、target 固定後
     に schema を設計する余地を残さない。strict square は恒等
     datum の特殊化とする。正負の対: 正例 = strict pullback square
     での `MateCoherentRel`(および canonical mate の同型性 —
     絶対述語 `IsIso` は正例側の別 theorem)、負例 = 具体 lax
     fixture 上での `¬ MateCoherentRel`(orbit 不変)。**負例は
     Beck–Chevalley 交換の `IsIso` 水準の破れではなく、authored
     比較に相対的な canonicity obstruction の独立 theorem として
     固定する** — `¬ MateCoherentRel` は正例側の `IsIso mate` と
     両立し得る別軸であり、その否定ではない。n1005
     §4.3 の「交換が破れる witness」は本カードでは canonicity 破れ
     として実現し、`IsIso` 水準の破れは構成可能性が未決定のため
     本カードでは主張しない(この n1005 からの差異を明記して固定
     する)。**IsIso 水準の exchange-failure の存否決定
     (全同型定理または反例)は Gr4 完遂 gate 第四項へ移管する**
     (program context。義務の削除ではない — ユーザー裁定
     2026-08-19)。負例 fixture の値の選択は
     proof obligation 選定時に固定し(schema は上記のとおりカードで
     固定済み)、以後の target-fitting 選択を route integrity gate で
     禁止する。誘導比較と canonical mate の生成が raw field を直接
     返さないことは proof-use / structure-field escape audit で監査
     する。
     `IsIso` は正例側の追加 theorem であり負例の否定軸ではない
     (`¬ IsIso` の構成可能性は**未決定の問い**であり — 存否は Gr4
     完遂 gate 第四項で決定する — 負例形として義務化すると構成不能
     だった場合に (C) が反証で死ぬ設計リスクがあるため採らない。
     対の述語は一致述語で固定する)。canonical
     comparison を非自明な自己同型で twist した authored 比較の
     供給、および供給 datum から定義展開で従う不一致は放電と数え
     ない。
  4. **(D) 診断の base change 共変性**: **診断 base change 作用
     そのものを本カードで構成する**。障害・defect は G-106 語彙の
     raw defect / reselection に一本化する(`J_A` defect profile への
     拡張は frontier)。**組合せ層は固定する** — base change は
     presentation(vertex / edge / cell)を同一に保ち、semantic
     interpretation(endpoint package・lift・admissible data)に作用する
     (組合せ層まで動かす一般 presentation hom は frontier)。
     **量化域(診断入力資格)を固定する**(改訂裁定 2026-08-24) —
     (d1)–(d6) は ordinary interpretation
     (`BCDiagnosticInterpretation` — decode した診断幾何上の G-106
     admissible data)と、pointed square の southwest 頂点への
     **source-fiber incidence**(`DiagnosticSourceFiberIncidence`、
     southwest 特殊化は `BCDiagnosticSourceFiberIncidence`)の対で
     量化する。incidence は全 source package が southwest 対象上に
     載ることと全 source edge がその恒等上で vertical であることを
     記録する、(C) の compatible point cone と同格の
     `direction-hypothesis` である。source edge の可逆性は source
     `edgeStrong` と verticality から fiber isomorphism として導出する。
     任意 ordinary interpretation からの incidence 普遍生成は
     `no_universalBCDiagnosticSourceFiberIncidence` が否定する。同 theorem
     は `FiniteModel.carrier` 上の全 presentation / interpretation を
     量化する普遍生成命題を一つの realized finite counterexample で
     反証し、carrier 大域の generator が存在しないことを確定する。
     full-domain 化は global / indexed base-change schema を構成する
     Gr4 完遂 gate 第一項が担う。

     (d1)–(d6) は pointed square が生成する southwest -> northeast の
     **実 BC 二経路**(direct / via-base core-fiber functor)で構成する:

     - (d1) 同一組合せ層上の source-fiber interpretation と、両経路の
       target interpretation。
     - (d2) 各終点の `PackageFiberAut` 群準同型。identity cochain 保存と
       edge / path 上の functoriality を theorem として持つ。
     - (d3) transported admissible data の constructor。target comparator
       は `transported.comparator c = φ_(target c)
       (source.comparator c)` で生成し、target `edgeStrong` と
       `twoCellBase` を導出する。
     - (d4) source `EdgeReselection` を target `EdgeReselection` へ送る
       canonical map(`mapEdgeReselection`)。reselected edge / path が
       core-fiber functor の写像と一致する theorem を伴う。
     - (d5) 各 source reselection `r` に対する coherence 保存
       `CoherentAt source r -> CoherentAt target (map r)`。source の
       core-fiber 等式へ functor を作用させ、(d3) の生成 comparator と
       (d4) の path map を proof term として消費する。
     - (d6) obstruction vanishing 保存
       `TransportObstructionVanishes source ->
       TransportObstructionVanishes target`。一般 fiberwise functor の
       theorem と、direct / via-base 各実経路への特殊化を持ち、(d4)(d5)
       から coherent reselection witness を構成する。

     診断比較写像は G-101 普遍性と (A)–(C) の構成から生成し、theorem
     argument・structure field・certificate として受け取らない。
     (d1)–(d6) は追加条件なしの forward covariance であり、Cycle 75 の
     `transportObstructionVanishes_map`、
     `bcDiagnosticDirectTransportObstructionVanishes`、
     `bcDiagnosticViaBaseTransportObstructionVanishes` が statement の
     既存候補である。旧カードの source-vanishing / target-nonvanishing
     必須 witness は `no_bcDiagnosticQualifiedVanishingCounterexample` が
     同じ量化域より広い形で否定したため、この改訂では要求しない。

     **named finite nonvacuity** として、同一の validated finite
     presentation・ordinary interpretation・incidence・source
     reselection `r` 上で
     `∃ c, initialRawDefectCochain source c ≠ 1`、`r ≠ 1`、
     `CoherentAt source r` を同時に証明し、(d4) が生成する direct / via
     の両 target reselection が (d5) で coherent となり、(d6) の
     vanishing 保存が発火することを要求する。これにより初期 defect が
     恒等、または identity reselection だけで閉じる発火を排除する。
     pointwise raw-defect reflection、source orbit の検出、target
     vanishing から source vanishing への反射は Gr4 完遂 gate 第五項の
     `DiagnosticConservative` カードが分類する。
  5. **(E) 閉性**: pullback square の貼り合わせ(水平・垂直合成)が
     再び pullback square であり、(C) の比較射および (D) の診断比較
     写像・mapped reselection・coherence 保存・vanishing 保存が
     貼り合わせと整合することを証明する。押し出し側の水平
     貼り合わせでは **G-106 の合成 coherence
     (`transportAlong_comp_coherence` 系)を消費**し、引き戻し側の
     合成 coherence は G-106 に存在しないため本カードで建設する。
     G-106 coherence は package 水準の射等式、G-109 compositor
     coherence は fiber functor 水準であるため、**両者を結ぶ bridge
     declaration(package 水準等式と fiber functor compositor の
     整合 theorem)を建設し、`transportAlong_comp_coherence` はその
     proof term で実消費する**(装飾的引用の排除)。
- `target theorem boundary`: Lean 置き場所は
  `research/lean/ResearchLean/AG/DoctrineFiberProduct/` 配下(新設)。
  G-101 / G-106 / G-109 のモジュールは参照のみ。完了面は (A)–(E)
  まで。(D) の claim は incidence 付き実 BC 二経路上の無条件 forward
  covariance と named finite nonvacuity で固定し、(B) は上記の二枝
  disjunction 単一命題で固定する(右枝は条件同定+十分性+反例)。診断の
  reflection / orbit exactness は Gr4 完遂 gate 第五項が扱う。derived
  化・係数 base change・bifibration の一般論は主張しない。
- `target proof artifacts`: fiber product の構成と普遍性 theorem、
  同型不変な真部分 fiber witness(`Nonempty` pullback・canonical 射
  の非全射性・両射影の非同型性・compatible / incompatible pair)、
  有限 code 族 presentation schema(不変条件 (s1)–(s6)。signature は
  F0 で確定)と decoder・soundness theorem・code 族の閉性 theorem、`CartPresentation U`(raw code / validated
  二段+`DecidableEq`)/ `CartSemanticInput U`(named structure)/
  `RealizableHom U` と `realizableHomOf` / `RealizableSquare U` と
  `realizableSquareOf` / `BCPresentation U` /
  `BCSemanticInput U` と `toSemantic` realization・realization
  soundness theorem、条件言語 `CartConditionSyntax`
  と評価器、presentation 取替え不変性 theorem、presentation 閉性
  constructor 4種(id / comp / pullback / pasting)と realization
  整合 theorem、`CartesianRegime U`(分岐結果の dependent package)
  と producer `cartesianRegimeOfDisjunction`、
  (B) の disjunction 確定 artifact(左枝: 無条件存在定理/右枝:
  `H_cart` の定義・資格条項 theorem 群(同型不変性・pullback-stable
  wide class)・十分性定理・非存在反例・checker+非定義的 bridge)
  と universe-polymorphic signature 一式、右枝を選択した場合の
  `FiniteModelLift.{u}`(固定有限 fixture から内部生成した named target
  package の canonical lift・exact component graph・supplied-lift
  reflection・反例の universe 移送)、lift 実構成のパラメトリック正例族
  (非可逆底射を含む)、
  compatible point cone による pointed 化手続きと
  `pointedPullback_isPullback`・pullback reindexing functor と
  functor law・随伴 `f_! ⊣ f^*`・canonical mate(natural
  transformation)・自然性・cleavage 非依存性・pullback での同型
  theorem・`packageProjection` の Beck–Chevalley exactness support
  theorem、`AuthoredBC2CellPresentation` / authored support 上の
  誘導比較の構成 / `MateCoherentRel` の定義と正負対(strict 正例+
  lax 負例 = authored 相対の canonicity obstruction 独立 theorem)
  と実在 `InReselectionOrbit` 全軌道の非消滅 theorem・軌道非自明性
  witness、
  `DiagnosticSourceFiberIncidence`((D) の southwest source-fiber
  入力資格 structure — southwest 特殊化は
  `BCDiagnosticSourceFiberIncidence`)と source edge 可逆性の導出
  (fiber isomorphism 構成)・schema no-go theorem
  (`no_universalBCDiagnosticSourceFiberIncidence` — 主張域限定の
  範囲根拠)、
  診断 base change 作用の構成一式(incidence 付き入力上の実 BC 二経路
  に対する無条件 (d1)–(d6): interpretation、endpoint 群準同型、
  transported data、`mapEdgeReselection`、`coherentAt_map`、一般および
  direct / via-base の vanishing 保存 theorem、診断比較写像)、旧必須
  反例の no-go theorem `no_bcDiagnosticQualifiedVanishingCounterexample`、
  初期 defect 非恒等・reselection 非恒等・source coherence を同時に
  発火させる named finite nonvacuity witness、
  貼り合わせ閉性 theorem・比較射整合 theorem・引き戻し側合成
  coherence・G-106 / G-109 coherence bridge、report
  `research/reports/G-110-aat-doctrine-fiber-product.md`。
- `target proof strategy`: F0 schema typing(presentation・条件
  述語・相対述語・regime の正確な Lean signature を elaboration の
  実フィードバック付きで固定する typing cycle — G-109 Cycle 1 の
  F0 tower typing と同型。本カードの schema 記述は設計意図の正本で
  あり、signature 水準の最終確定は F0 の proof obligation として
  per-cycle review が監査する。F0 は複数 obligation に分割してよく、
  確定 signature は tracking Issue に fixed head として記録する)
  -> K0 fiber product 構成と普遍性・
  退化しない witness -> K1 cartesian lift の disjunction 確定
  (存在定理または条件同定+反例) -> K2 pointed 化と
  Beck–Chevalley 比較射・正負の対 -> K3 診断 base change の無条件
  (d1)–(d6) 共変作用と named finite nonvacuity ->
  K4 閉性と整合。既存成果の利用 map: G-101 opcartesian 普遍性
  (比較射の生成)、G-106 の reselection / coherentizable 同値(K3 の
  proof DAG)と合成 coherence(K4 の素材)、G-109
  core pseudofunctor API(K2 の fiber functor / compositor)、
  `FiniteModel`(witness 計算)、スキーム射幾何ノートの fiber
  product 節(設計素材)。固定 statement と完了条件は本カードのみを
  正本とする。
- `target theorem completion criteria`: 全 artifact が sorry なしで
  `ResearchLean` に受理され、axiom / placeholder audit が clean で
  あること。下記 ledger の `discharge-required` を放電し、audit で
  provenance、proof-use、structure-field escape、route integrity を
  監査すること。**二段 review gate を分離して実行する**(正本 =
  target-goal-contract.md と `$target-theorem-loop` SKILL): 各実装
  PR は標準 fixed-head `$review-pr` gate を通過すること、および
  completion candidate では別工程として Lean / report / tracking
  Issue を同期し、final review packet を作り、`$math-lean-review` の
  4査読がすべて `No major findings` であること。有限 presentation 入力の
  `checkCart` と非定義的 soundness / completeness bridge theorem
  (`checkCart P = true ↔ H_cart (realizableHomOf P)`、`Iff.rfl` 放電禁止)を、
  `H_cart` で右枝を閉じた場合に artifact として含める(code の有限性から semantic 層の一般
  decidability は従わないため、決定可能性は checker+bridge で操作化
  する。左枝確定時に `H_cart` checker は要求しない)。同様に
  `FiniteModelLift` は右枝を閉じた場合だけ要求し、左枝確定時は
  `cartesianLiftNonexistence_isEmpty` による枝整合を監査して
  `not-applicable` とする。完遂時の
  記録は **「有限 presentation 付き(realization 像)底層射上の
  `H_cart`-admissible exact-bottom・diagnostic-covariant subcalculus
  達成」**に
  限定する
  (左枝で閉じた場合は `H_cart` 部を全域 lift と読み替える)。
  条件外・realization 像外を含む exact-bottom 全域の分類と読める
  表現を避ける。**Gr4 達成の記録は本カードでは行わない** — Gr4
  記録は capstone カード完遂時であり(program context)、本カードの
  report には subcalculus 達成と範囲根拠のみを記す(達成は exact
  底層の極限構造・base change 交換・診断共変性・閉性。量化域 =
  realization 付き入力(有限 presentable な底射・square)であり、
  (D) の診断 base change は source-fiber incidence 付き入力上である
  ことも併記する。範囲併記の様式は G-109 の Gr3 記録に従う)。
- `target premise discharge policy`: 入力(doctrine の射の対、package、
  base change **前**の診断の図式データ、(D) の source-fiber
  incidence)だけを残せる。引き戻し済み
  (transported)図式・診断比較写像の供給は放電と数えない。普遍性、
  退化しない witness、(B) の分岐確定、`H_cart` の十分性、
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
    不変な真部分 fiber witness(`Nonempty` pullback・canonical 射の
    非全射性・両射影の非同型性・compatible / incompatible pair)で
    退化と空虚充足を排除する(支える結論 = (A)。proof-use = (C) の
    square 供給)。
  - `compatible point cone(pointed 化の各頂点 instance 選択と
    ExtInstHom 整合)`: `direction-hypothesis`。入力資格。Doct
    square からの全域持ち上げは主張しない。
  - `H_cart の定義・資格条項 theorem 群・checker bridge`:
    `discharge-required`。定義(固定条件言語の syntax 項+
    `RealizableHom` 上の述語)、資格 theorem(同型不変性・
    constructor 相対の pullback-stable wide class)、非定義的 bridge は
    すべて本カードで建設する。原子式の
    許容定数・関係は探索前固定の structural vocabulary に限る
    (fixture 値・checker 出力・target 結果由来は禁止)。(支える
    結論 = (B)(C)。結論相当でない理由 = 条件は入力側語彙のみで
    立ち、十分性 theorem が別途結論へ橋を架ける)。
  - `個別 membership 証拠 h : H_cart f`:
    `direction-hypothesis`。十分性 theorem と (C)–(E) regime の仮定
    として理論に残る(必要十分化は frontier)。
  - `有限 presentation と toSemantic bridge(CartPresentation /
    BCPresentation と semantic 層の分離)`: `discharge-required`。
    condition bit・結論 certificate の埋め込みを禁じ、checker
    bridge と presentation 取替え不変性 theorem を非定義的 theorem
    として放電する。schema は field の役割・不変条件 (s1)–(s6)・
    閉性をカード本文で固定し、signature は F0 で確定して tracking
    Issue に fixed head として記録する。`CartConditionSyntax` constructor は
    カード本文で全列挙済み — F0 固定後の field / constructor 追加は
    改訂扱い。
  - `G-106 の AdmissibleTransportData 型 / API`: `ambient-boundary`。
    型と reviewed theorem の参照のみ(provenance = 上記 G-106 錨)。
  - `instance 水準の admissible data field(各 fixture の
    edgeStrong・twoCellBase・authored comparator)`:
    `direction-hypothesis`。base change 前入力の資格(役割 = (D) の
    入力と witness fixture の素材。proof-use = `edgeStrong`・
    authored comparator は (d3) 導出の入力、`twoCellBase` は source
    側診断(canonical comparator 経由の raw defect・named 実発火
    predicate)の入力 — 実 BC 経路の (d3) 導出では消費しない
    (incidence の恒等上 verticality が代替。(D) 本文と同一)。
    witness fixture では具体構成で非空性を放電する。結論相当でない
    理由 = base change 後の同種 field はここから供給せず (d3) で
    導出する)。
  - `DiagnosticSourceFiberIncidence((D) の southwest source-fiber
    入力資格)`: `direction-hypothesis`。入力資格。southwest 特殊化
    は `BCDiagnosticSourceFiberIncidence`(schema no-go theorem の
    量化域)。field は base change 前の source 幾何のみ(全 source
    package の southwest 載りと全 source edge の恒等上
    verticality)— edge の可逆性・target 側 field・比較
    certificate は含まず、可逆性は source `edgeStrong` と
    verticality から導出する(fiber isomorphism の構成)。任意
    ordinary interpretation からの普遍生成は主張しない(現行
    ordinary schema に対する不在は schema no-go theorem
    `no_universalBCDiagnosticSourceFiberIncidence` が確定する —
    主張域限定の範囲根拠)。full-domain 化は Gr4 完遂 gate 第一項へ
    移管する(program context)。
  - `AuthoredBC2CellPresentation(負例 lax fixture の raw field)`:
    `conclusion-equivalent-risk`(入力資格として残すが risk 種別で
    監査する)。schema はカード本文で固定済み(G-106 authored
    comparator 表と同形)、値の選択は proof obligation 選定時に固定
    (役割 = (C) 負例の入力幾何。proof-use = 2-cell family の生成
    入力。監査 artifact = 生成 family と両 canonical construction が
    raw field を直接返さないことの proof-use / structure-field
    escape audit、および `¬ MateCoherentRel` の presentation 取替え
    +実在 `InReselectionOrbit` 作用の全軌道非消滅 theorem+軌道非
    自明性 witness)。
  - `相対障害の orbit 不変性(実在 InReselectionOrbit への錨止め)`:
    `discharge-required`。負例の相対不一致が raw cochain への実在
    reselection 作用の全軌道で非消滅であること+軌道非自明性
    witness(新設 gauge の発明はしない — `EdgeReselection` は割当表
    に作用しないため、割当表側の不変性は僭称しない)。
  - `pointed ExtInst pullback bridge(pointedPullback_isPullback)`:
    `discharge-required`。compatible point cone と (A) の Source
    pullback・`source_eq` から生成する(`IsPullback` の入力供給は
    放電と数えない。支える結論 = (C) の mate 前提と `π₁`
    membership 導出)。
  - `FiniteModelLift(反例の universe 移送)`: **右枝選択時のみ**
    `discharge-required`。固定有限 fixture から named target package
    を内部生成し、その package の canonical universe lift、exact
    component graph、任意の supplied high `StrongCartesianLift` を
    実消費する low lift reflection、非存在証明の移送を任意 `u` で
    構成する(大域左枝の反証資格)。反例入力の任意 `targetPackage`、
    package reindexing certificate、reflection certificate の caller
    供給は放電と数えない。reflection producer は named positive
    fixture でも発火させ、empty elimination を排除する。生成 low
    input / package と `RightBranch.finiteCounterexample.nonexistence` の
    dependent endpoint 一致、lifted input / package、component graph、
    reflection、high `no_lift` は (B) で固定した同じ signature family の
    index を共有しなければならず、別 fixture 間の後付け対応は不可。
    左枝選択時は
    `cartesianLiftNonexistence_isEmpty` が右枝反例の不在を固定するため
    本行を `not-applicable` とする。任意 package の cross-universe
    exact reindexing は本行の数学的結論より強い補助 artifact なので
    completion obligation から除くが、左枝と右枝十分性にある固定
    carrier 内の全 target package 量化は維持する。
  - `CartesianRegime producer(cartesianRegimeOfDisjunction :
    DisjunctionArtifact -> ∀ U, CartesianRegime U)`:
    `discharge-required`。左枝 = 大域存在定理、右枝 = 一様 `H_cart`・
    十分性の instantiation(反例からは生成しない)。任意引数として
    供給される `CartesianRegime` は `conclusion-equivalent-risk` で
    あり放電と数えない。
  - `presentation 閉性 constructor(id / comp / pullback / pasting)
    と realization 整合 theorem`: `discharge-required`。(C) の
    `π₁^*` は `pullbackPresentation` 出力上で構成する(支える結論 =
    (B)→(C)→(E) の calculus 閉性)。
  - `G-106 / G-109 coherence bridge((E) の package 水準–fiber
    functor 水準整合)`: `discharge-required`。
    `transportAlong_comp_coherence` の実 proof-use をこの bridge
    経由で固定する。
  - `G-109 core pseudofunctor API(CoreFiber・
    coreFiberTransportFunctor・compositor / unitor)`:
    `ambient-boundary`。語彙 / API の参照のみ、改変しない。固定錨:
    CrossStageCoherence(G-109)= 実装 PR #4022–#4029(final
    reviewed head `b5ca4630`、implementation base `61bb4859`、完了
    記録 = Issue #4018 comment 5320617466)。中心 theorem への論理
    依存はない(消費箇所 = (C) fiber functor 経路・(E) 貼り合わせ)。
  - `(B) の disjunction 確定と H_cart の十分性・反例対`:
    `discharge-required`。条件は構成データ側の述語として立て、結論
    との同値・単一 fixture 等式型を禁じる。
  - `Beck–Chevalley 比較射と MateCoherentRel の正負対`:
    `discharge-required`。比較射(canonical mate)は普遍性から
    natural transformation として生成し、cleavage 非依存性 theorem を
    伴う。正負は同一相対述語 `MateCoherentRel` で対にする(負例 =
    authored 相対の canonicity obstruction 独立 theorem、`IsIso` の
    否定ではない)。
    comparator / holonomy の自由供給による破れは放電と数えない。
  - `pullback reindexing functor・随伴・functor law`:
    `discharge-required`。producer 由来の `f^*` 構成・id / comp
    law・`f_! ⊣ f^*`(unit / counit)・compositor / unitor(strong
    cartesian lift の存在だけからは従わない)。
  - `packageProjection の Beck–Chevalley exactness support theorem`:
    `discharge-required`。pullback square 上の mate 同型は
    bifibration 一般論から従わないため固有 support を建設する。
  - `点ごとの割当表からの誘導比較の構成(authored support 上)`:
    `discharge-required`。authored support(datum の載る pointed
    endpoint)上でのみ生成する(full-fiber natural family への
    canonical 拡張は主張しない)。
  - `診断 base change 共変作用と named finite nonvacuity`:
    `discharge-required`。(d1)–(d6) と診断比較写像は incidence 付き
    入力上の実 BC 二経路について無条件に G-101 普遍性と (A)–(C) から
    生成する。(d4) の mapped reselection、(d5) の coherence 保存、
    (d6) の vanishing 保存は同じ functorial action の proof DAG を
    消費する。(d1)–(d6) は pointed square が生成する実 BC 経路で放電し、
    square を消費しない汎用 total-category 作用の供給による放電は
    数えない)。引き戻し済み図式の
    入力供給、および base change 後の `edgeStrong` / `twoCellBase` /
    authored comparator・mapped reselection・coherence / vanishing
    certificate の再供給は放電と数えない(authored field の
    資格は base change 前の入力 presentation に限る — G-106 の
    authored field と生成 comparator の区別を維持する)。named finite
    witness は初期 defect 非恒等、source reselection 非恒等、source
    coherence、両 actual-route target coherence を同一 fixture 上で
    証明する。
  - `閉性と比較射整合`: `discharge-required`。G-106 coherence
    (`transportAlong_comp_coherence` 系)の消費は proof term として
    明示する。引き戻し側の合成 coherence は本カードで建設する
    (G-106 は押し出し側のみを供給する)。
- `target anti-weakening rule`: 結論相当の仮定(lift の存在、交換の
  同型性、診断共変性、診断比較写像・mapped reselection・coherence /
  vanishing certificate そのもの)を theorem argument、
  typeclass、structure field、certificate field へ移して成功扱い
  しない。`H_cart` は構成データ側の述語として立て、資格
  条項((B) の (i)–(v))と checker+bridge(completion
  criteria)で操作化する(G-107 の decider 前例)。結論(lift の
  存在)との論理同値、および単一 fixture との等式型述語を
  禁じる — 十分性は述語から結論への含意 theorem として別立てする。
  (C) の negative witness を comparator / holonomy の自由供給で作る
  構成、(C) の negative witness を省いた「正例のみの交換定理」、
  (D) の nonvacuity を恒等初期 defect または identity reselection だけで
  満たす構成、(B) 分岐 1 を強 cartesian より弱い lift
  概念で立てる構成は完了と数えない。右枝の `FiniteModelLift` を
  `CartesianLiftNonexistence.targetPackage` の任意供給、reindexing /
  reflection certificate の field、または empty elimination で立てる
  構成も完了と数えない。named input / package producer の computational
  body が `RightBranch.finiteCounterexample.nonexistence` の input / package
  fieldを返す accessorである構成、または別 fixture の reflectionを
  endpoint equalityなしに反例へ転用する構成も不可。`ambient-boundary`
  に残せるのは入力幾何だけである。
- `target route integrity gate`: 許容経路 — pullback・canonical
  mate・診断比較写像は入力と普遍性からのみ生成する。selected point
  cone・cleavage・有限 witness を証明後に target-fitting 選択しない
  (選択は proof obligation 選定時に fixture として固定する —
  負例 lax fixture の全 raw field も同時に固定する)。右枝の named
  target package も同じ時点で固定有限 fixture から生成し、canonical
  universe lift と reflection はその producer の出力だけを消費する。
  任意 package の cross-universe exact reindexing を G-110 または
  Gr4 の数学的 completion 証拠へ読み替えない。固定 carrier 内の
  全 package に対する lift 量化は別物として維持する。(C) の fiber
  functor / compositor 経路は G-109 core pseudofunctor API を消費し、
  G-101 からの再建はしない(経路の一意化)。
  authored comparator / lax datum は base change 前の入力に限り、
  base change 後の comparator は生成する。(D) の (d1)–(d6) は
  pointed square が生成する実 BC 経路(direct / via-base core-fiber
  functor)で放電し、square を消費しない汎用 total-category 作用の
  供給・relabel は禁止する。(d4) は endpoint group action から
  reselection を生成し、(d5) は mapped path 等式、(d6) は同じ
  coherent witness を proof term として消費する。source-fiber incidence は base change 前の
  source 幾何のみを記録する(edge 可逆性・target field・比較
  certificate の埋め込みは禁止)。有限 presentation は
  `toSemantic` realization を持ち、condition bit・結論 certificate
  を含まない。主張の量化域は realization 付き入力に限る(像外の
  semantic 入力への拡張主張をしない)。条件言語の許容定数・有限
  列挙集合・関係は探索前に固定した named structural vocabulary に
  限る — fixture 値・checker 出力・target 結果に由来する定数、
  および checker 由来 predicate を補助 lemma で包んで `H_cart` とする
  構成は禁止。base change 後 comparator は
  (d3) の生成式に従う。(E) は `transportAlong_comp_coherence` を
  G-106 / G-109 coherence bridge 経由の実 proof term で消費する。
  禁止経路 — 結論相当データの供給
  (anti-weakening rule)、checker の定義的 bridge(`Iff.rfl`)、
  base change 後の `edgeStrong` / `twoCellBase` / comparator / mapped
  reselection / coherence・vanishing certificate の再供給、自由供給
  2-cell による破れの作成。
- `target failure policy`: fail-closed を原則とする — 中心 conjunct
  の反証は `target-refuted`、statement の不足の発見は `goal-defect`
  で停止し、fixed target の変更はいずれも人間の別判断とする(自動
  weakening をしない)。個別分岐: (B) は二枝 disjunction の単一
  命題であり、どちらの枝の確定も成功である。左枝確定時は右枝専用の
  `FiniteModelLift` を停止理由にしない。右枝確定時に named target
  package の canonical universe lift・reflection・非存在移送を構成
  できない場合は `target-blocked` とする。左枝が反証され(非存在例が
  出る)かつ資格条項を満たす `H_cart` の同定に至らない場合も
  `target-blocked` で停止する。(A) の同型不変な真部分 fiber witness
  が存在し得ない(両射影が常に同型になる)ことが定理として示された
  場合、その退化定理を成果として `target-refuted` を宣言する
  (Boolean regime の零次元性の定理化として記録)。(C) の破れ
  witness が原理的に構成不能(固定比較等式が全ての資格入力で成立)
  と示された場合は、負例 conjunct の反証として `target-refuted` を
  宣言する。(D) の forward covariance を否定する qualified input が
  構成された場合、または named finite nonvacuity が原理的に不能
  (全 coherent source の初期 defect が恒等、あるいは coherence が
  identity reselection だけで成立)と theorem で示された場合は
  `target-refuted` とする。nonvacuity witness の構成が停滞し、反証も
  得られない場合は `target-blocked` とする。full-domain 作用と
  diagnostic conservativity は Gr4 gate 第一項・第五項の target で
  あり、本カードの停止理由にはしない。
