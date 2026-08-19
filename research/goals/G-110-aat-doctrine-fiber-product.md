# G-110-aat-doctrine-fiber-product — doctrine 圏の fiber product と base change

- `id`: `G-110-aat-doctrine-fiber-product`
- `status`: `active`
- `priority`: `high`
- `research mode`: `target-theorem`(mode 裁定済み 2026-08-18:
  (B)(D) は「条件同定+十分性+反例」の三点セットを基本形として
  target statement に固定する。(B) は型の決まった二枝 disjunction
  として単一命題で固定する(下記 (B))。`H_cart` / `H_bc` には資格
  条項(固定条件言語・結論非参照・同型不変性・閉性・非可逆入力を
  含むパラメトリック正例族・checker+非定義的 bridge)を課す
  (下記 (B)(D))。score-phase への切替は採らない —
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
  (E) のみ(合成 coherence、n1005 §4.3 の記載どおり)、G-109 へは
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
  finite-presentable subcalculus。Gr4 完遂 gate として (i) 全
  semantic exact-bottom への coverage 拡張、(ii) refinement 系統
  (`RefinementDoctrineHom` の圏化と refinement base change)、
  (iii) 上段(`GeomRead` / `ObProblem`)への base-change lift(Gr3
  段横断輸送への接続 bridge)、(iv) **IsIso 水準の Beck–Chevalley
  exchange-failure の存否決定**(全同型定理または反例 — 存否は
  **未決定の問い**であり、本 sector と refinement / 上段 regime を
  含む設定で決定する。n1005 §4.3 の
  exchange-failure 義務の移管先であり削除ではない)が残り、
  これらを束ねる **Gr4 capstone カード(後続、番号は起草時に
  割当)が Gr4 達成を記録する**(依存順: 本カード -> gate カード群 -> capstone。Gr3 を
  G-106+G-108+G-109 の三点セットで閉じた前例と同じ複数カード
  分割。n1001 §3.3 / §3.5 の relative stability 三系統)。
- `predecessor`: G-101(`Doct_U` / `ExtInst_U` / opcartesian 普遍性。
  完遂済み。`research/lean/ResearchLean/AG/AtomFoundation/` 配下、
  unported)、G-104 / G-107(「不変性+条件+反例」型の方法論資産。
  いずれも完遂済み)、G-106(閉性層 (E) の合成 coherence 素材。
  完遂済み = `target-theorem-proved`、2026-08-15。
  `research/lean/ResearchLean/AG/TransportCoherence/` 配下、unported。
  固定錨は下記 ledger 行)、G-109(core pseudofunctor API /
  coherence。完遂済み = `target-theorem-proved`、2026-08-18。
  `research/lean/ResearchLean/AG/CrossStageCoherence/` 配下、
  unported。中心 obstruction theorem へは非依存 — 固定錨は下記
  ledger 行)。先行考察はスキーム射幾何
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
  (B) cartesian lift の存在条件、(C) Beck–Chevalley exactness と
  canonicity obstruction、(D) 診断の base change 可換性の成立条件、
  (E) pullback square の貼り合わせ閉性。
  これで exact 底層(`Doct_U` / `ExtInst_U` / package 下層)の
  finite-presentable subcalculus が立つ — 本カードは **Gr4 の中間
  カード(第一手)**であり、Gr4 の達成記録は行わない(capstone は
  後続カード。program context)。
- `core tension`: 最大リスクは自明化である — Boolean regime の零次元性に
  より fiber product が集合論的交わりへ退化し、(C) が「集合論的
  Beck–Chevalley の再証明」に堕ちる可能性が明記されている(n1005
  §4.3)。したがって非自明性は (C) の canonicity obstruction
  (lax square 上の二経路比較射の不一致。IsIso 水準の
  exchange-failure の存否は Gr4 gate 第四項へ移管)と (D)(診断
  base change の成立条件同定)に置く。(B) の cartesian 方向の存在は開いた問いである — `atomEquiv`
  共役(`transportCompositionReading` 系の逆向き輸送)による無条件
  構成が成立する経路と、上位輸送の前進成分(`objectMap` /
  `operationMap` 等。可逆性を持たない)が障害になる経路の両方が
  生きており、どちらに転んでも定理として固定できる二枝
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
  構成**、(A) の非退化 witness を空 pullback で満たす構成、
  `H_cart` / `H_bc` を同型安全域(同型な底射・全脚同型の square で
  のみ発火する)述語で立てる構成、checker bridge を定義的
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
  昇格)、IsIso 水準の Beck–Chevalley exchange-failure の存否決定
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
     witness を**同型不変な形**で構成する — 有限 fixture 上で
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
     `DisjunctionArtifact.{u}` / `cartesianRegimeOfDisjunction.{u}`)
     で立てる。右枝の有限反例は universe 0 の `FiniteModel.carrier`
     上で構成し、任意 universe `u` への移送は
     **`FiniteModelLift.{u}`**(`ULift` 経由の carrier 持ち上げと
     非存在証明の移送 theorem)を discharge-required として供給する
     (暗黙の `u = 0` 限定はしない)。**二層の入力型と量化の
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
     結論符号化の排除)。**schema は本カードで閉じる — code 族を
     Lean signature 水準で固定する**: `CartPresentation U` の field
     は名前付き code 型 `DoctrineCode U`(source / target の有限
     presentation 対)・`SourceMapCode`(成分写像の有限表 —
     index / value 型は有限 code 型、宣言 support 外は default
     値)・`AtomPermCode`(有限 support の置換表、support 外は恒等
     — `AtomCarrier.Atom` が任意型でも有限 support 置換として
     decode できる)・`FiberAutCode`・`CoeffCode`(係数表)で全列挙
     する。各 code に decoder・code 水準の合成 / 逆元 /
     `DecidableEq` 等式判定・coverage(decode 像の宣言)・
     **soundness theorem**(decode 出力が `normalize_eq`・
     `extraction_iff`・`source_eq` を実際に満たす)を完全 signature
     で固定し、validated subtype の well-formedness 述語の内容
     (decoder の全域性条件)もカードで固定する。semantic payload・
     結論寄り certificate を leaf code に隠す構成は禁止(code の
     value 型は上記有限型のみ)。`PackageFiberAut` は semantic な
     `Aut` の subgroup であり有限 code ではないため、**割当表の値は
     `FiberAutCode`(有限 support 置換由来の生成元 code)に限る** —
     完全な semantic automorphism の任意入力は型で排除する。
     `BCConditionSyntax` の typed constructor も BC 固有 field
     (square 成分・compatible point data 成分・pre-BC 診断図式
     成分)の projection と operand 型を同様に列挙する(「(B) と
     同一」という参照だけでは閉じない)。`BCPresentation U` の **authored
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
     閉性)。条件 syntax の
     constructor は(field 値の等式原子・field 値の有限列挙集合への
     所属原子・presentation cell 上の有限全称原子・連言)の4種で
     全列挙する — 実装時の field / constructor 追加は改訂扱い。
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
     各 field の有限 code 値型、許容定数 = 単位元・恒等置換・零 /
     単位係数の named constants のみ、許容関係 = 値の等式と、
     presentation 自身の field から導出される有限集合への所属のみ。
     外部有限集合・fixture 値・checker 出力・target 結果に由来する
     定数の持ち込みは禁止し、checker 由来 predicate を補助 lemma で
     包んで `H` とする構成も禁止する(route gate と ledger の依存
     規則)。**以後の projection / constant / relation / 有限集合の
     追加は target 改訂扱いとする**。その上で、`H_cart` はある syntax 項の評価と bridge で結ばれる形で
     のみ立てる(任意述語は不可。condition bit・lift / 比較
     certificate の presentation への埋め込み、(d4)–(d6) の保存等式
     そのものの符号化、`check := if H then true else false` 型の
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
     負例は **有限表示部分圏**(対象有限に加え、hom の有限 code と
     全射 coverage を持つ finitely presented subcategory — 対象有限
     だけでは hom-set の有限性は従わない)に制限して立て、点ごとの
     割当表からこの部分圏上の component family を生成する theorem を
     discharge-required とし、全成分と全射の naturality を有限 code
     上の検査で固定する(有限表示部分圏上の**全 morphism
     naturality の typed validation interface** をあわせて固定
     する)。さらに**失敗の不変性を要求し、gauge を本カードの建設
     義務として固定する**: G-106 の `EdgeReselection` は
     edge-indexed で `DefectCochain` に作用し authored comparator を
     固定したままにする既存作用であり、**割当表への既存作用は存在
     しない**(既存作用への誤帰属をしない)。そこで **`CellGauge`
     を本カードで新設定義する** — gauge 群の定義・割当表への作用
     則・edge gauge(`EdgeReselection`)からの写像・component
     family への作用・**G-106 reselection orbit との比較 theorem**
     を全て discharge-required の target artifact とする(実装側で
     作用を選ばせない)。`¬ MateCoherent` は presentation 取替えと
     `CellGauge` 作用の**全軌道**で不変に成立しなければならず、
     **軌道の非自明性 witness**(軌道が一点でないことの concrete
     witness — 自明作用・一点軌道による空虚成立の排除)を負例
     fixture に義務化する。割当表の値は `FiberAutCode` に限る
     (schema 節 — semantic automorphism の任意入力の型排除)ため、
     central twist 等による `¬ MateCoherent` の入力符号化は code
     制限+全軌道全称+validation interface で三重に排除する。
     comparator の provenance は primitive lax-square geometry
     (base change 前 presentation の原子データ)からの生成に限る。
     canonical / direct comparison の依存元は
     replacement-invariance theorem と proof-use audit で拘束する
     (identity wrapper・合成を介した authored comparator の再包装も
     同 audit の対象)。比較射・natural family・期待等式の field は
     存在せず、target 固定後に schema を設計する余地を残さない。
     strict square は恒等 datum の特殊化とする。**正例と
     負例を同一の固定述語 `MateCoherent`**(unit / counit 経由の
     canonical mate と、(A) 普遍性・合成輸送経由の直接比較 —
     **双方とも固定済みの独立な canonical construction から生成**
     — の一致)**で対にする**: 正例 = strict pullback square での
     `MateCoherent`(および mate の同型性)、負例 = 具体 lax
     fixture 上での `¬ MateCoherent`。**負例は Beck–Chevalley 交換の
     `IsIso` 水準の破れではなく、comparison canonicity failure の
     独立 theorem として固定する** — `¬ MateCoherent` は正例側の
     `IsIso mate` と両立し得る別軸であり、その否定ではない。n1005
     §4.3 の「交換が破れる witness」は本カードでは canonicity 破れ
     として実現し、`IsIso` 水準の破れは構成可能性が未決定のため
     本カードでは主張しない(この n1005 からの差異を明記して固定
     する)。**IsIso 水準の exchange-failure の存否決定
     (全同型定理または反例)は Gr4 完遂 gate 第四項へ移管する**
     (program context。義務の削除ではない — ユーザー裁定
     2026-08-19)。負例 fixture の値の選択は
     proof obligation 選定時に固定し(schema は上記のとおりカードで
     固定済み)、以後の target-fitting 選択を route integrity gate で
     禁止する。生成 2-cell family と `MateCoherent` の両 canonical
     construction が raw field を直接返さないことは proof-use /
     structure-field escape audit で監査する。
     `IsIso` は正例側の追加 theorem であり負例の否定軸ではない
     (`¬ IsIso` の構成可能性は**未決定の問い**であり — 存否は Gr4
     完遂 gate 第四項で決定する — 負例形として義務化すると構成不能
     だった場合に (C) が反証で死ぬ設計リスクがあるため採らない。
     対の述語は一致述語で固定する)。canonical
     comparison を非自明な自己同型で twist した authored 比較の
     供給、および供給 datum から定義展開で従う不一致は放電と数え
     ない。
  4. **(D) 診断の base change 可換性**: まず**診断 base change 作用
     そのものを本カードで構成する** — 障害・defect の構成(**G-106
     語彙の raw defect / reselection orbit に一本化**。`J_A` defect
     profile への拡張は frontier)に対し、次を層別の Lean artifact
     として固定する。**組合せ層は固定する** — base change は組合せ
     presentation(vertex / edge / cell)を同一に保ち、semantic
     interpretation(endpoint package・lift・admissible data)にのみ
     作用する、と target を固定する(従属添字の reindex 問題を発生
     させない。組合せ層まで動かす一般 presentation hom は
     frontier)。その上で: (d1) 同一組合せ層上の interpretation
     引き戻しの構成、(d2) 各終点の `PackageFiberAut` 群準同型
     (endpoint ごと、identity cochain 保存)、(d3) transported
     admissible data の constructor — **target comparator の生成式を
     等式で固定する**:
     `transported.comparator c = φ_(target c) (source.comparator c)`
     (dependent cast 込み。`edgeStrong`・`twoCellBase` は theorem
     として**導出**する — base change 後の同種 field の再供給、
     および生成式に従わない「任意生成物」comparator は放電と数え
     ない)、(d4) pointwise raw defect 保存 theorem(**(d3) の生成式
     を proof term として実消費する**)、(d5) cochain map と
     reselection 作用の equivariance theorem、(d6) (d2)(d4)(d5) から
     導出する orbit map theorem(`InReselectionOrbit` の raw
     basepoint 整合に (d4) が必要)。**条件の消費箇所を固定する**: (d1)–(d3) と
     診断比較写像は無条件の構成、**(d4)–(d6) は `H_bc` を消費する
     条件付き theorem** とする(d4–d6 を無条件で採ると、単位元を
     保存する (d2) 準同型により source の vanishing witness がその
     まま target へ写り、vanishing 保存が無条件に従って負例
     conjunct と両立しない — 条件の消費箇所を theorem signature と
     ledger で固定する)。可換性等式の両辺を同一群に載せる診断比較
     写像は G-101 普遍性と (A)–(C) の構成から生成し、theorem
     argument・structure field・certificate として受け取らない。
     その上で、可換性が成立する条件 `H_bc` を同定し、**結論を
     vanishing 水準で固定した可換性定理**(`H_bc` 下で消滅
     (`TransportObstructionVanishes` 水準)が保存される — **proof
     DAG を固定する**: (d2) の identity cochain 保存・(d4)・(d5)・
     (d6) を全て proof term として消費して導出する。いずれかを迂回
     した導出は放電と数えない(proof-use audit の対象)。反射は
     frontier — G-109 effectivity 反射と同じ側)と、`H_bc` を満たさず保存が破れる反例(source 側
     vanishing が実発火し、target 側で消滅しない)を対で構成する。
     正例・負例とも source 側 vanishing の実発火を **named
     predicate** で要求する — 同一 fixture 上で
     `∃ c, initialRawDefectCochain data c ≠ 1`(初期 defect の非
     恒等)かつ、それを identity cochain へ移す実 reselection
     witness が存在すること(初期 defect が恒等で identity
     reselection が消滅を証明する安価な正例の排除)。raw 等式だけの
     最弱可換性では完了と数えず、(d1)–(d6) 全層の artifact を要求
     する。`H_bc` の入力は (B) と同じ二層分離(`BCPresentation U` /
     `BCSemanticInput U` / `toSemanticBC` — 述語は semantic 層、
     checker は presentation 層)で固定し、資格条項は (B) の
     (i)–(v) と同一(条件言語は `BCConditionSyntax`。閉性は
     **admissible-square calculus** — 恒等 square の包含と square の
     水平・垂直貼り合わせ閉性。(v) は非恒等かつ非可逆な脚を含む
     square 族 — 全脚同型でのみ発火する同型安全域述語は資格違反)。
     checker+bridge の規律も (B) と同一とする。
  5. **(E) 閉性**: pullback square の貼り合わせ(水平・垂直合成)が
     再び pullback square であり、(C) の比較射および (D) の診断比較
     写像が貼り合わせと整合することを証明する。押し出し側の水平
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
  まで。(D) の claim は「条件同定+十分性+反例」の三点セットで
  固定し、(B) は上記の二枝 disjunction 単一命題で固定する(右枝は
  同じ三点セット)。条件の必要十分化は frontier(G-107 の条件 C
  必要十分化と同じ後続ハント様式)。derived 化・係数 base change・
  bifibration の一般論は主張しない。
- `target proof artifacts`: fiber product の構成と普遍性 theorem、
  同型不変な真部分 fiber witness(`Nonempty` pullback・canonical 射
  の非全射性・両射影の非同型性・compatible / incompatible pair)、
  code 族(`DoctrineCode` / `SourceMapCode` / `AtomPermCode` /
  `FiberAutCode` / `CoeffCode`)と decoder・code 演算・coverage・
  soundness theorem、`CartPresentation U`(raw code / validated
  二段+`DecidableEq`)/ `CartSemanticInput U`(named structure)/
  `RealizableHom U` と `realizableHomOf` / `BCPresentation U` /
  `BCSemanticInput U` と `toSemantic` realization・realization
  soundness theorem、条件言語 `CartConditionSyntax` / `BCConditionSyntax`
  と評価器、presentation 取替え不変性 theorem、presentation 閉性
  constructor 4種(id / comp / pullback / pasting)と realization
  整合 theorem、`CartesianRegime U`(分岐結果の dependent package)
  と producer `cartesianRegimeOfDisjunction`、
  (B) の disjunction 確定 artifact(左枝: 無条件存在定理/右枝:
  `H_cart` の定義・資格条項 theorem 群(同型不変性・pullback-stable
  wide class)・十分性定理・非存在反例・checker+非定義的 bridge)
  と universe-polymorphic signature 一式+`FiniteModelLift.{u}`
  (反例の universe 移送)、lift 実構成のパラメトリック正例族
  (非可逆底射を含む)、
  compatible point cone による pointed 化手続きと
  `pointedPullback_isPullback`・pullback reindexing functor と
  functor law・随伴 `f_! ⊣ f^*`・canonical mate(natural
  transformation)・自然性・cleavage 非依存性・pullback での同型
  theorem・`packageProjection` の Beck–Chevalley exactness support
  theorem、`AuthoredBC2CellPresentation` / 有限表示部分圏上の
  component family 生成 theorem と生成 2-cell family /
  `MateCoherent` の定義と正負対(strict 正例+lax 負例 = canonicity
  failure 独立 theorem)と `CellGauge` の定義・作用則・edge gauge 写像・G-106 orbit 比較
  theorem・gauge 全軌道不変性 theorem と軌道非自明性 witness、
  naturality の typed validation interface、
  診断 base change 作用の構成一式((d1)–(d3) 無条件+(d4)–(d6)
  条件付きと診断比較写像・named 実発火 predicate)、`H_bc` の定義・
  資格条項 theorem 群(admissible-square calculus)・checker+非
  定義的 bridge・vanishing 保存定理・保存破れ反例(source 実発火)、
  貼り合わせ閉性 theorem・比較射整合 theorem・引き戻し側合成
  coherence・G-106 / G-109 coherence bridge、report
  `research/reports/G-110-aat-doctrine-fiber-product.md`。
- `target proof strategy`: K0 fiber product 構成と普遍性・退化しない
  witness -> K1 cartesian lift の disjunction 確定(存在定理または
  条件同定+反例) -> K2 pointed 化と Beck–Chevalley 比較射・正負の
  対 -> K3 診断 base change 作用の構成と条件同定・正負の対 ->
  K4 閉性と整合。既存成果の利用 map: G-101 opcartesian 普遍性
  (比較射の生成)、G-104 / G-107 の「不変性+条件+反例」構成法
  (K3 の方法論)、G-106 の合成 coherence(K4 の素材)、G-109
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
  4査読がすべて `No major findings` であること。有限 presentation 入力の checker
  関数と非定義的 soundness / completeness bridge theorem
  (`check P = true ↔ H (toSemantic P)`、`Iff.rfl` 放電禁止)を、
  `H_cart` は右枝を閉じた場合のみ、`H_bc` は (D) の条件同定に伴い、
  artifact として含める(`FiniteModel` の有限性から一般
  decidability は従わないため、決定可能性は checker+bridge で操作化
  する。左枝確定時に `H_cart` checker は要求しない)。完遂時の
  記録は **「finite-presentable(realization 像)上の `H_cart` /
  `H_bc`-admissible exact-bottom subcalculus 達成」**に限定する
  (左枝で閉じた場合は `H_cart` 部を全域 lift と読み替える)。
  条件外・realization 像外を含む exact-bottom 全域の分類と読める
  表現を避ける。**Gr4 達成の記録は本カードでは行わない** — Gr4
  記録は capstone カード完遂時であり(program context)、本カードの
  report には subcalculus 達成と範囲根拠のみを記す(達成は exact
  底層の極限構造・base change 交換・診断可換性・閉性。量化域 =
  realization 付き入力(有限 presentable な底射・square)である
  ことも併記する。範囲併記の様式は G-109 の Gr3 記録に従う)。
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
    不変な真部分 fiber witness(`Nonempty` pullback・canonical 射の
    非全射性・両射影の非同型性・compatible / incompatible pair)で
    退化と空虚充足を排除する(支える結論 = (A)。proof-use = (C) の
    square 供給)。
  - `compatible point cone(pointed 化の各頂点 instance 選択と
    ExtInstHom 整合)`: `direction-hypothesis`。入力資格。Doct
    square からの全域持ち上げは主張しない。
  - `H_cart / H_bc の定義・資格条項 theorem 群・checker bridge`:
    `discharge-required`。定義(固定条件言語の syntax 項+
    `RealizableHom` 上の述語)、資格 theorem(同型不変性・
    constructor 相対の pullback-stable class / admissible-square
    calculus)、非定義的 bridge はすべて本カードで建設する。原子式の
    許容定数・関係は探索前固定の structural vocabulary に限る
    (fixture 値・checker 出力・target 結果由来は禁止)。(支える
    結論 = (B)(C)(D)。結論相当でない理由 = 条件は入力側語彙のみで
    立ち、十分性 theorem が別途結論へ橋を架ける)。
  - `個別 membership 証拠 h : H_cart f / H_bc s`:
    `direction-hypothesis`。十分性 theorem と (C)–(E) regime の仮定
    として理論に残る(必要十分化は frontier)。
  - `有限 presentation と toSemantic bridge(CartPresentation /
    BCPresentation と semantic 層の分離)`: `discharge-required`。
    condition bit・結論 certificate の埋め込みを禁じ、checker
    bridge と presentation 取替え不変性 theorem を非定義的 theorem
    として放電する。schema(code 族の decoder・演算・coverage・soundness を含む)と
    条件 syntax constructor はカード本文で全列挙済み — 実装時の
    field / constructor 追加は改訂扱い。
  - `G-106 の AdmissibleTransportData 型 / API`: `ambient-boundary`。
    型と reviewed theorem の参照のみ(provenance = 上記 G-106 錨)。
  - `instance 水準の admissible data field(各 fixture の
    edgeStrong・twoCellBase・authored comparator)`:
    `direction-hypothesis`。base change 前入力の資格(役割 = (D) の
    入力と witness fixture の素材。proof-use = (d3) 導出の入力。
    witness fixture では具体構成で非空性を放電する。結論相当でない
    理由 = base change 後の同種 field はここから供給せず (d3) で
    導出する)。
  - `AuthoredBC2CellPresentation(負例 lax fixture の raw field)`:
    `conclusion-equivalent-risk`(入力資格として残すが risk 種別で
    監査する)。schema はカード本文で固定済み(G-106 authored
    comparator 表と同形)、値の選択は proof obligation 選定時に固定
    (役割 = (C) 負例の入力幾何。proof-use = 2-cell family の生成
    入力。監査 artifact = 生成 family と両 canonical construction が
    raw field を直接返さないことの proof-use / structure-field
    escape audit、および `¬ MateCoherent` の presentation 取替え+
    `CellGauge`(本カード新設)作用の全軌道不変性 theorem+軌道非
    自明性 witness)。
  - `CellGauge(割当表への gauge 作用)`: `discharge-required`。
    gauge 群の定義・作用則・edge gauge(`EdgeReselection`)からの
    写像・component family への作用・G-106 reselection orbit との
    比較 theorem(既存作用への誤帰属をしない — G-106 の
    `EdgeReselection` は割当表に作用しない)。
  - `pointed ExtInst pullback bridge(pointedPullback_isPullback)`:
    `discharge-required`。compatible point cone と (A) の Source
    pullback・`source_eq` から生成する(`IsPullback` の入力供給は
    放電と数えない。支える結論 = (C) の mate 前提と `π₁`
    membership 導出)。
  - `FiniteModelLift(反例の universe 移送)`: `discharge-required`。
    universe 0 の FiniteModel 反例を `ULift` 経由で任意 `u` へ移送し
    非存在証明を保つ(大域左枝の反証資格)。
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
  - `(B) の disjunction 確定と H_cart / H_bc の十分性・反例対`:
    `discharge-required`。条件は構成データ側の述語として立て、結論
    との同値・単一 fixture 等式型を禁じる。
  - `Beck–Chevalley 比較射と MateCoherent の正負対`:
    `discharge-required`。比較射(canonical mate)は普遍性から
    natural transformation として生成し、cleavage 非依存性 theorem を
    伴う。正負は同一述語 `MateCoherent` で対にする(負例 =
    canonicity failure の独立 theorem、`IsIso` の否定ではない)。
    comparator / holonomy の自由供給による破れは放電と数えない。
  - `pullback reindexing functor・随伴・functor law`:
    `discharge-required`。producer 由来の `f^*` 構成・id / comp
    law・`f_! ⊣ f^*`(unit / counit)・compositor / unitor(strong
    cartesian lift の存在だけからは従わない)。
  - `packageProjection の Beck–Chevalley exactness support theorem`:
    `discharge-required`。pullback square 上の mate 同型は
    bifibration 一般論から従わないため固有 support を建設する。
  - `点ごとの割当表からの component family 生成 theorem(有限表示
    部分圏上)`: `discharge-required`。hom の有限 code と coverage を
    型で固定した部分圏上でのみ生成する(full-fiber への canonical
    拡張は主張しない)。
  - `診断 base change 作用の構成`: `discharge-required`。(d1)–(d3)
    と診断比較写像は無条件に、**(d4)–(d6) は `H_bc` 消費の条件付き
    theorem として**、G-101 普遍性と (A)–(C) から生成する(条件の
    消費箇所は theorem signature に固定する)。引き戻し済み図式の
    入力供給、および base change 後の `edgeStrong` / `twoCellBase` /
    authored comparator の再供給は放電と数えない(authored field の
    資格は base change 前の入力 presentation に限る — G-106 の
    authored field と生成 comparator の区別を維持する)。
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
- `target route integrity gate`: 許容経路 — pullback・canonical
  mate・診断比較写像は入力と普遍性からのみ生成する。selected point
  cone・cleavage・有限 witness を証明後に target-fitting 選択しない
  (選択は proof obligation 選定時に fixture として固定する —
  負例 lax fixture の全 raw field も同時に固定する)。(C) の fiber
  functor / compositor 経路は G-109 core pseudofunctor API を消費し、
  G-101 からの再建はしない(経路の一意化)。
  authored comparator / lax datum は base change 前の入力に限り、
  base change 後の comparator は生成する。有限 presentation は
  `toSemantic` realization を持ち、condition bit・結論 certificate
  を含まない。主張の量化域は realization 付き入力に限る(像外の
  semantic 入力への拡張主張をしない)。条件言語の許容定数・有限
  列挙集合・関係は探索前に固定した named structural vocabulary に
  限る — fixture 値・checker 出力・target 結果に由来する定数、
  および checker 由来 predicate を補助 lemma で包んで `H` とする
  構成は禁止。base change 後 comparator は
  (d3) の生成式に従う。(E) は `transportAlong_comp_coherence` を
  G-106 / G-109 coherence bridge 経由の実 proof term で消費する。
  禁止経路 — 結論相当データの供給
  (anti-weakening rule)、checker の定義的 bridge(`Iff.rfl`)、
  base change 後の `edgeStrong` / `twoCellBase` / comparator の
  再供給、自由供給 2-cell による破れの作成。
- `target failure policy`: fail-closed を原則とする — 中心 conjunct
  の反証は `target-refuted`、statement の不足の発見は `goal-defect`
  で停止し、fixed target の変更はいずれも人間の別判断とする(自動
  weakening をしない)。個別分岐: (B) は二枝 disjunction の単一
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
