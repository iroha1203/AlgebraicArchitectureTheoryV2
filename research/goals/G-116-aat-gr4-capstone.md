# G-116-aat-gr4-capstone — exchange-failure 存否決定と Gr4 達成記録

- `id`: `G-116-aat-gr4-capstone`
- `status`: `draft`
- `priority`: `high`
- `research mode`: `target-theorem`
- `program context`: Gr4 完遂 gate 第四項(O12)と達成記録(O19)の
  担当カード = **Gr4 capstone**(設計の source note は n1007 §3–§8)。
  依存は G-111〜G-115 の全カード — 存否決定の量化域は G-114 / G-115 が
  供給する active mate-bearing context から組み、達成記録は全カードの
  帰趨確定を突合する。
  したがって**昇格は G-111〜G-115 の全帰趨確定後にのみ行う**。上流の
  いずれの statement 改訂も本カードへ伝播する(達成記録の突合対象と
  範囲併記の内容が動くため)。依存する reviewed カード(G-110)の
  statement が改訂された場合も、本カードは draft へ差し戻して再固定
  する(伝播規定)。**本カードの下記義務台帳が Gr4 完遂義務の正本で
  ある**(n1007 は source note)。
- `predecessor`: G-110(完遂済み。MateCoherentRel 正負対と pullback
  square 上の mate exactness = 既決の正例。固定錨は下記 ledger 行)、
  G-111〜G-115(完遂後に各 final head を固定して錨に載せる)。
- `tracking issue`: 未起票(active 昇格時に起票)
- `source note`: [docs/note/n1007_aat_sakura_gr4_completion_design.md](../../docs/note/n1007_aat_sakura_gr4_completion_design.md)(§3 義務台帳の設計元、§7 成立条件、§8 達成階梯対応表)、
  [docs/note/n1005_aat_semantic_geometry_route_after_g107.md](../../docs/note/n1005_aat_semantic_geometry_route_after_g107.md)(§4.3 exchange-failure 義務)、
  [G-110 カード](G-110-aat-doctrine-fiber-product.md)(gate (iv)・(C) 移管文)
- `research aim`: 二つ。(1) G-110 が未決定の問いとして残した IsIso
  水準の Beck–Chevalley exchange-failure の存否を、実際に canonical
  mate が定義された refinement / 上段 context で決定する。(2) Gr4
  完遂義務の台帳(下記 O1–O20)を
  先行カードの成果と突合し、Gr4 達成を範囲併記付きで記録する。
- `core tension`: 存否決定の核心は既決と未決の分界にある — G-110
  sector の pullback square 上の mate 同型は証明済みの正例であり、
  未決なのは authored datum 付き lax square と active refinement /
  上段 context 側である。既決正例の再包装や empty-fiber context を
  混ぜた「全同型」
  枝を放電する経路が最大リスクである — authored datum は可逆値
  (`PackageFiberAut`)を取るため、lax 成分の IsIso が既決 mate と
  可逆 twist の合成の系として従う可能性があり、その場合は独立の発見
  ではなく系として計上しなければならない。また量化域そのものが
  G-114 / G-115 の成果物形式から組めるかは供給契約に依存する — 組め
  ない場合は本カードで新設せず、gate (iv) の regime の意味の裁定へ
  差し戻す(単責務規律)。
- `rival`: Beck–Chevalley 条件の古典理論(成立条件の一般論)。差は
  「具体 doctrine 塔の refinement / 上段 regime 込みの設定で、存否
  未決だった exchange-failure に決定を与え、階梯全体の達成を検証可能な
  台帳突合として記録する」点に置く。
- `claim boundary`: 固定した一般 carrier `U` の上で語る。係数は動かさ
  ない。終対象・絶対積は導入しない。量化域は、mate を伴う G-110
  sector、G-114 の `ActiveRefinementBCContext`、G-115 の active
  upper-stage regime からなる `Gr4ExchangeContext` とする。本カードは
  regime や mate を新設しない。G-114 の forward-only / inactive
  refinement は O12 の外に置くが、O19 でその帰趨と理由を記録する。
  下記域外リストの全項目は主張しない。達成記録は
  theorem ではなく completion criteria+report 側の義務である(O19 を
  target theorem の conjunct にしない)。
- `capability categories`: exchange-law、decision、counterexample、
  unification。
- `threshold policy`: SCORE は使わない。runtime state は tracking Issue に
  置き、固定 statement と completion criteria だけで完了判定する。
- `portfolio constraint`: どちらの枝で確定する場合も、**量化域の各成分
  (sector の lax square 域・active refinement・active upper stage)
  ごとに**非退化発火 witness を要求する。空 fiber による空虚性は
  放電と数えない。lax 成分の
  IsIso が既決 mate+可逆 twist の系として従う場合は独立放電と数えず
  系として記録する(計上規律)。達成記録は台帳突合を欠いた宣言だけ
  では完了と数えない。
- `phase boundary criteria`: 未証明なら `target-proof-checkpoint`、反証
  なら `target-refuted`、全完了条件と final review を満たした場合だけ
  `target-theorem-proved` とする。
- `reward rubric`: `not-applicable (target-theorem mode)`。各 cycle は
  proof obligation delta で評価する。
- `dullness filter`: 次を弾く。既決正例(pullback square 上の mate
  同型)の再包装による正枝放電、退化 square(成分恒等・診断恒零)や
  empty-fiber context での放電、**twist 系で従う lax 成分の IsIso を
  独立の発見として計上する構成**、負例枝 witness を既決域に置く
  構成、達成記録が台帳突合を欠いて宣言だけで立つ構成。
- `frontier`: exchange-failure の分類の精密化(どの regime 成分が破れを
  生むかの帰属)、係数 base change カードへの接続点、SAKURA 論文
  (n1007 §8)の Main 素材化。

- `target theorem`: **Beck–Chevalley Exchange Exactness Decision
  Theorem**(O12)。G-110〜G-115 の設定の上で、**「全同型定理」または
  「¬IsIso の具体反例」の二枝 disjunction 単一命題**を証明する:
  - `Gr4ExchangeContext` を、mate を伴う G-110 sector、G-114
    `ActiveRefinementBCContext`、G-115 active upper-stage regime の
    tagged sum として定義する。量化域はこの型に固定し、**authored
    datum 付き lax square を含める**。
  - 既決 / 未決の分界: G-110 sector の pullback square 上の mate 同型は
    証明済みの正例であり、存否の未決部分は lax square と active
    refinement / upper-stage context 側にある。負例枝 witness の居住域を
    そこに限定する。
  - **成分別の実質**: 全同型枝で確定する場合、量化域の各成分ごとに
    非退化発火 witness を要求する。inactive / forward-only refinement
    は mate が未定義なので O12 の反例でも正例でもなく、O19 の
    domain-classification 行で記録する。lax 成分が既決 mate+可逆 twist
    の系で従う場合は系として
    記録する(portfolio constraint の計上規律)。
  - 排他性は反例が供給し、網羅性(両枝の少なくとも一方が成立)は主張
    しない(両枝とも閉じない場合は `target-blocked`)。二枝の payload
    は G-110 `DisjunctionArtifact` 様式の構造化 artifact で立て、
    payload の caller 供給を放電と数えない。
  - 上段 regime の第二 universe(`GeomReadCategory` は二 universe)は
    端点固定とし、方式は F0 で確定する。
- `target theorem boundary`: Lean 置き場所は
  `research/lean/ResearchLean/AG/DoctrineFiberProduct/` 配下の新
  module。G-110〜G-115 の reviewed module は参照のみ。regime の新設
  建設はしない(供給契約から組めない場合は昇格前に gate (iv) の
  regime の意味の裁定へ差し戻す)。完了面は O12 の決定+O19 の記録
  まで。
- `target proof artifacts`: 二枝 disjunction 確定 artifact(全同型
  theorem または ¬IsIso witness、構造化 payload)、量化域の regime
  組成 artifact(G-114 / G-115 成果物の消費と O19 除外記録)、active
  成分ごとの非退化 witness、report
  `research/reports/G-116-aat-gr4-capstone.md`(**達成階梯対応表**を
  含む — 下記 completion criteria)。
- `target proof strategy`: F0 typing(regime 合成の signature・payload
  構造・第二 universe の端点固定)→ K0 量化域の組成と除外記録 →
  K1 lax square 域の mate 挙動の探索(twist 系判定を含む)→ K2 枝の
  確定(全同型証明または反例構成)→ K3 台帳突合と達成記録。既存成果の
  利用 map: G-110 `MateCoherentRel` 正負対と TargetTheorem の mate
  exactness(既決正例の分界)、G-114
  `ActiveRefinementBCContext`、G-115 active upper-stage regime。
- `target theorem completion criteria`: 全 artifact が sorry なしで
  `ResearchLean` に受理され、axiom / placeholder audit が clean で
  あること。下記 ledger の `discharge-required` を放電し、audit で
  provenance、proof-use、structure-field escape、route integrity を監査
  すること。二段 review gate(各実装 PR の標準 fixed-head
  `$review-pr`、completion candidate での Lean / report / tracking
  Issue 同期と final review packet 作成、独立 `$math-lean-review`
  4査読全 `No major findings`)を通過すること(正本 =
  target-goal-contract.md)。
  **さらに、達成記録(O19)を completion の必須義務とする**:
  1. **義務台帳の突合**: 下記「Gr4 完遂義務台帳」の O1–O11・O13–O18・
     O20 を先行カード(G-111〜G-115)の fixed head・review 錨と突合
     し、O12 を本カードの確定で充足する。**義務は移管、または人間承認
     revision でのみ動かす。revision 時は旧義務の disposition を下記履歴
     台帳に残し、削除しない**。O19 は現行義務の fixed head に加え、履歴
     台帳の refuted / strengthened / superseded disposition も突合する
     (台帳改訂の規律)。
  2. **解釈規約**: Gr4 達成とは gate 全項の帰趨が定理で確定している
     ことをいう(正枝である必要はない — 二枝 disjunction 義務は
     どちらの枝の確定も帰趨確定)。ただし記録の表現は exact-bottom
     全域の分類と読める形を避け、確定枝を全て併記する。O6・O12 が
     ともに反例枝で確定した場合の記録の見出し語は、枝が出揃った時点の
     ユーザー裁定とする(O7 は semantic-global 正枝で確定済み —
     実装実査 2026-08-26、反例枝を持たない)。
     G-114 については、raw refinement 全域の forward square、realized
     support 上の reverse regime、actual package 上の active mate、
     その外側の forward-only / inactive 分類が揃って初めて帰趨確定と
     数える。
  3. **範囲併記**: coverage の到達段(第一段 / 第二段)、O6 /
     O12・G-113 の transport equivalence / base-`IsIso` 非依存性と
     converse 反証・
     G-114 の forward / reverse / inactive 三層分類、O7 の
     semantic-global 正枝
     fixed statement(`strongCartesianLiftOfTarget` の reviewed 宣言・
     wrapper・proof-use audit の記録)、量化域からの除外成分、
     **任意の独立 raw square family は自動的には coherent diagnostic
     assembly をなさないという G-111 の分類負枝**、下記域外リストを
     併記する。
  4. **達成階梯対応表**: 各段 Gr0–Gr4 ↔ theorem package ↔ Lean 宣言錨 ↔
     記録正本の所在 ↔ 範囲限定、の5列を report 成果物として作成する。
     Gr0–Gr1 は statement 化段(達成 = 文書固定、n1001 §3.5)、Gr2 =
     G-101(遡及記載)、Gr3 = G-109 記録、Gr4 = 本カード記録。

**Gr4 完遂義務台帳(正本)**:

| id | 義務 | 担当 |
|---|---|---|
| O1 | indexed base action(base / total / fiber)の建設+identity / composition / pasting API(全 `ExtractionInstance` 上の base 作用) | G-111 |
| O2 | cocartesian-preserving lifted action+canonical lift compatibility(各固定 carrier 内) | G-111 |
| O3 | 実 BC 経路との制限比較 C0–C3(incidence 資格付き部分域上で G-110 の direct / via-base 経路と一致+三角形 coherence) | G-111 |
| O4 | declared base relation を持つ coherent indexed base-diagram morphism 全域での incidence-independent relative diagnostic assembly と (d1)–(d6)、一頂点の全 right legs に対する uniform liftability iff `Epi`、finite-family support 上の vertexwise-epi sufficiency producer、coherent domain の非 epi 正例、独立の nontrivial diagnostic witness、有限 non-liftable 負例 | G-111 |
| O5 | coverage 拡張第一段(`U.Atom` 有限・source / target 両 endpoint の `Source` 有限の上の arrow 圏同型までの coverage) | G-112 |
| O6 | coverage 拡張第二段(sector 全域の帰趨決定 — 二枝、負枝は資格条項付き特徴付け) | G-112 |
| O7 | 全域 lift = semantic-global strong cartesian lift の正枝確定(G-110 reviewed 宣言 `strongCartesianLiftOfTarget` の Gr4 正本 wrapper 化・proof-use audit・記録。completion artifact に semantic-global cleavage / reindexing functor と unitor・compositor・triangle・pentagon coherence(G-112 (e))を含む。実装実査 2026-08-26、n1001 §3.5 の忠実転写) | G-112 |
| O8 | refinement 射の圏化(`RefinementDoctrineHom` を射とする圏構造と `Doct_U ⥤ Refin_U` 比較 functor) | G-114 |
| O9 | refinement の unconditional forward square、realized-locus extraction reflection iff reverse regime、active forward-only / reverse witness、inactive empty-fiber 分類、`ActiveRefinementBCContext` の供給 | G-114 |
| O10 | `GeomRead` 段への base-change lift+Gr3 接続 bridge+上段 regime 型の建設 | G-115 |
| O11 | `ObProblem` 段への base-change lift = 構成された障害類の base-change naturality(semantic adequacy 条件込み) | G-115 |
| O12 | IsIso 水準 exchange-failure の存否決定(`Gr4ExchangeContext` の actual mate-bearing sector / active refinement / active upper stage — 二枝) | G-116 |
| O13 | G-111 `indexedFiberAction` と G-112 semantic-global reindexing の vertexwise quasi-inverse、unit / counit、endpoint equivalence | G-113 |
| O14 | obstruction vanishing iff と全 hom 上の `DiagnosticConservative` / no-killing corollary | G-113 |
| O15 | reselection equivalence と `InReselectionOrbit` membership iff | G-113 |
| O16 | 非恒等 `¬ IsIso` base component、非恒等 defect / reselection を持ち、診断同値性が非退化発火する有限 witness | G-113 |
| O17 | 診断輸送 equivalence の identity・垂直合成・path-square・水平貼り合わせ coherence | G-113 |
| O18 | `Full` / `Faithful` / `EssentiallySurjective` producer と explicit equivalence。全 hom / vertex で base `IsIso` 非依存、`IsIso` base corollary、finite `¬ IsIso` witness による converse 反証 | G-113 |
| O19 | Gr4 達成の範囲併記記録(義務台帳との突合+達成階梯対応表込み) | G-116 |
| O20 | raw-defect cochain transport の explicit equivalence と `rawDefectCochain` commuting、pointwise iff | G-113 |

**台帳注記**:

**G-113 revision 1 義務 disposition(履歴台帳)**:

| id | revision 1 義務 | disposition |
|---|---|---|
| O13-r1 | `DiagnosticConservative` と構造的生成 class・十分性 | class syntax、normalization completeness、生成 class は proved。class 上の十分性は `diagnosticConservative_all` により全 hom theorem へ strengthened。revision 1 全体は O16-r1 により `target-refuted`、現行 O13 は人間承認 revision 2 で置換。これら歴史 artifact は revision 2 completion には数えない |
| O14-r1 | class 上の target vanishing → source vanishing | `diagnosticConservative_all` により全 hom へ強化済み。revision 2 O14 の iff の一方向として保持 |
| O15-r1 | source reselection orbit の検出 | revision 1 では未完。人間承認 revision 2 の reselection / membership iff に superseded |
| O16-r1 | class 外で非零 obstruction が零へ消える witness | `no_diagnosticConservativityCounterexample` により refuted。これが revision 1 の target-level 停止理由 |
| O17-r1 | 診断 class の恒等・水平・垂直貼り合わせ閉性 | revision 1 では未完。人間承認 revision 2 の equivalence coherence に superseded |
| O18-r1 | 生成 class と `Full` + `Faithful` 候補の関係決定 | revision 1 では未完。人間承認 revision 2 の一般 categorical decomposition に superseded |
| O20-r1 | class 相対の pointwise raw-defect reflection 分類 | revision 1 では未完。人間承認 revision 2 の explicit cochain equivalence に superseded |

- G-110 (D) の gate 第五項移管3項は O20(raw-defect cochain
  equivalence)・O15(reselection orbit exactness)・O14(vanishing iff)に
  対応する — 移管義務の消滅なしをここで固定する。
- n1005 §4.3 (D) の「情報損失の分類」のうち、obstruction が非零から零へ
  消える枝は revision 1 の no-counterexample theorem で反証された。一般の
  injectivity、Full / Faithful、cochain / orbit equivalence はそこからは従わず、
  G-110 の package-projection 固有 ambidextrous theorem を追加根拠とする
  revision 2 の新しい未証明 target である。O13 が輸送 equivalence、O16 が
  非 `IsIso` base 上での非退化発火を担う。
- **universe 注記**: O1・O2・O6・O12 の universe 契約は F0 typing
  cycle で Lean の宇宙割当と型突合した上で確定する(O7 は G-110
  reviewed 宣言の universe 契約を継承し、fallback 対象外)。symbolic universe で
  型不能と判明した場合は枝条件付き・endpoint 固定の契約へ**再表現**する
  (義務の削除ではない — G-110 (B) の枝条件付き universe 移送契約を
  設計前例とする)。

**域外リスト(Gr4 に含めない隣接義務 — 範囲併記の対象)**:

- carrier change(carrier `U` を動かす主張。底の取り替えとは別軸)
- 任意 package の cross-universe exact reindexing(O2 の固定 carrier 内
  量化とは別物)
- (D) の `J_A` defect profile 枝(係数 base change カードとの接続点)
- G-109 (G) の core 押し出し `p` に沿う effectivity の保存・反射
  (O14 / O20 の診断 exactness とは方向が異なる別物)
- derived fiber product・bifibration 一般論・係数 base change(ℚ→R)・
  `ObProblem` 段の class 構成の変更・nerve / cover 接続
- 候補8(係数忠実性)・候補13(comonadicity)の引き受け先裁定(係数
  base change カード起草時の裁定事項)

- `target premise discharge policy`: 入力(regime・square・witness
  fixture)だけを残せる。mate の同型性・破れの結論相当データの供給は
  放電と数えない。達成記録は先行カードの reviewed 成果の突合であり、
  未完遂義務の宣言的充足を認めない。
- `target material premise ledger`:
  - `G-110 reviewed artifact(MateCoherentRel 正負対・mate
    exactness)`: `ambient-boundary`。参照のみ、改変しない。固定錨:
    DoctrineFiberProduct = 完了 PR #4153(final head `a1471483`、
    merge `315a2537`)(支える結論 = 既決正例の分界。結論相当でない
    理由 = 既証明の環境であり、本カードの未決部分の決定はここから
    従わない)。
  - `G-111〜G-115 の完遂成果`: `ambient-boundary`(各カード完遂後に
    final head を固定して昇格する — 昇格条件。台帳突合の対象。支える
    結論 = 量化域の組成と O19)。
  - `Gr4ExchangeContext の組成`: `discharge-required`(支える結論 =
    O12 の設定。discharge artifact = G-114 / G-115 の active
    mate-bearing 成果物と G-110 sector のみから組む tagged sum。
    inactive / forward-only の除外は O19 に記録し、新設 mate は不可)。
  - `二枝 disjunction 確定`: `discharge-required`(支える結論 = O12。
    discharge artifact = 構造化 payload の全同型 theorem または
    ¬IsIso witness)。
  - `active 成分別の非退化 witness`: `discharge-required`
    (支える結論 = 決定の実質。empty component は O19 の
    domain-classification にのみ記録し、この行を放電しない。twist 系の
    計上規律を含む)。
  - `達成記録(台帳突合・範囲併記・達成階梯対応表)`:
    `discharge-required`(completion criteria 1–4)。
- `target route integrity gate`: 量化域は供給された actual
  mate-bearing context からのみ組む。負例枝 witness は lax square・
  active refinement / upper-stage 域に限定し、既決域や inactive 域に
  置かない。witness fixture は proof obligation 選定時に固定する。禁止
  経路 — regime の新設建設、既決正例の再包装、twist 系の独立計上、
  台帳突合を欠く達成宣言、payload の caller 供給。
- `target anti-weakening rule`: mate の同型性・破れ・regime の組成
  可能性を theorem argument、typeclass、structure field、certificate
  field へ移して成功扱いしない。`ambient-boundary` に残せるのは入力
  幾何と、先行カードの reviewed 成果(環境扱い — 語彙正本規則)だけで
  ある。
- `target failure policy`: fail-closed を原則とする。両枝とも閉じない
  場合は `target-blocked` であり、**Gr4 は未達のまま**(達成記録だけ
  先行させない)。量化域が供給契約から組めない場合は昇格前に gate
  (iv) の regime の意味の裁定へ差し戻す(`goal-defect` 扱い)。**F0 で
  組成の型不能が判明した場合も `goal-defect` で停止する**(自動
  weakening をしない)。witness の停滞は `target-blocked`。fixed
  target の変更は人間の別判断とする。
