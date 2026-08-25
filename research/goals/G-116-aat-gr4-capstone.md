# G-116-aat-gr4-capstone — exchange-failure 存否決定と Gr4 達成記録

- `id`: `G-116-aat-gr4-capstone`
- `status`: `draft`
- `priority`: `high`
- `research mode`: `target-theorem`
- `program context`: Gr4 完遂 gate 第四項(O12)と達成記録(O19)の
  担当カード = **Gr4 capstone**(設計の source note は n1007 §3–§8)。
  依存は G-111〜G-115 の全カード — 存否決定の量化域は G-114 / G-115 が
  供給する regime 型から組み、達成記録は全カードの帰趨確定を突合する。
  したがって**昇格は G-111〜G-115 の全帰趨確定後にのみ行う**。上流の
  いずれの statement 改訂も本カードへ伝播する(達成記録の突合対象と
  範囲併記の内容が動くため)。**本カードの下記義務台帳が Gr4 完遂義務
  の正本である**(n1007 は source note)。
- `predecessor`: G-110(完遂済み。MateCoherentRel 正負対と pullback
  square 上の mate exactness = 既決の正例。固定錨は G-111 カード
  ledger と同一)、G-111〜G-115(draft — 完遂後に各 final head を固定
  して昇格する)。
- `tracking issue`: 未起票(active 昇格時に起票)
- `source note`: [docs/note/n1007_aat_sakura_gr4_completion_design.md](../../docs/note/n1007_aat_sakura_gr4_completion_design.md)(§3 義務台帳の設計元、§7 成立条件、§8 達成階梯対応表)、
  [docs/note/n1005_aat_semantic_geometry_route_after_g107.md](../../docs/note/n1005_aat_semantic_geometry_route_after_g107.md)(§4.3 exchange-failure 義務)、
  [G-110 カード](G-110-aat-doctrine-fiber-product.md)(gate (iv)・(C) 移管文)
- `research aim`: 二つ。(1) G-110 が未決定の問いとして残した IsIso
  水準の Beck–Chevalley exchange-failure の存否を、refinement / 上段
  regime を含む設定で決定する。(2) Gr4 完遂義務の台帳(下記 O1–O20)を
  先行カードの成果と突合し、Gr4 達成を範囲併記付きで記録する。
- `core tension`: 存否決定の核心は既決と未決の分界にある — G-110
  sector の pullback square 上の mate 同型は証明済みの正例であり、
  未決なのは authored datum 付き lax square と refinement / 上段
  regime 側である。既決正例の再包装や vacuous な新 regime で「全同型」
  枝を安価に放電する経路が最大の敵になる。また量化域そのものが
  G-114 / G-115 の成果物形式から組めるかは供給契約に依存する — 組め
  ない場合は本カードで新設せず、gate (iv) の regime の意味の裁定へ
  差し戻す(単責務規律)。
- `rival`: Beck–Chevalley 条件の古典理論(成立条件の一般論)。差は
  「具体 doctrine 塔の refinement / 上段 regime 込みの設定で、存否
  未決だった exchange-failure に決定を与え、階梯全体の達成を検証可能な
  台帳突合として記録する」点に置く。
- `claim boundary`: 量化域は G-110 sector+G-114 供給の refinement
  regime 型+G-115 供給の上段 regime 型(供給された成果物形式のみ —
  本カードは regime を新設建設しない)。下記域外リストの全項目は主張
  しない。達成記録は theorem ではなく completion criteria+report 側の
  義務である(O19 を target theorem の conjunct にしない)。
- `capability categories`: exchange-law、decision、counterexample、
  unification。
- `threshold policy`: SCORE は使わない。runtime state は tracking Issue に
  置き、固定 statement と completion criteria だけで完了判定する。
- `portfolio constraint`: どちらの枝で確定する場合も、退化しない実
  witness(全同型枝: 非恒等・非可逆成分を含む regime 上の mate 同型の
  実証明/反例枝: 非退化な ¬IsIso witness)を要求する。達成記録は台帳
  突合を欠いた宣言だけでは完了と数えない。
- `phase boundary criteria`: 未証明なら `target-proof-checkpoint`、反証
  なら `target-refuted`、全完了条件と final review を満たした場合だけ
  `target-theorem-proved` とする。
- `reward rubric`: `not-applicable (target-theorem mode)`。各 cycle は
  proof obligation delta で評価する。
- `dullness filter`: 次を弾く。既決正例(pullback square 上の mate
  同型)の再包装による正枝放電、退化 square(成分恒等・診断恒零)や
  vacuous な新 regime での放電、負例枝 witness を既決域に置く構成、
  達成記録が台帳突合を欠いて宣言だけで立つ構成。
- `frontier`: exchange-failure の分類の精密化(どの regime 成分が破れを
  生むかの帰属)、係数 base change カードへの接続点、SAKURA 論文
  (n1007 §8)の Main 素材化。

- `target theorem`: **Beck–Chevalley Exchange Exactness Decision
  Theorem**(O12)。G-110〜G-115 の設定の上で、**「全同型定理」または
  「¬IsIso の具体反例」の二枝 disjunction 単一命題**を証明する:
  - 量化域 = G-110 sector+G-114 が供給する refinement regime 型+
    G-115 が供給する上段 regime 型。**authored datum 付き lax square を
    含める**。
  - 既決 / 未決の分界: G-110 sector の pullback square 上の mate 同型は
    証明済みの正例であり、存否の未決部分は lax square と新 regime 側に
    ある。負例枝 witness の居住域をそこに限定する。
  - 排他性は反例が供給し、網羅性(両枝の少なくとも一方が成立)は主張
    しない(両枝とも閉じない場合は `target-blocked`)。
  - 上段 regime の第二 universe(`GeomReadCategory` は二 universe)は
    端点固定とし、方式は F0 で確定する。
- `target theorem boundary`: Lean 置き場所は
  `research/lean/ResearchLean/AG/DoctrineFiberProduct/` 配下の新
  module。G-110〜G-115 の reviewed module は参照のみ。regime の新設
  建設はしない(供給契約から組めない場合は起票前に gate (iv) の
  regime の意味の裁定へ差し戻す)。完了面は O12 の決定+O19 の記録
  まで。
- `target proof artifacts`: 二枝 disjunction 確定 artifact(全同型
  theorem または ¬IsIso witness)、量化域の regime 組成 artifact
  (G-114 / G-115 成果物の消費)、非退化 witness、report
  `research/reports/G-116-aat-gr4-capstone.md`(**達成階梯対応表**を
  含む — 下記 completion criteria)。
- `target proof strategy`: F0 typing(regime 合成の signature と第二
  universe の端点固定)→ K0 量化域の組成 → K1 lax square 域の mate
  挙動の探索 → K2 枝の確定(全同型証明または反例構成)→ K3 台帳突合
  と達成記録。既存成果の利用 map: G-110 `MateCoherentRel` 正負対と
  TargetTheorem の mate exactness(既決正例の分界)、G-114 refinement
  regime 型、G-115 上段 regime 型。
- `target theorem completion criteria`: 全 artifact が sorry なしで
  `ResearchLean` に受理され、axiom / placeholder audit が clean である
  こと。下記 ledger の `discharge-required` を放電し、audit で
  provenance、proof-use、structure-field escape、route integrity を監査
  すること。二段 review gate(各実装 PR の標準 fixed-head `$review-pr`
  +completion 時の独立 `$math-lean-review` 4査読全 `No major
  findings`)を通過すること(正本 = target-goal-contract.md)。
  **さらに、達成記録(O19)を completion の必須義務とする**:
  1. **義務台帳の突合**: 下記「Gr4 完遂義務台帳」の O1–O11・O13–O18・
     O20 を先行カード(G-111〜G-115)の fixed head・review 錨と突合
     し、O12 を本カードの確定で充足する。
  2. **解釈規約**: Gr4 達成とは gate 全項の帰趨が定理で確定している
     ことをいう(正枝である必要はない — 二枝 disjunction 義務は
     どちらの枝の確定も帰趨確定)。ただし記録の表現は exact-bottom
     全域の分類と読める形を避け、確定枝を全て併記する。O6・O7・O12 が
     すべて反例枝で確定した場合の記録の見出し語は、枝が出揃った時点の
     ユーザー裁定とする。
  3. **範囲併記**: coverage の到達段(第一段 / 第二段)、O6 / O7 /
     O12・G-113 (i)・G-114 (b) の確定枝、下記域外リストを併記する。
  4. **達成階梯対応表**: 各段 Gr0–Gr4 ↔ theorem package ↔ Lean 宣言錨 ↔
     記録正本の所在 ↔ 範囲限定、の5列を report 成果物として作成する。
     Gr0–Gr1 は statement 化段(達成 = 文書固定、n1001 §3.5)、Gr2 =
     G-101(遡及記載)、Gr3 = G-109 記録、Gr4 = 本カード記録。

**Gr4 完遂義務台帳(正本)**:

| id | 義務 | 担当 |
|---|---|---|
| O1 | global / indexed base-change schema の建設(全 `ExtractionInstance` 上の base 作用) | G-111 |
| O2 | 各固定 carrier 内の全 package に対する cocartesian 保存 lift | G-111 |
| O3 | 実 BC 経路との制限比較(incidence 資格付き部分域上の一致) | G-111 |
| O4 | (D) の full-domain 化 = source-fiber incidence 資格の解除(indexed 版 (d1)–(d6)) | G-111 |
| O5 | coverage 拡張第一段(有限 carrier・有限 Source 上の同型までの coverage) | G-112 |
| O6 | coverage 拡張第二段(sector 全域の帰趨決定 — 二枝) | G-112 |
| O7 | 全域 lift の realization 資格外への帰趨決定 — 二枝 | G-112 |
| O8 | refinement 射の圏化 | G-114 |
| O9 | refinement base change の帰趨決定と refinement 側 regime 型の建設 — 二枝 | G-114 |
| O10 | `GeomRead` 段への base-change lift+Gr3 接続 bridge+上段 regime 型の建設 | G-115 |
| O11 | `ObProblem` 段への base-change lift = 構成された障害類の base-change naturality(semantic adequacy 条件込み) | G-115 |
| O12 | IsIso 水準 exchange-failure の存否決定 — 二枝 | G-116 |
| O13 | `DiagnosticConservative` の定義と構造的生成 class の固定+十分性 theorem | G-113 |
| O14 | target obstruction vanishing → source vanishing の反射 theorem(class 上) | G-113 |
| O15 | source reselection orbit の検出 theorem | G-113 |
| O16 | class 外で非零 obstruction が消える有限 witness | G-113 |
| O17 | 診断 class の恒等・水平・垂直貼り合わせ閉性 | G-113 |
| O18 | `Full` + `Faithful` 十分条件候補の statement 固定と生成 class との関係決定 | G-113 |
| O19 | Gr4 達成の範囲併記記録(義務台帳との突合+達成階梯対応表込み) | G-116 |
| O20 | pointwise raw-defect reflection の分類(cochain 値水準 — O14 とは別 statement) | G-113 |

**域外リスト(Gr4 に含めない隣接義務 — 範囲併記の対象)**:

- carrier change(carrier `U` を動かす主張。底の取り替えとは別軸)
- 任意 package の cross-universe exact reindexing(O2 の固定 carrier 内
  量化とは別物)
- (D) の `J_A` defect profile 枝(係数 base change カードとの接続点)
- G-109 (G) の core 押し出し `p` に沿う effectivity の保存・反射
  (O14 / O20 の診断反射とは方向が異なる別物)
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
    exactness)`: `ambient-boundary`。参照のみ(固定錨は G-111 カード
    ledger と同一)。既決正例の分界の根拠。
  - `G-111〜G-115 の完遂成果`: `ambient-boundary`(各カード完遂後に
    final head を固定して昇格する — 昇格条件。台帳突合の対象)。
  - `量化域の regime 組成`: `discharge-required`(G-114 / G-115 供給の
    成果物形式のみから組む。新設建設は不可)。
  - `二枝 disjunction 確定`: `discharge-required`。
  - `非退化 witness`: `discharge-required`。
  - `達成記録(台帳突合・範囲併記・達成階梯対応表)`:
    `discharge-required`(completion criteria 1–4)。
- `target route integrity gate`: 量化域は供給された regime 型からのみ
  組む。負例枝 witness は lax square・新 regime 域に限定し、既決域に
  置かない。witness fixture は proof obligation 選定時に固定する。禁止
  経路 — regime の新設建設、既決正例の再包装、台帳突合を欠く達成
  宣言。
- `target anti-weakening rule`: mate の同型性・破れ・regime の組成
  可能性を theorem argument、typeclass、structure field、certificate
  field へ移して成功扱いしない。`ambient-boundary` に残せるのは入力
  幾何と先行カードの reviewed 成果だけである。
- `target failure policy`: 両枝とも閉じない場合は `target-blocked` で
  あり、**Gr4 は未達のまま**(達成記録だけ先行させない)。量化域が
  供給契約から組めない場合は昇格前に gate (iv) の regime の意味の
  裁定へ差し戻す(`goal-defect` 扱い)。fixed target の変更は人間の別
  判断とする。
