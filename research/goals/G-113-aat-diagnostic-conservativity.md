# G-113-aat-diagnostic-conservativity — 診断保守性・反射・orbit exactness の分類

- `id`: `G-113-aat-diagnostic-conservativity`
- `status`: `draft`
- `priority`: `high`
- `research mode`: `target-theorem`
- `program context`: Gr4 完遂 gate 第五項の担当カード(担当義務 =
  O13–O18・O20。義務台帳の正本は G-116 カード、設計の source note は
  n1007 §3–§5)。G-111(順方向 = 共変・経路整合)に対する逆方向カード
  であり、G-111 の schema 型を再定義せず量化域として消費する(n1007
  §5 判定線1)。依存は G-111。**新設語彙の命名権**:
  `DiagnosticConservative` の命名は本カード専属。G-111 の statement
  改訂は本カードの draft 差し戻しへ伝播し、本カードの改訂は G-116 の
  達成記録要件へ伝播する。依存する reviewed カード(G-110 / G-106)の
  statement が改訂された場合、本カードは draft へ差し戻して再固定する
  (伝播規定)。
- `predecessor`: G-110(完遂済み。無条件 forward covariance
  (`transportObstructionVanishes_map` 系)と
  `no_bcDiagnosticQualifiedVanishingCounterexample`。固定錨は下記
  ledger 行)、G-111(indexed schema — 昇格順で先行)、G-106
  (reselection orbit 語彙)、G-109(core pseudofunctor API —
  `CoreFiber` を型に含む seed を消費する)。
- `tracking issue`: 未起票(active 昇格時に起票)
- `source note`: [docs/note/n1007_aat_sakura_gr4_completion_design.md](../../docs/note/n1007_aat_sakura_gr4_completion_design.md)(§3 義務台帳、§4 G-113、§5 判定線1・3)、
  [docs/note/n1005_aat_semantic_geometry_route_after_g107.md](../../docs/note/n1005_aat_semantic_geometry_route_after_g107.md)(§4.3 (D) の独立 gate 文)、
  [G-110 カード](G-110-aat-doctrine-fiber-product.md)(gate (v)・(D) 移管文)
- `research aim`: G-110 / G-111 で診断は base change に沿って順方向に
  無条件に運ばれる。本カードは逆方向を分類する — どの base 作用が診断を
  **保守**するか(target で消えたら source でも消えている)、どの作用が
  reselection orbit を検出するか、そして保守性が破れる作用の実在。
  `DiagnosticConservative` を定義し、それを構造的に生成する class を
  固定し、反射・検出・破れ・閉性を定理化する。「診断が base change で
  何を失うか」の分類であり、Gr4 gate 第五項の全体である。
- `core tension`: 順方向の無条件性(G-110 で証明済み)は逆方向を含意
  しない — source 非零かつ target 零は forward covariance と両立する
  ため、逆方向の非含意そのものは (f) の class 外 witness が実在証明と
  して供給する。ここに保守性が class の理論になる根拠がある。最大
  リスクは二つ。class を「conservative と同値」の述語で立てる結論の
  埋め込み、および class が空・退化でも反射・検出が vacuous に立つ
  こと(class 内の非自明成員の実在義務で防ぐ)。また本カードの反射
  (O14・O20)は G-109 の段射影 `p` に沿う effectivity 反射(域外)と
  方向が異なる別物であり、この分界を statement に明記する(n1007 §5
  判定線3)。
- `rival`: conservative functor・descent の一般論。差は「診断障害
  (defect cochain・reselection orbit)水準の保守性を、構造的生成
  class・破れの witness・貼り合わせ閉性込みで Lean で固定する」点に
  置く。
- `claim boundary`: 固定した一般 carrier `U`、G-111 の full-domain
  indexed action 上で語る(schema 型は G-111 の宣言を参照のみ)。係数は
  動かさない。終対象・絶対積は導入しない。G-106 系 raw defect /
  reselection 語彙に一本化(`J_A` defect profile 枝は域外)。carrier
  change・係数 base change・段射影方向の effectivity 反射は域外
  (G-116 カードの域外リストを継承)。
- `capability categories`: classification、conservativity、reflection、
  counterexample、closure。
- `threshold policy`: SCORE は使わない。runtime state は tracking Issue に
  置き、固定 statement と completion criteria だけで完了判定する。
- `portfolio constraint`: 生成 class と十分性だけで完了扱いしない。
  反射・orbit 検出・cochain 値反射(O20)・class 外の破れ witness・
  class 内の非自明発火 witness・閉性の全面に Lean artifact を要求する。
- `phase boundary criteria`: 未証明なら `target-proof-checkpoint`、反証
  なら `target-refuted`、全完了条件と final review を満たした場合だけ
  `target-theorem-proved` とする。
- `reward rubric`: `not-applicable (target-theorem mode)`。各 cycle は
  proof obligation delta で評価する。
- `dullness filter`: 次を弾く。class を結論(conservative)と同値な
  述語または単一 fixture 等式型で立てる構成、反射を全成分可逆の
  fixture だけで発火させる構成、class 外 witness を空診断図式で満たす
  構成、class 内 witness を恒等 defect・恒等 reselection で満たす
  構成、**O20 の反例枝を自明成分の退化 cochain 設定で満たす構成**、
  閉性が恒等成分で vacuous に立つ構成、**(i) の候補を生成 class の
  条件の構文的再ラベルで立てて関係決定を自明化する構成**、G-110 の
  forward covariance の再証明を成果と数える構成。
- `frontier`: 生成 class の必要十分化(最大 class theorem)、`p` 方向
  effectivity 反射との合成観察(域外との接続点)、`J_A` 枝(域外の
  まま)、係数 base change カードとの接続点。

- `target theorem`: **Diagnostic Conservativity Classification
  Theorem**。G-111 の indexed schema の上で:
  1. **(a) `DiagnosticConservative` の定義**: full-domain indexed
     action 上の述語として新設定義する(Lean に既存宣言は無い —
     本カードの建設義務)。
  2. **(b) 生成 class と十分性**: `DiagnosticConservative` を構造的に
     生成する class を探索前固定の構造条件で定義し(結論参照の禁止 —
     G-110 `H_cart` 資格条項の様式)、class membership → conservative
     の十分性 theorem を証明する。
  3. **(c) 反射 theorem**: class 上で target obstruction vanishing →
     source vanishing を証明する。逆方向が順方向無条件性から従わない
     ことは (f) の class 外 witness が実在証明として固定する(この
     紐付けを statement に明記する)。
  4. **(d) orbit 検出 theorem**: source reselection orbit の非自明性が
     target で検出されることを class 上で証明する。
  5. **(e) pointwise raw-defect reflection の分類(O20)**: cochain 値
     水準の反射が成立する class の固定または反例を、(c) の orbit /
     vanishing 水準とは別 statement として証明する。反例枝の witness
     には非恒等 defect・非恒等 reselection の非退化条件を課す。
  6. **(f) class 外 witness**: class に入らない作用で非零 obstruction が
     消える有限 witness を構成する(保守性の破れの実在 = class 制限の
     非空虚性、かつ (c) の逆方向非含意の実在証明)。
  7. **(g) class 内 named nonvacuity witness**: 非恒等 defect・非恒等
     reselection・非可逆成分を含む class 成員上で反射・検出が実発火
     する有限 witness を構成する。
  8. **(h) 閉性**: 診断 class の恒等・水平・垂直貼り合わせ閉性を証明
     する。
  9. **(i) `Full` + `Faithful` 候補の決定**: 生成診断部分圏上の
     `Full` + `Faithful` 十分条件候補の statement を固定し、生成 class
     との関係(含意・同値・反例)を決定する。候補は Full+Faithful への
     十分性が独立に立つ形に限り、生成 class の条件と構文的に同一の
     候補は不可(関係決定の自明化の排除)。
- `target theorem boundary`: Lean 置き場所は
  `research/lean/ResearchLean/AG/DoctrineFiberProduct/` 配下の新
  module。G-111 / G-110 / G-109 / G-106 の reviewed module は参照
  のみ。完了面は (a)–(i) まで。順方向共変性(G-111)・coverage
  (G-112)・段射影方向の effectivity 反射(域外)は主張しない。
- `target proof artifacts`: `DiagnosticConservative` 定義、生成 class
  定義と資格 theorem 群(結論非参照・同型不変性・閉性)、十分性
  theorem、反射 theorem(O14)、orbit 検出 theorem(O15)、cochain 値
  反射の分類 artifact(O20、反例枝は非退化条件付き)、class 外破れ
  witness(O16)、class 内 named nonvacuity witness、貼り合わせ閉性
  theorem(O17)、`Full` + `Faithful` 決定 artifact(O18)、report
  `research/reports/G-113-aat-diagnostic-conservativity.md`。
- `target proof strategy`: F0 typing(`DiagnosticConservative` と生成
  class の signature、G-111 schema 型への接続)→ K0 定義と生成 class →
  K1 十分性と反射 → K2 orbit 検出と O20 → K3 witness 対(class 外の
  破れ+class 内の実発火)→ K4 閉性と (i) 決定。既存成果の利用 map:
  G-111 indexed schema(量化域)、`InReselectionOrbit`(orbit 語彙)、
  `CoreFiberFunctorDefectCochain` 系(fiberwise 作用の seed 型)。
- `target theorem completion criteria`: 全 artifact が sorry なしで
  `ResearchLean` に受理され、axiom / placeholder audit が clean で
  あること。下記 ledger の `discharge-required` を放電し、audit で
  provenance、proof-use、structure-field escape、route integrity を監査
  すること。二段 review gate(各実装 PR の標準 fixed-head
  `$review-pr`、completion candidate での Lean / report / tracking
  Issue 同期と final review packet 作成、独立 `$math-lean-review`
  4査読全 `No major findings`)を通過すること(正本 =
  target-goal-contract.md)。
- `target premise discharge policy`: 入力(indexed action・witness
  fixture)だけを残せる。保守性・反射・検出の結論相当データの供給は
  放電と数えない。
- `target material premise ledger`:
  - `G-110 reviewed artifact`: `ambient-boundary`。参照のみ、改変
    しない。固定錨: DoctrineFiberProduct = 完了 PR #4153(final head
    `a1471483`、merge `315a2537`)(支える結論 = 順方向無条件性との
    分界と (f) の対照。結論相当でない理由 = 既証明の環境)。
  - `G-111 indexed schema`: `ambient-boundary`(完遂後に final head を
    固定して昇格する — 昇格条件。schema 型の再定義禁止。支える結論 =
    全 conjunct の量化域)。
  - `G-106 InReselectionOrbit 系`: `ambient-boundary`(固定錨は G-110
    カード ledger の G-106 錨を継承。proof-use = orbit 検出 (d) の
    語彙)。
  - `G-109 core pseudofunctor API(CoreFiber)`: `ambient-boundary`
    (固定錨は G-110 カード ledger の G-109 錨を継承。proof-use =
    fiberwise seed 型の消費)。
  - `DiagnosticConservative 定義と生成 class`: `discharge-required`
    (支える結論 = (a)(b)。discharge artifact = 定義+資格 theorem 群+
    十分性。結論相当でない理由 = class は構造条件のみで立ち、保守性は
    十分性 theorem が結ぶ)。
  - `反射・orbit 検出・O20 分類`: `discharge-required`(支える結論 =
    (c)(d)(e)。proof-use = (f) witness との紐付けを含む)。
  - `witness 対(class 外の破れ+class 内の実発火)`:
    `discharge-required`(支える結論 = (f)(g)。discharge artifact =
    非退化条件付き有限 fixture 証明)。
  - `貼り合わせ閉性`: `discharge-required`(支える結論 = (h))。
  - `Full + Faithful 決定`: `discharge-required`(支える結論 = (i)。
    どちらの決定でも成功)。
- `target route integrity gate`: 生成 class は探索前固定の構造条件で
  立て、fixture 値・結論由来の条件を持ち込まない。witness fixture は
  proof obligation 選定時に固定する。class 候補・(i) 候補の証明後の
  差し替えをしない。禁止経路 — 結論の埋め込み(class = conservative
  同値述語)、可逆 fixture のみの反射発火、候補の構文的再ラベル、
  証明後の target-fitting 選択。
- `target anti-weakening rule`: 保守性・反射・検出を theorem
  argument、typeclass、structure field、certificate field へ移して成功
  扱いしない。`ambient-boundary` に残せるのは入力幾何だけである。
- `target failure policy`: fail-closed を原則とする。(c)(d)(e) の反証は
  `target-refuted`。(f) が原理的に不能(保守性が full-domain で無条件
  成立し class 制限が空虚)と定理化された場合も、その定理を成果として
  `target-refuted` とする。(i) は決定がどちらでも成功。(a) の型不能・
  statement 不足は `goal-defect`。**生成 class 候補が十分性で落ちた
  場合の候補差し替えは改訂扱い(人間裁定)であり、loop 内の再選定を
  しない**。witness の停滞は `target-blocked`。fixed target の変更は
  人間の別判断とする。
