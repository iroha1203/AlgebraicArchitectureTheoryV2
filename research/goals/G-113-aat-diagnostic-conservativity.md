# G-113-aat-diagnostic-conservativity — 診断保守性・反射・orbit exactness の分類

- `id`: `G-113-aat-diagnostic-conservativity`
- `status`: `active`
- `priority`: `high`
- `research mode`: `target-theorem`
- `program context`: Gr4 完遂 gate 第五項の担当カード(担当義務 =
  O13–O18・O20。義務台帳の正本は G-116 カード、設計の source note は
  n1007 §3–§5)。G-111(完遂済み — 順方向 = coherent diagnostic
  assembly・経路整合)に対する逆方向カードであり、G-111 の
  `IndexedBaseDiagramHom` 上の diagnostic transport API を再定義せず
  量化域として消費する(n1007
  §5 判定線1)。依存は G-111。**新設語彙の命名権**:
  `DiagnosticConservative` の命名は本カード専属。本カードの改訂は
  G-116 の達成記録要件へ伝播する。依存する reviewed カード(G-111 /
  G-110 / G-109 / G-106)の statement が改訂された場合、本カードは
  draft へ差し戻して再固定する(伝播規定)。report は (c)(d)(e) の
  class 限定の範囲を G-116 の範囲併記へ突合可能な形で記録する
  (供給契約)。
  **head 分離**: F0 は次の fixed head を分けて tracking Issue に記録
  する — language head(閉じた syntax・evaluator)、class-term head
  ((b) の生成 class term)、O20-term head((e) の固定 term)、
  (i) candidate head(`Full` + `Faithful` 候補 statement)。条件言語
  そのものの設計を F0 以後へ持ち込むことは `goal-defect` とする
  (F0 で行うのはカード constructor 表の Lean 転写であり、新語彙の
  発明ではない)。
  **候補遷移規則(三層状態、G-112 様式)**: term 候補列と順序
  ((b)・(e)・(i) の各 head)は F0 で事前登録し、各 head は先頭候補の
  機械的採用とする(K 段の証明結果を選定に使わない)。状態は三層で
  記録する — candidate state(tracking Issue の local state)、cycle
  result(loop 契約の正式語彙 = `proof-obligation-discharged` /
  `blocker-fixed` / `proof-checkpoint` / `rejected`)、GOAL state
  (`target-proof-checkpoint` / `target-refuted` / `target-blocked`)。
  資格条項の反例固定・十分性の反例固定・candidate class 上の
  (c)(d) の反例固定 = candidate state を refuted とし、再利用可能な
  refutation artifact を固定して cycle result = `blocker-fixed`、
  GOAL state = `target-proof-checkpoint`、次 = 事前登録列の次候補と
  する — **候補の反証は固定 target の反証ではない**(`target-refuted`
  は candidate の取り方に依存しない、固定 target statement 自体への
  反例・不能定理化に限る)。(e) の O20-term は資格条項の反例固定で
  のみ candidate refuted とする — 固定 term 上の cochain 反射の破れは
  反例枝の確定(成功)であり、遷移トリガーではない。候補遷移時は
  class 相対 artifact((b)–(h) の candidate 依存部分と (f)(g)
  witness)を新 term で再放電する — witness の再選定は遷移後の proof
  obligation 選定として行い、証明後の target-fitting 選択には当たら
  ない。完了時の全 conjunct は同一の final class-term に対して立つ
  ことを completion audit で確認する。事前登録列には、既存の反証
  artifact がそのまま適用できる外延同値 term を置かない。proof
  未完成・反例なし = cycle result `proof-checkpoint`(候補は破棄
  しない)。
  同一 blocker が2 cycle 継続 = `target-blocked`。次候補への移行は
  事前登録列の次項、または人間承認による。proof 結果を見た新 term の
  発明は target 改訂(人間裁定)であり、証明サイクル内では行わない。
- `predecessor`: G-110(完遂済み。無条件 forward covariance
  (`transportObstructionVanishes_map` 系)と
  `no_bcDiagnosticQualifiedVanishingCounterexample`。固定錨は下記
  ledger 行)、G-111(完遂済み `target-theorem-proved`。coherent
  diagnostic assembly (d1)–(d6)・`IndexedBaseDiagram` /
  `IndexedBaseDiagramHom`・pointwise indexed calculus。固定錨は下記
  ledger 行)、G-106
  (reselection orbit 語彙)、G-109(core pseudofunctor API —
  `CoreFiber` を型に含む seed を消費する)。
- `tracking issue`: 未起票(昇格 PR マージ後に起票し、本行を Issue
  番号へ更新する)
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
- `claim boundary`: 固定した一般 carrier `U`、G-111 の
  `IndexedBaseDiagramHom` の declared base relation に相対して生成された
  diagnostic transport
  について語る(diagram / hom 型と順方向 API は G-111 の宣言を参照
  のみ)。target base relation / path naturality は G-111 から継承する
  direction hypothesis であり、保守性の結論相当 certificate ではない。
  任意の独立 raw square family は量化域に含めない。係数は
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
  Theorem**。G-111 の coherent diagnostic transport の上で:
  1. **(a) `DiagnosticConservative` の定義**:
     `IndexedBaseDiagramHom` 上の述語として新設定義する(Lean に
     既存宣言は無い — 本カードの建設義務)。量化形は
     **per-interpretation 形**で固定する — 当該 hom 上の全 source
     diagnostic interpretation について、生成 target transport の
     obstruction vanishing が成立するならその interpretation の
     source vanishing が成立する。interpretation を含意の外側で全量化
     する集約形(「全 interpretation で target 消滅」を前件に取る形)
     は不可 — 前件の vacuous 化により保守性が無内容に成立するため。
  2. **(b) 生成 class と十分性**: `DiagnosticConservative` を構造的に
     生成する class を、**閉じた条件言語(constructor 完全列挙)**の
     term で定義し、class membership → conservative の十分性 theorem を
     証明する。constructor は次の3つに限る(operand なし・数値定数
     なし・集合定数なし)—
     `vertexwiseSourceMapInjective`(全 vertex の transport index の
     `sourceMap` が単射)、
     `edgewiseSquarePullback`(全 generating edge の生成 edge square が
     `ExtInst_U` の pullback square)、
     `conjunction`(結合子はこれのみ)。評価意味は constructor ごとに
     `Prop` 水準で固定する(`Function.Injective` / `IsPullback` 系。
     決定手続き・cardinality 比較は用いない)。categorical `Mono`
     constructor は採用しない(`atomEquiv` が常に可逆である
     `ExtInst_U` では `sourceMap` 単射の外延的言い換えとなる見込みで、
     独立候補にならないため)。
     diagnostic 語彙(defect / reselection / coherence / vanishing /
     conservativity)・生成 transport の値・fixture 値・arbitrary
     `Prop` callback・external constant・存在量化(Skolem 化を含む)は
     syntax に持ち込めない — この禁止は syntax の constructor /
     operand 水準の規則であり、constructor の固定評価意味
     (`IsPullback` の `Prop` 内容)には適用しない。constructor・
     結合子・量化形の追加は target
     改訂扱いとする。term の評価対象は hom(`IndexedBaseDiagramHom`)
     とし(`DiagnosticConservative` は同じ hom 上の per-interpretation
     全量化述語 — (a) の量化形固定が型を接続する)、
     constructor が carrier / shape / diagram parameter を含まない
     ことで全量化域に一様とする(per-carrier / per-shape 分岐なし。
     rebase 装置は不要 — 構文が parameter を含まないため)。class には
     資格条項5項を課す — (i) 探索前固定(language head / class-term
     head の手続き)、(ii) 結論非参照(syntax の排除で担保し、
     transitive dependency audit を discharge artifact に含める)、
     (iii) 同型不変性(iso の読みは **diagram 圏の同型** — vertex
     成分 iso が全 generating edge と可換(naturality)である diagram
     iso の対+両 hom との可換 square からなる witness 型で F0 が型
     固定する。naturality を欠く成分別同型の読みは採らない —
     `edgewiseSquarePullback` が保存されないため)、(iv) 閉性
     ((h) の conjunct が担い、別 artifact に計上しない)、(v) 非空
     発火((g) の conjunct が担う — 非恒等 defect・非恒等
     reselection・非可逆成分を含む class 成員上の実発火)。
  3. **(c) 反射 theorem**: class 上で target obstruction vanishing →
     source vanishing を証明する。非自明性の根拠 — (d2) endpoint 群
     準同型は一般に非単射であり、逆方向は G-110 / G-111 の順方向
     無条件性から従わない — を statement 側に一文固定し、逆方向の
     非含意そのものは (f) の class 外 witness が実在証明として固定
     する(この紐付けを statement に明記する)。
  4. **(d) orbit 検出 theorem**: source reselection orbit の非自明性が
     target で検出されることを class 上で証明する。
  5. **(e) pointwise raw-defect reflection の分類(O20)**: cochain 値
     水準の反射が成立するか否かを、(c)(d) の vanishing / orbit 水準と
     は別 statement として、固定 O20-term の class 上で二枝分類する
     (どちらの枝の確定も成功)。term は (b) と同一の条件言語から
     選び、候補列は F0 で事前登録する(O20-term head。先頭 =
     class-term head と同一の term を**名指しで**(by-value)登録
     する — (b) の候補遷移が O20 の選定を動かさないため)。正枝 =
     固定 term の class 上の cochain 反射 theorem。反例枝 = 固定
     term の **class membership を満たし**、非恒等 defect・非恒等
     reselection の非退化条件を満たす witness で、正枝を反証する
     ことを同時に証明する(排他性は反例が供給 — G-110 (B) 様式。
     class 外 witness による代替は放電と数えない — (f) との分界)。
  6. **(f) class 外 witness**: class に入らない作用で非零 obstruction が
     消える有限 witness を構成する(保守性の破れの実在 = class 制限の
     非空虚性、かつ (c) の逆方向非含意の実在証明)。
  7. **(g) class 内 named nonvacuity witness**: 非恒等 defect・非恒等
     reselection・非可逆成分を含む class 成員上で反射・検出が実発火
     する有限 witness を構成する。非可逆成分は hom の vertex 成分の
     `sourceMap`(単射・非全射)で実現する — `atomEquiv` は常に可逆で
     あり実現部位にならない。
  8. **(h) 閉性**: 診断 class の恒等・水平・垂直貼り合わせ閉性を証明
     する。閉性は producer で証明する — operand の class membership を
     実消費し、output の membership を構成する(output 側の caller
     供給、および membership 定義の展開だけの放電は不可)。
  9. **(i) `Full` + `Faithful` 候補の決定**: 対象は vertex ごとの
     生成 fiber transport functor(`indexedFiberAction` 系、
     `CoreFiber` 間)とし、`Full` + `Faithful` はこの functor に
     ついて読む。その十分条件候補の statement を固定し、生成 class
     との関係を決定する。「決定」= class → 候補、候補 → class の
     含意それぞれについて証明または反例で帰趨を確定すること(一方向
     のみの確定は完了と数えない。帰趨の組はどれでも成功)。候補
     statement は F0 で
     事前登録し((i) candidate head)、K 段の証明結果で差し替えない
     (遷移は候補遷移規則に従う)。候補は Full+Faithful への
     十分性が独立に立つ形に限り、生成 class の条件と構文的に同一の
     候補、および Full+Faithful 自体の言い換え・定義展開に一致する
     候補は不可(関係決定の自明化の排除)。
- `target theorem boundary`: Lean 置き場所は
  `research/lean/ResearchLean/AG/DoctrineFiberProduct/` 配下の新
  module。G-111 / G-110 / G-109 / G-106 の reviewed module は参照
  のみ。完了面は (a)–(i) まで。順方向共変性(G-111)・coverage
  (G-112)・段射影方向の effectivity 反射(域外)は主張しない。
  universe 契約は F0 の型突合で確定し fixed head に記録する。(f)(g) の
  witness は有限 fixture であり per-universe 構成を原則とする。
  per-universe 構成が具体的 Lean universe constraint として型不能と
  固定・記録された場合は `goal-defect` とする(endpoint 固定への弱化
  は行わない)。
- `target proof artifacts`: `DiagnosticConservative` 定義、閉じた条件
  言語(constructor 表の syntax 型・evaluator・transitive dependency
  audit)、iso witness 型と生成 class の資格 theorem 群(結論非参照・
  同型不変性)、十分性
  theorem、反射 theorem(O14)、orbit 検出 theorem(O15)、cochain 値
  反射の分類 artifact(O20、反例枝は非退化条件付き)、class 外破れ
  witness(O16)、class 内 named nonvacuity witness、貼り合わせ閉性
  theorem(O17)、`Full` + `Faithful` 決定 artifact(O18)、report
  `research/reports/G-113-aat-diagnostic-conservativity.md`。
- `target proof strategy`: F0 typing(language head = カード
  constructor 表の Lean 転写、term 候補列と順序の事前登録
  (class-term 先頭 = `vertexwiseSourceMapInjective`、O20-term 先頭 =
  `vertexwiseSourceMapInjective` を名指しで登録)、(i) candidate
  statement の事前登録、iso
  witness 型、`DiagnosticConservative` と生成
  class の signature、G-111 diagram-hom API への接続、universe 契約)→
  K0 定義と生成 class →
  K1 十分性と反射 → K2 orbit 検出と O20 → K3 witness 対(class 外の
  破れ+class 内の実発火)→ K4 閉性と (i) 決定。既存成果の利用 map:
  G-111 coherent diagnostic transport(量化域 —
  `IndexedBaseDiagram.lean` / `IndexedDiagnosticAssembly.lean` /
  `IndexedDiagnosticReselection.lean` / `IndexedDiagnosticVanishing.lean`)、
  `InReselectionOrbit`(orbit 語彙)、
  `CoreFiberFunctorDefectCochain` 系(fiberwise 作用の seed 型)。
- `target theorem completion criteria`: 全 artifact が sorry なしで
  `ResearchLean` に受理され、axiom / placeholder audit が clean で
  あること。下記 ledger の `discharge-required` を放電し、audit で
  provenance、proof-use、structure-field escape、route integrity を監査
  すること。二段 review gate(各実装 PR の標準 fixed-head
  `$review-pr`、completion candidate での Lean / report / tracking
  Issue 同期と final review packet 作成、独立 `$math-lean-review`
  4査読全 `No major findings`)と CI・merge・最終 Issue 同期を通過
  した場合だけ完了する(正本 = target-goal-contract.md)。完了時の
  全 conjunct が同一の final class-term に対して立つことを audit で
  確認する。
- `target premise discharge policy`: 入力
  (`IndexedBaseDiagramHom`・source diagnostic interpretation・witness
  fixture)だけを残せる。保守性・反射・検出の結論相当データの供給は
  放電と数えない。
- `target material premise ledger`:
  - `G-110 reviewed artifact`: `ambient-boundary`。参照のみ、改変
    しない。固定錨: DoctrineFiberProduct = 完了 PR #4153(final head
    `a1471483`、merge `315a2537`)(支える結論 = 順方向無条件性との
    分界と (f) の対照。proof-use = (c) の非自明性根拠の参照と (f) の
    対照。結論相当でない理由 = 既証明の環境)。
  - `G-111 reviewed artifact`: `ambient-boundary`。参照のみ、改変
    しない。固定錨: 完了 PR #4181(final head `87278945`、merge
    `8850a5b4`、fixed GOAL blob `6541ee42`)。供給 =
    `IndexedBaseDiagram` / `IndexedBaseDiagramHom`・coherent
    diagnostic assembly (d1)–(d6)・pointwise indexed calculus。
    順方向 API の再定義禁止。支える結論 = 全 conjunct の量化域。
    proof-use = 量化域と順方向 transport API の消費。結論相当でない
    理由 = 順方向定理と入力幾何であり、逆方向(保守・反射・検出)の
    結論を供給しない。
  - `G-106 InReselectionOrbit 系`: `ambient-boundary`(固定錨は G-110
    カード ledger の G-106 錨を継承。proof-use = orbit 検出 (d) の
    語彙)。
  - `G-109 core pseudofunctor API(CoreFiber)`: `ambient-boundary`
    (固定錨は G-110 カード ledger の G-109 錨を継承。proof-use =
    fiberwise seed 型の消費)。
  - `G-111 継承 direction hypothesis(declared base relation / path
    naturality)`: `direction-hypothesis`(支える結論 = 全 conjunct の
    量化域の入力仮定。provenance = G-111 reviewed の diagnostic-free
    diagram / hom 入力。proof-use = 生成 diagnostic transport の方向
    仮定として実消費する。結論相当でない理由 = 入力幾何の方向仮定で
    あり、保守性・反射・検出の結論を供給しない — claim boundary の
    宣言と対応する行)。
  - `閉じた条件言語(syntax / evaluator)`: `discharge-required`
    (支える結論 = (b) 資格条項 (i)(ii)。discharge artifact = カードの
    完全列挙と一致する閉じた syntax 型・evaluator・transitive
    dependency audit(依存 helper 経由で diagnostic 結論を読む経路の
    禁止)。provenance = カード列挙の Lean 転写(language head)。
    proof-use = class-term と O20-term が消費する。結論相当でない
    理由 = 条件の表現手段であり保守性の結論を含まない)。
  - `DiagnosticConservative 定義と生成 class`: `discharge-required`
    (支える結論 = (a)(b)。discharge artifact = 定義+iso witness 型+
    資格 theorem 群(結論非参照・同型不変性 — (iv)(v) は (h)(g) の
    行が担い二重計上しない)+十分性。provenance = language head の
    term(class-term head)。proof-use = (c)–(h) の class index。
    結論相当でない理由 = class は閉じた条件言語の
    構造条件のみで立ち、保守性は十分性 theorem が結ぶ)。
  - `反射・orbit 検出・O20 分類`: `discharge-required`(支える結論 =
    (c)(d)(e)。discharge artifact = (c)(d) の class 上 theorem と
    (e) の二枝確定 artifact(正枝 theorem、または membership+非退化
    +正枝反証の witness)。provenance = 固定 class-term / O20-term と
    G-111 順方向 transport API。proof-use = source 側仮定と class
    membership を実消費し、(c) は (f) witness との紐付けを含む。
    結論相当でない理由 = 反射・検出・分類は全て証明で生成し、
    certificate 供給を認めない)。
  - `witness raw data((f)(g))`: `conclusion-equivalent-risk`
    (支える結論 = (f)(g) の入力。provenance = proof obligation 選定時
    に固定する authored raw 幾何のみ — shape・diagram・hom・source
    diagnostic interpretation の有限 data。class membership / 非
    membership・保守性の破れ・発火・非退化・非可逆性を field に
    持たせない。proof-use = (f)(g) の証明で実消費する。監査
    artifact = structure-field escape audit と選定時固定の記録
    (証明後の target-fitting 選択の禁止)。結論相当でない理由 =
    raw 幾何のみで、破れ・発火は theorem として生成する)。
  - `witness firing / nondegeneracy theorem`: `discharge-required`
    (支える結論 = (f)(g)。discharge artifact = (f) の非零 obstruction
    の target 消滅と class 非 membership、(g) の class membership・
    反射 / 検出の実発火・非恒等 defect / reselection・非可逆成分の
    生成 theorem 群。provenance = witness raw data と固定 term。
    結論相当でない理由 = 全て証明で生成し、certificate 供給を認め
    ない)。
  - `貼り合わせ閉性`: `discharge-required`(支える結論 = (h)。
    discharge artifact = 恒等・水平・垂直の producer theorem —
    operand の class membership を実消費し output の membership を
    構成する(output の caller 供給不可)。provenance = class-term の
    評価意味と G-111 pasting API。proof-use = (h) の放電。結論相当で
    ない理由 = 閉性は証明で生成する)。
  - `Full + Faithful 決定`: `discharge-required`(支える結論 = (i)。
    discharge artifact = F0 事前登録の候補 statement+両含意それぞれ
    の証明または反例。provenance = (i) candidate head と生成 fiber
    transport functor。proof-use = 生成 class との関係決定。結論相当
    でない理由 = 帰趨の組はどれでも成功する分類であり、結論を仮定
    しない)。
- `target route integrity gate`: 生成 class は language head で固定
  した閉じた syntax の term として立て、fixture 値・checker 出力・
  結論由来の条件を持ち込まない。witness fixture は
  proof obligation 選定時に固定する。term 候補・(i) 候補の証明後の
  target-fitting 差し替えをしない(遷移は事前登録列の次項、または
  人間承認に限る)。禁止経路 — 結論の埋め込み(class = conservative
  同値述語)、可逆 fixture のみの反射発火、候補の構文的再ラベル、
  証明後の target-fitting 選択。
- `target anti-weakening rule`: 保守性・反射・検出・閉性・発火を
  theorem argument、typeclass、structure field、certificate field、
  opaque class membership へ移して成功扱いしない。class term・(i)
  候補と結論の**定義的同値**(定義展開・Skolem 化で結論に一致する
  形)を禁じる。`ambient-boundary` に残せるのは入力幾何だけである。
- `target failure policy`: fail-closed を原則とする。資格条項・十分
  性・candidate class 上の (c)(d) の反例固定は candidate 相対の反証で
  あり、候補遷移規則に従って candidate refuted → 事前登録列の次候補と
  する(固定 target の反証ではない)。事前登録列の消尽は
  `target-blocked` とし、新 term の発明は target 改訂(人間裁定)と
  する。candidate の取り方に依存しない不能の定理化 — (f) が原理的に
  不能(保守性が coherent domain で無条件成立し class 制限が空虚)、
  または条件言語の全 term 上で反射 (c) もしくは orbit 検出 (d) が
  不能 — は、その定理を成果として
  `target-refuted` とする。(e) は二枝分類でありどちらの枝の確定も
  成功、両枝とも閉じない場合は `target-blocked`。(i) は帰趨の組が
  どれでも成功。(a) の型不能・statement 不足、および条件言語の F0 以後の
  設計持ち込みは `goal-defect`。witness の停滞は `target-blocked`。
  fixed target の変更は人間の別判断とする。
