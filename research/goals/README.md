# Research GOALs

GOAL とは、研究で成し遂げたい能力や到達像である。通常は証明したい定理の一覧ではない。定義と改訂は人間の判断による。`$research-loop` は、active な GOAL に対して候補を探索し、四審判、Lean 検証または証拠固定、SCORE 監査、PR レビューを通して、GOAL の能力がどれだけ増えたかを積み上げる。`research mode: target-theorem` の GOAL では、GOAL の能力を代表する一つの大定理をカードに定義し、その証明を完了条件にしてよい。

各 GOAL の静的定義、固定 target statement、完了条件は、このディレクトリの GOAL カードを正本とする。active な GOAL は、サイクルの先頭で `$research-loop` または `$target-theorem-loop` が `goal defect` を検査する。必要な項目は末尾の「GOAL カードの型」にまとめる。カードの中に現れる NT 番号や大定理 G1-G8 は、[docs/note の AG 版考察ノート](../../docs/note/aat_ag_porting_bridges_grand_theorems.md)で定義する。

active threshold、current SCORE、proof state、サイクル履歴などの実行状態は、GOAL ごとの GitHub tracking Issue を正本とする。ループ実行中は GOAL カードを編集せず、改訂が必要なら tracking Issue または別 Issue に提案を残す。

## 命名規則

GOAL id は `G-<NNN>-<領域>-<テーマ>` とする。`<NNN>` は 101 から始まる3桁の
グローバル通し番号(領域をまたいで単調増加)、`<領域>` は `aat` / `sft` 等、
`<テーマ>` は短い kebab-case。略称には `G-<NNN>` を用いる。
旧形式 `G-<領域>-<テーマ>-<連番>` のカードは改名しない。

## active

- [G-aat-quality-surface-01](G-aat-quality-surface-01.md)
- [G-sft-conway-01](G-sft-conway-01.md)
- [G-aat-quality-surface-04](G-aat-quality-surface-04.md)
- [G-112-aat-exact-bottom-coverage](G-112-aat-exact-bottom-coverage.md)
  (Gr4 完遂 gate 第一項後半: 第一段 coverage、第二段帰趨の二枝
  disjunction、O7 semantic-global lift の正本化、coverage closure と
  lift coherence (a)–(e)。O6 量化域 = sector 全域(裁定済み)。依存先
  G-110 は完遂済み、G-111 とは lift の分界(O2 / O7)を相互明記)
- [G-113-aat-diagnostic-conservativity](G-113-aat-diagnostic-conservativity.md)
  (Gr4 完遂 gate 第五項: `DiagnosticConservative` の新設、生成
  class の十分性・反射・orbit 検出・O20 分類、class 外 / 内 witness
  対、貼り合わせ閉性、`Full` + `Faithful` 関係決定 (a)–(i)。生成
  class = 閉じた条件言語の term(候補列はカード固定の全 normal form
  3項、先頭 = `vertexwiseSourceMapInjective`)。依存先 G-111 は完遂
  済み。execution gate: loop 起動は G-112 完遂後 — カード program
  context を正とする)

## draft（人間の確認待ち）

- [G-114-aat-refinement-base-change](G-114-aat-refinement-base-change.md)
- [G-115-aat-upper-stage-lift](G-115-aat-upper-stage-lift.md)
- [G-116-aat-gr4-capstone](G-116-aat-gr4-capstone.md)
  (以上3枚 = Gr4 完遂 gate 5項を閉じる単責務ラインナップの後続
  (第一手 G-111 は完遂済み、第二手 G-112・第三手 G-113 は active)。
  義務台帳の正本 = G-116 カード、設計の source note = n1007。昇格は一枚ずつ、
  G-116 は G-111〜G-115 の全帰趨確定後。昇格前の裁定事項: G-115 =
  `ObProblem` の Lean 指示対象)
- [G-aat-quality-surface-03](G-aat-quality-surface-03.md)
- [G-sft-law-transport-01](G-sft-law-transport-01.md)
- [G-sft-deformation-01](G-sft-deformation-01.md)
- [G-sft-ensemble-01](G-sft-ensemble-01.md)

## completed

- [G-101-aat-atom-foundation](G-101-aat-atom-foundation.md)
- [G-102-aat-two-phase-obstruction](G-102-aat-two-phase-obstruction.md)
- [G-103-aat-canonical-resolution](G-103-aat-canonical-resolution.md)
- [G-104-aat-resolution-invariance](G-104-aat-resolution-invariance.md)
- [G-106-aat-transport-coherence](G-106-aat-transport-coherence.md)
- [G-107-aat-uniform-invariance-characterization](G-107-aat-uniform-invariance-characterization.md)
- [G-108-aat-geometry-reading-transport](G-108-aat-geometry-reading-transport.md)
- [G-109-aat-cross-stage-coherence](G-109-aat-cross-stage-coherence.md)
- [G-110-aat-doctrine-fiber-product](G-110-aat-doctrine-fiber-product.md)
- [G-111-aat-indexed-base-change-schema](G-111-aat-indexed-base-change-schema.md)
- [G-aat-quality-surface-02](G-aat-quality-surface-02.md)
- [G-aat-quality-surface-05](G-aat-quality-surface-05.md)
- [G-aat-quality-surface-06](G-aat-quality-surface-06.md)
- [G-aat-quality-surface-07](G-aat-quality-surface-07.md)

## inactive

- [G-105-aat-structural-cover-invariance](G-105-aat-structural-cover-invariance.md)
  (`target-refuted`。改訂裁定待ち — 反証記録と salvage reading はカードを参照)

## GOAL カードの型

active な GOAL は、次の項目をすべて備えていなければならない。draft はここへ昇格する前にすべて埋める。足りない場合、`$research-loop` は `goal defect` として止まる。

- `id` と `status: active`。
- 任意の `research mode`: 省略時は `score-phase`。大定理証明モードでは `target-theorem` とする。
- `research aim`: 研究で成し遂げたい能力や到達像。
- `core tension`: 何が分かれば本当に非自明で、何が解ければ理論の景色が変わるか。
- `rival`: 比較対象にする既存概念、手法、tooling、理論枠組み。候補の価値は、GOAL 内部の面白さだけでなく、この rival に対してどの能力で有効かでも評価する。
- `claim boundary`: どの語彙、law universe、coverage topology、係数、profile の上で語るか。
- `capability categories`: SCORE を配分する能力カテゴリ。例: quantity、invariance、computability、interpretation、obstruction、unification。
- `threshold policy`: active SCORE threshold を tracking Issue でどう設定・読むかの方針。固定値ではなく、フェーズごとの運用パラメータとして扱う。
- `portfolio constraint`: ひとつの方向だけで点を稼いでフェーズを区切らないための条件。
- `phase boundary criteria`: 研究としてキリが良いと判定する条件。
- `reward rubric`: SCORE の採点規則。base score、evidence multiplier、penalty を分けて読めること。
- `dullness filter`: 定義展開、既存定理の即時系、名前替え、小補題量産を弾く基準。
- `frontier`: 探索してよい周辺領域。反例、obstruction、予想の強化、新しい不変量、別領域との橋を含めてよい。
- 任意の `spine`: 現時点の仮説的な道筋。固定計画ではなく、壊す、鋭くする、置き換える対象として扱う。

`research mode: target-theorem` の GOAL は、さらに次の項目を持つ。大定理は GOAL カードに定義し、ループ中に弱めて成功扱いしない。

- `target theorem`: 証明したい大定理の名前と statement。
- `target theorem boundary`: 語彙、有限性、law universe、coverage topology、係数、site / cover、Lean 置き場所、主張してよい範囲。
- `target proof artifacts`: 完了時に存在すべき Lean theorem / theorem package / finite witness / concrete certificate / report section。
- `target proof strategy`: support lemma、normalization、counterexample exclusion、bridge、既存成果の利用 map。
- `target theorem completion criteria`: 証明完了の条件。原則として sorry なし Lean proof、対象 declaration の axiom audit、material premise / hypothesis の discharge audit(provenance / proof-use / structure-field escape / route integrity を含む)、各実装 PR の標準 fixed-head `$review-pr` gate、report と tracking Issue の target_cycle_result 同期、final_review_packet、別工程の 4 並列 `$math-lean-review` の全査読 `No major findings` 判定を含む(二段 gate の正本 = `target-goal-contract.md`)。
- `target premise discharge policy`: target theorem が faithfulness、exactness、nondegeneracy、coverage、transport、representation adequacy などの実質的前提を含む場合、その前提を target boundary として残すのか、Lean theorem / finite witness / concrete certificate で discharge して completion 条件に含めるのかを書く。
- `target material premise ledger`: target theorem の結論を支える実質的前提を列挙する。各 premise について、名前、何を支えるか、許される role (`direction-hypothesis` / `ambient-boundary` / `discharge-required` / `conclusion-equivalent-risk`)、completion までに必要な discharge artifact、provenance と proof-use、結論相当 premise ではない理由を書く。
- 任意の `target route integrity gate`: 生成物(比較射・診断写像・witness)の許容経路と禁止経路(結論相当データの供給、証明後の target-fitting 選択、定義的 bridge 等)を独立の節として書く。selected fixture・checker・authored 入力を使うカードでは省略しない。この一覧の正本は `.codex/skills/target-theorem-loop/references/target-goal-contract.md` であり、drift した場合は契約側を正とする。
- `target anti-weakening rule`: 結論相当の仮定を theorem argument、typeclass、structure field、certificate field、opaque class membership に移して成功扱いしないための規則を書く。`ambient-boundary` に残せるのは入力幾何だけであり、target conclusion、faithfulness、effectivity、triviality、global coherence、obstruction vanishing と同値または片方向に近い条件を隠してはならない。
- `target failure policy`: 反例、仮説不足、証明停滞を `target-refuted`、`target-blocked`、GOAL 改訂提案のどれとして扱うか。
