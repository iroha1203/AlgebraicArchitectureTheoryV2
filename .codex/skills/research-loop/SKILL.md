---
name: research-loop
description: 研究 GOAL に対して、定理候補・反例・構成・不変量を探索し、Lean 検証、ライバル比較、独立審判で研究貢献 SCORE を確定しながら反復する研究ループ。GOAL カードで定義された大定理をターゲットに証明を積み上げる大定理証明モードも扱う。Use when the user says "$research-loop <goal-id>", "研究ループを回して", or wants Codex to autonomously search, score, prove, compare against rivals, report, and PR research contributions toward a standing research goal.
---

# Research Loop

この skill は、研究 GOAL に向けて候補を探索し、価値の高いものを Lean で検証し、研究貢献 SCORE を積み上げるためのループである。GOAL カードが `research mode: target-theorem` を持つ場合は、SCORE threshold ではなく GOAL カード上の大定理を完了条件として、補題、反例、構成、normalization、bridge を積み上げる。応答、Issue、PR はすべて日本語で行う。

GOAL は通常、「証明したい定理の一覧」ではない。GOAL は文字通り、研究で成し遂げたい能力や到達像である。たとえば AAT なら「アーキテクチャ品質を定量的に計測できるようにする」のように、理論が獲得すべき力を表す。skill が行うのは、その GOAL に貢献する定理、反例、構成、不変量、比較、計算可能性結果、予想の鋭化を探し、証拠に応じて SCORE を確定することである。例外として、大定理証明モードの GOAL は、その能力を代表する一つの大定理を GOAL カードに定義し、その証明を完了条件にしてよい。

Lean proof は主報酬ではない。Lean は成果の信頼度を上げる検証ゲートである。主報酬は、GOAL の能力をどれだけ増やしたか、見方をどれだけ変えたか、複数の現象をどれだけ圧縮したか、次の研究をどれだけ開いたか、ライバルとなる既存概念に対してどれだけ有効な差分を作ったかに対して与える。

## 入口

起動は `$research-loop <goal-id>` とする。`goal-id` は [research/GOALS.md](../../../research/GOALS.md) の active な GOAL を指す。任意で `threshold <N>`、`score-threshold <N>`、`max-cycles <N>`、対象カテゴリ、探索寄りまたは証明寄りの指示を渡してよい。GOAL カードが `research mode: target-theorem` を持つ場合は、起動引数に threshold がなくてもよく、完了条件は GOAL カードの `target theorem completion criteria` で読む。

最初に次を読む。

- [research/README.md](../../../research/README.md)
- [research/GOALS.md](../../../research/GOALS.md)
- [research/ideas/TEMPLATE.md](../../../research/ideas/TEMPLATE.md)
- [research/reports/README.md](../../../research/reports/README.md)
- [research/DESIGN.md](../../../research/DESIGN.md)

tracking Issue に cycle / merge / phase / genius target / target theorem proof コメントを書くときだけ、[references/ledger-templates.md](references/ledger-templates.md) の該当テンプレートを読む。
G0 で GOAL card の必須項目や欠陥判定を確認するときは、[references/goal-card-contract.md](references/goal-card-contract.md) を読む。
候補カードを作成または同期するときは、[references/candidate-card-contract.md](references/candidate-card-contract.md) を読む。

GOAL が active でなければ Issue を作らずに止まる。draft を active に昇格させるのは人間の判断である。

`research/GOALS.md` は research-loop の不変入力として扱う。この skill は GOAL 本文、`status`、`rival`、`threshold policy`、`portfolio constraint`、`reward rubric`、`spine`、`frontier`、`research mode`、`target theorem`、`target theorem completion criteria`、`target premise discharge policy`、`target failure policy` を直接編集しない。active SCORE threshold は GOAL カードではなく tracking Issue の threshold state として扱う。欠陥を見つけた場合は `goal defect` または `threshold missing` として止まり、tracking Issue コメントまたは別 Issue に改訂案を書く。

## GOAL 契約

active な GOAL は、候補を落とすための報酬関数を持つ。必須項目、任意項目、欠陥判定は [references/goal-card-contract.md](references/goal-card-contract.md) を正とする。

G0 では、GOAL が active か、reward / rival / claim boundary / research mode / threshold policy または target theorem / portfolio constraint / frontier が候補選別に足りるかだけを確認する。不足する場合は `goal defect` として止まり、改訂案を tracking Issue または別 Issue に残す。

## SCORE の原則

SCORE は研究能力の増分に対して与える。証明数、ファイル数、定理数には与えない。

基本点は、候補が GOAL に与える価値で決める。

- `0`: 定義展開、既存結果の言い換え、GOAL の能力を増やさない局所補題。
- `10-20`: 小さいが必要な補助結果。単独では GOAL の景色を変えない。
- `30-40`: 新しい測定量、構成、比較、計算手段を与え、既存の AAT 構造と接続する。
- `50-70`: 複数の品質概念、obstruction、cohomology、metric、lawfulness を一つの枠で説明する。
- `80-100`: 反例、obstruction、新しい不変量、主定理候補により、GOAL の見方や到達像を変える。

### ジーニアス評価

通常の `0-100` 基本点とは別に、めったに出ないブレークスルー候補だけを `genius` として扱う。

- `1000`: 天才的な閃きがあり、複数の分野を橋渡しし、数学的にも CS 的にも非常に強い主張で、AAT にブレークスルーをもたらす候補。

`genius` は「少し良い 80-100 点」ではない。通常候補の延長として乱発してはならない。次をすべて満たす場合だけ、基本点 `1000` を採用してよい。

- AAT の core tension や到達像を実質的に変える。
- 数学的構造と CS / SWE / tooling / architecture 理論の少なくとも二つ以上を、単なる比喩ではなく同じ定理・構成・不変量・反例・予想強化の中で橋渡しする。
- 既存 rival が提供できない能力を明確に作るか、rival の強みを AAT 内部のより強い構造へ統合する。
- claim boundary を守りながら、通常の incremental closure では到達しない大きな射程、圧縮、反例性、または新しい研究プログラムを開く。
- 証拠計画があり、単なる大きな名前、願望、未検証のスローガンではない。

`genius` 候補は G2 の四審判が全員 `genius_eligibility: yes` を明示し、G4 SCORE 監査が `genius_verdict: confirm` を返した場合だけ採点する。一人でも `no` または `cannot-determine` なら通常の `0-100` 基本点へ戻す。証拠 multiplier と penalty は通常どおり適用する。

`genius` は一サイクルで完結しなくてもよい。先に `genius target theorem` を立て、後続サイクルで補題、反例、構成、計算例、不変量、bridge を積み上げて、その定理を攻略する形を許す。

- `genius target theorem`: AAT にブレークスルーをもたらす大定理候補、または大きな conjecture / theorem program。tracking Issue に target、claim boundary、必要補題 map、現在の証拠段階を残す。
- `genius support cycle`: target theorem を証明・反証・鋭化するための補題、有限 witness、obstruction、bridge、normalization、counterexample analysis。通常の `0-100` 基本点で採点し、target への寄与も記録する。
- `genius unlock`: target theorem そのものが Lean proof、十分強い theorem package、または明示的に許された conjectural evidence として G2/G3/G4 を通ったときだけ、基本点 `1000` を確定する。

`genius target theorem` を立てただけで `1000` 点を加算してはならない。target を置くサイクルは、定理プログラムとしての価値を通常 SCORE で採点するか、証拠が足りなければ SCORE なしの tracking Issue seed として扱う。後続の support cycle は通常 SCORE を得られるが、target unlock の `1000` 点は、target theorem の証拠が固定された時点でだけ別途確定する。二重計上を避けるため、G4 は target unlock 時に「support cycles で既に得た SCORE」と「今回 unlock する genius SCORE」が何を別々に評価しているかを説明する。

証拠は multiplier として扱う。

- `x1.0`: 手計算、説得的議論、既知理論との対応。
- `x1.2`: 有限例、計算例、具体的 architecture family での検算。
- `x1.5`: Lean statement または結論部だけの `sorry` を持つ conjecture。
- `x2.0`: Lean proof が通り、公理検査と Lean 形式化品質監査が clean。

負の選択圧も明示する。

- `-30`: 強い問いを弱い命題に落として成功扱いした。
- `-30`: SCORE を稼ぐために自然な主張を不自然に分割した。
- `-30`: GOAL の `rival` に対する有効性や新規性を示さず、既存手法の説明を言い換えただけだった。
- `-50`: GOAL の claim boundary を越えた主張を成果として扱った。

候補の最終 SCORE は、独立審判が `base score`、`evidence multiplier`、`penalty`、`final score` に分けて承認したときだけ tracking Issue に加算する。

### 大定理証明モード

`research mode: target-theorem` の GOAL では、ひとつの大定理をターゲットにして証明を積み上げる。基本サイクルは通常と同じだが、完了条件は SCORE threshold ではなく、GOAL カードで定義された `target theorem completion criteria` を満たすことである。

大定理証明モードは `genius` 評価とは別概念である。`genius` は希少な SCORE 枠であり、`target-theorem` は制御ループのモードである。ターゲット定理が `genius` 級である必要はないし、target support cycle が自動的に高 SCORE になるわけでもない。SCORE は証明への研究貢献を測る補助台帳として使ってよいが、target theorem が未証明なら SCORE threshold 到達だけでは完了しない。

GOAL カードは最低限、次を定義する。

- `research mode`: `target-theorem`。
- `target theorem`: 証明したい大定理の名前と自然言語 statement。
- `target theorem boundary`: 語彙、有限性、係数、site / cover、Lean 置き場所、主張してよい範囲。
- `target proof artifacts`: 完了時に存在すべき Lean theorem / theorem package / report section / candidate card。
- `target proof strategy`: support lemma、normalization、counterexample exclusion、bridge、既存成果の利用 map。
- `target theorem completion criteria`: 何をもって証明完了と判定するか。原則は sorry なし Lean proof、対象 theorem package の axiom audit、実質的な前提条件の discharge audit、G3.5 同期、G4 監査、G5 レビュー、G6 target completion 判定である。target theorem が faithfulness、exactness、nondegeneracy、coverage、transport、representation adequacy などの実質的前提を含む場合、それらを theorem / concrete certificate で discharge するのか、GOAL の claim boundary として明示的に残すのかを completion criteria に書く。
- `target premise discharge policy`: target theorem の実質的前提を target boundary として残すのか、completion までに Lean theorem / finite witness / concrete certificate で discharge するのかの方針。
- `target failure policy`: target theorem が反例、仮説不足、証明停滞に遭遇したときの `target-refuted` / `target-blocked` / GOAL 改訂提案の扱い。

tracking Issue は実行状態を持つ。target theorem 自体は GOAL カードが正本であり、Issue には proof state、未完 support node、完了 support node、blocker、PR、現在の証拠段階だけを置く。target theorem の statement を弱める、claim boundary を変える、completion criteria を変える場合は、人間の明示指示または GOAL 改訂提案が必要である。ループ内では、target を弱めて成功扱いしない。

大定理証明モードの候補は次のいずれかである。

- `target-support`: target theorem の support map の node を進める補題、構成、有限 witness、normalization、bridge。
- `target-obstruction`: target theorem の仮説不足、反例、必要条件、statement 修正要求を明らかにする結果。
- `target-refinement`: target theorem を弱めず、仮定、型、claim boundary、support map を鋭くする整理。GOAL カードの改訂が必要な場合は提案で止める。
- `target-proof`: target theorem 本体または theorem package を証明するサイクル。

G6 では、通常の phase boundary 判定に加えて target completion 判定を行う。`target-proof` が完了し、completion criteria を満たした場合だけ `target-theorem-proved` として止まる。support node が進んだだけなら、SCORE threshold に到達していても stop state は `continue` または、人間に整理判断を返す `target-proof-checkpoint` に留める。theorem package が結論に必要な実質的前提を未 discharge の引数として残している場合は、GOAL カードがその conditional theorem を完了形として明示していない限り `target-theorem-proved` にしない。GOAL が premise discharge を completion criteria に含める場合、その前提を証明または concrete certificate で支えるまでは `target-proof-checkpoint` とする。target theorem が反例で壊れた場合は `target-refuted`、support map が詰まった場合は `target-blocked` として止め、GOAL 改訂または新 target 設計を人間に返す。

## サイクル

```text
G0 状態確認
G1 探索と候補生成
G2 価値スコア審判
G3 Lean 検証または証拠固定
G3.5 候補カード同期
G4 SCORE 確定とレポート
G5 PR レビューとマージ
G6 研究フェーズ区切り判定
```

ひとサイクルで PR に入れる主成果は原則ひとつにする。ただし一つの貢献を構成する補題群はまとめてよい。
研究主張の revise は一巡だけにする。Lean の機械的修正、候補カード同期、PR メタデータ修正は二巡まで許すが、同じゲートで三度止まる場合は `proof stagnation`、`review stagnation`、または SCORE 減点として扱う。

### G0 状態確認

1. `git status` と `git ls-files --others --exclude-standard` を確認する。ユーザーの未コミット変更や未追跡ファイルがあれば勝手に戻さない。作業対象と衝突する場合は止まる。
2. `main` を最新化する。
3. tracking Issue `Research Loop: <goal-id>` を探す。なければ作る。
4. GOAL カードの `research mode` を読む。省略時は `score-phase` とみなす。`target-theorem` の場合は GOAL カードの target theorem、boundary、support map、completion criteria、premise discharge policy、failure policy を読む。
5. 起動引数に `threshold <N>` または `score-threshold <N>` があれば、tracking Issue に threshold 設定コメントを残し、その値を active threshold とする。既存値を変える場合は old/new と理由をコメントに残す。
6. 起動引数に threshold がなければ、tracking Issue の最新 threshold 設定コメントまたは Issue body から active threshold を読む。
7. `score-phase` で tracking Issue に active threshold が見つからない場合は `threshold missing` として止まり、`$research-loop <goal-id> threshold <N>` で再開するよう返す。GOAL カードの `threshold policy` は threshold の選び方の方針であり、active threshold の代替正本にはしない。`target-theorem` では threshold は任意の補助台帳であり、GOAL カードの completion criteria があれば threshold missing では止めない。
8. 未完の PR があれば新しいブランチを切らずに続ける。
9. tracking Issue から現在の SCORE、カテゴリ別 SCORE、直近サイクル、停止条件を読む。
10. `target-theorem` では tracking Issue から target proof state、完了 support node、未完 support node、blocker、直近 proof attempt を読む。
11. tracking Issue に open な `genius target theorem` がある場合は、target、claim boundary、support map、既に完了した support cycles、unlock 条件を読む。

GOAL 定義の正本は `research/GOALS.md` に置くが、ループ中は read-only invariant として扱う。実行状態の正本は GitHub の tracking Issue に置く。active threshold、current SCORE、カテゴリ別 SCORE、直近サイクル、停止条件は Issue state である。候補 frontmatter とレポートは証拠 artifact である。README や committed docs を頻繁に変わる台帳にしない。
G0 で読んだ tracking Issue state は、本体が短い入力メモにして G1、G2、G3.5、G4、G6 の該当サブエージェントへ渡す。`target-theorem` では、GOAL カードの target theorem、completion criteria、premise discharge policy、target proof artifacts、support map、failure policy と、tracking Issue の proof state、完了 support node、未完 support node、blocker を必ず渡す。特に `genius target theorem` が open の場合は、target、claim boundary、support map、完了済み support cycles、unlock 条件、既存 SCORE ledger も渡す。
tracking Issue コメントには、後続 G6 が再構成できる cycle / merge / phase ledger を残す。人間向けの説明だけで SCORE 台帳を進めない。

### G1 探索と候補生成

候補生成では、spine を埋めるものだけでなく、GOAL の見方を変えるものを探す。毎サイクル、独立した候補生成サブエージェントを四体走らせ、最低四案の候補 pool を作る。
四体には互いの出力を渡さず、G0 で読んだ tracking Issue state、GOAL、rubric、claim boundary、必要な source references だけを渡す。同質な低リスク候補へ収束しないよう、四体には `closer`、`obstruction`、`unifier`、`wildcard` の探索ロールを一つずつ割り当てる。
候補 pool は重複を除いて数え、四案未満なら G2 へ進まず、追加探索するか `low-value stagnation` / `exhausted` の候補として止める。
候補 pool には、可能な範囲で性質の異なる候補種別と capability category を含める。picked を先に決めてから審判へ通すのではなく、候補 pool から最も強い候補を選べる状態を作る。`target-theorem` では、候補 pool の少なくとも二案は target theorem の support map、proof blocker、completion criteria のいずれかを直接進める候補にする。二案出せない場合は、なぜ target theorem が詰まっているかを `target-blocked` 候補として記録する。
通常候補とは別に、可能なら `genius` 候補も探索する。ただし `genius` は希少枠であり、該当しない場合は「なし」としてよい。SCORE を上げるために普通の候補を `genius` と呼ばない。
既存の `genius target theorem` が tracking Issue にある場合は、候補生成で少なくとも一つはその target を進める support cycle 候補を検討する。target より価値の高い別候補がある場合はそちらを採ってよいが、なぜ target を今進めないかを候補メモに残す。
ユーザーが breakthrough / genius 狙いを明示し、tracking Issue に open な target がない場合は、G1 候補 pool に `genius-target` 候補を少なくとも一つ含めるか、credible target がない理由を記録する。target seed は単独で SCORE を得るものではない。

良い候補は、数学的に非自明で、興味深く、GOAL に対して前進を作るものである。次を満たさない候補は生成しても優先しない。

- 定義展開や既存定理の即時系ではなく、新しい構成、比較、不変量、反例、obstruction、統一定式化のいずれかを含む。
- その候補が真なら、GOAL のどの能力カテゴリがどう増えるかを一文で言える。
- GOAL の `rival` に対して、どの能力で有効な差分を作るかを一文で言える。
- 驚き、圧縮、射程、反例性、計算可能性、古典理論や CS / SWE への橋のうち少なくとも一つを持つ。
- 証明または証拠の道筋があり、単なる願望や名前だけの予想ではない。
- claim boundary を守り、AAT / Lean / tooling の責務境界を混同しない。
- 直前までのサイクル、spine、report、または open frontier の何を閉じる、鋭くする、合成する、置き換えるのかが明確である。

候補種別を明記する。

- `closure`: 既存の重要 gap を閉じる定理。
- `orientation`: GOAL の見方を変える反例、obstruction、予想の強化、新しい不変量。
- `unification`: 複数の現象を一つの定式化で圧縮する結果。
- `computability`: 有限 regime や具体例で計算可能性を与える結果。
- `bridge`: 古典定理、CS / SWE、tooling surface への非自明な接続。
- `genius`: 天才的な閃きがあり、複数分野を橋渡しし、AAT にブレークスルーをもたらす希少候補。
- `genius-target`: 後続サイクルで攻略する大定理 / 大予想 / theorem program を立てる候補。
- `genius-support`: 既存の `genius target theorem` を証明・反証・鋭化するための補題、構成、有限 witness、bridge。
- `target-support`: GOAL カードの target theorem を証明するための support node を進める補題、構成、有限 witness、normalization、bridge。
- `target-obstruction`: target theorem の仮説不足、反例、必要条件、proof blocker を固定する結果。
- `target-refinement`: target theorem を弱めず、型、仮定、support map、claim boundary を鋭くする整理。
- `target-proof`: GOAL カードの target theorem 本体または theorem package を証明する候補。

候補カードは [research/ideas/TEMPLATE.md](../../../research/ideas/TEMPLATE.md) に従って `research/ideas/` に置く。必要フィールドは [references/candidate-card-contract.md](references/candidate-card-contract.md) を正とする。

### G2 価値スコア審判

四人の独立サブエージェントに審判させる。渡すのは GOAL、候補カード、GOAL の `rival`、関連する既存結果、reward rubric、dullness filter、必要な repo overview だけにする。本体の期待や途中判断は渡さない。

審判 A は厳密性を見る。

- claim boundary を守っているか。
- 既存結果の即時系や名前替えではないか。
- 証明または反例の筋が破綻していないか。
- Lean で狙う命題が候補の主張を弱めていないか。
- `genius` 候補なら、claim boundary を越えずに 1000 点級の主張として数学的に耐えるか。
- `target-theorem` では、候補が target theorem を弱めて成功扱いしていないか、support node と target completion criteria の関係が明示されているか。

審判 B は研究価値を見る。

- GOAL の能力を増やすか。
- core tension を閉じる、鋭くする、壊す、置き換えるか。
- surprise、compression、leverage があるか。
- paper の節または主定理候補になりうるか。
- `genius` 候補なら、AAT の見方を変えるブレークスルーか。
- `target-theorem` では、候補が target proof distance を実質的に縮めるか、または target の反例・仮説不足を明確にするか。

審判 C はプロジェクト全体の価値を見る。

- AAT / SFT / Tooling / Website / Research の全体像に照らして価値があるか。
- repo の現在の source of truth、claim boundary、公開面、研究計画に対して自然な前進か。
- 局所的には面白くても、プロジェクトの主軸から外れすぎていないか。
- 将来の docs、Lean、paper、tooling surface のいずれかに接続する見込みがあるか。
- `genius` 候補なら、AAT / SFT / Tooling / Website / Research のうち複数領域を自然に橋渡しするか。
- `target-theorem` では、target theorem が将来の docs、Lean、paper、tooling surface のどこに接続するかを保っているか。

審判 D はライバル比較を見る。

- GOAL の `rival` がすでに提供する能力を正しく捉えているか。
- 候補が rival に対して、どの能力で優位性、新規性、統合力、分離力、検証可能性を持つか。
- GOAL が複数の rival や strong rival を挙げる場合、それぞれが見える観測面を単に別名で繰り返していないか。
- rival では取り落とす support、transport、obstruction、trace、repair、failure mode のうち何を新しく扱えるか。
- `genius` 候補なら、rival の能力を単に超えるだけでなく、比較軸そのものを AAT 側で作り替えるか。
- `target-theorem` では、target theorem が rival に対して証明したい差分を、support cycle が維持または強化しているか。

各審判は次の形式で返す。

```text
verdict: accept | revise | reject
base_score:
genius_eligibility: yes | no | cannot-determine
target_progress: none | support-node | blocker-found | target-refined | target-proof-candidate | target-proved | target-refuted | not-applicable
category:
reason:
dullness_risk:
required_evidence:
checked:
unchecked:
```

G1 の候補 pool から、期待 SCORE、研究価値、rival に対する有効性が高い候補を審判へ出す。四者が `accept` した候補のうち、最も高いものを picked にする。A が `reject` した候補は数学的に進めない。B が `reject` した候補は GOAL に貢献しない。C が `reject` した候補は repo 全体の研究価値が不足している。D が `reject` した候補は rival に対する新規性または有効性が不足している。正しいが低 SCORE の候補は、必要な補助結果でない限り採らない。`target-theorem` では、通常 SCORE が少し低くても、target theorem の blocker を直接消す候補、completion criteria に必要な theorem package を進める候補、target proof の反例可能性を判定する候補を優先してよい。その場合は、なぜ SCORE 最大候補より target progress を優先したかを tracking Issue に残す。`genius` 基本点を採るには、四者全員が `genius_eligibility: yes` を返す必要がある。そうでなければ、候補の通常価値に応じて `0-100` 基本点で扱う。`genius-target` を採る場合、G2 は `1000` 点の即時付与ではなく、target theorem と support map が研究プログラムとして妥当かを判定する。既存 target への `genius-support` を採る場合、G2 には tracking Issue の target/support state を渡し、通常 SCORE に加えて、どの target hypothesis / lemma / obstruction / bridge を進めるかを確認する。`target-proof` を採る場合、G2 は score だけでなく target theorem の statement と Lean 予定 theorem が GOAL カードの completion criteria を満たしうるかを判定する。`revise` は一度だけ直して再審判する。審判が exactness、minimality、nonfaithfulness、typed transport、preservation/reflection、rival separation、`genius` 根拠、target completion criteria との対応などを要求した場合は、G3 へ進む前に候補カードと Lean 予定 statement に明示する。`reject` は `status: archived` とし、理由を残す。

### G3 Lean 検証または証拠固定

picked の性質に応じて証拠を固定する。

定理候補は `Formal/AG/Research/<slug>.lean` に形式化する。`Formal/AG` 本体は参照または import してよいが、直接編集してはならない。本体側の定義や補題が不足している場合は、Research 側で相対化できる範囲に留めるか、別 Issue / 別判断として報告し、このループ内で本体へ追加しない。合格条件は次の三つである。

1. `lake build FormalAGResearch` が通る。
2. 独立サブエージェントの公理検査が通る。
3. 独立サブエージェントの Lean 形式化品質監査を通る。

公理検査では、候補カードの主張文、Lean ファイル、claim boundary だけを渡す。`#print axioms <name>` を、レポートや候補カードに載せる全 declaration に対して流す。定理候補では `sorryAx`、非標準公理、相談されていない `axiom` がないこと、予想候補では `sorryAx` が結論部の一箇所だけにとどまること、前提・型・定義に sorry がないこと、Lean の命題が候補の主張と型の水準で一致し弱められていないことを確かめる。

有限 witness、computability、trace/support、repair frontier、最小反例などの具体構成では、`propext` / `Classical.choice` / `Quot.sound` を自動的に clean と扱わない。`Set` equality や `↔` の `simp` が `propext` を導入した場合は、可能な範囲で `cases`、`constructor`、`intro`、`rfl`、矛盾消去、明示的 witness 構成へ戻す。標準公理が残る場合は、G3 で理由を明示し、G4 SCORE 監査が `x2.0` に値するかを承認しなければならない。

ローカルでは対象範囲に応じて次を実行または同等に確認する。

```bash
lake env lean Formal/AG/Research/<file>.lean
lake build FormalAGResearch
#print axioms <declaration>
rg -n "\\b(axiom|admit|sorry|unsafe)\\b" Formal/AG/Research
rg -nP "[\\x{200B}-\\x{200F}\\x{202A}-\\x{202E}\\x{2066}-\\x{2069}]" <changed-files>
rg -n "$HOME|${TMPDIR%/}" <changed-files>
```

Lean 形式化品質監査では、候補の数学的命題が Lean で適切に表現されているかを確認する。型や仮定が強すぎて自明化していないか、弱すぎて元の主張を失っていないか、パラメータと claim boundary が明示されているか、vacuous な前提や到達不能な型で成功扱いしていないか、定理名と statement が研究レポートに載せられる水準かを見る。

反例、orientation result、計算例は、Lean proof だけを要求しない。ただし SCORE を確定する前に、証拠を固定する。

- 最小反例や有限例を明示する。
- 計算手順、対象 family、仮定を明示する。
- 既存理論との対応を参照できる形で書く。
- Lean statement、計算補助、手計算のどれを証拠にしたかを記録する。

証拠が弱い成果は multiplier を低くする。重要だが証明できていない insight は `orientation` として扱い、`proved-in-research` と呼ばない。

### G3.5 候補カード同期

G4 へ進む前に、候補カード、証拠、Lean declaration、審判メモを同期する。候補カードは生成時の期待値ではなく、実際に固定された証拠の index として読める状態にする。同期すべき最低項目は [references/candidate-card-contract.md](references/candidate-card-contract.md) を正とする。

候補カード、Lean declaration、report に載せる theorem 名、SCORE 監査入力がずれている場合は G4 に進まない。

### G4 SCORE 確定とレポート

検証と G3.5 同期後、独立サブエージェントに SCORE 監査を行わせる。渡すのは GOAL、GOAL の `rival`、同期済み候補カード、証拠、G2 の四審判結果、G3 の監査結果、diff だけにする。

監査は次を返す。

```text
score_verdict: confirm | reduce | reject | seed-only
base_score:
evidence_multiplier:
penalty:
final_score:
category:
genius_verdict: confirm | downgrade-to-normal | reject | not-applicable
goal_delta:
rival_delta:
project_value_delta:
formalization_quality:
target_progress:
proof_obligation_delta:
reason:
checked:
unchecked:
```

`confirm` または `reduce` の場合だけ `research/reports/<goal-id>.md` に書く。レポートは定理一覧ではなく、GOAL の能力がどう増えたかを書く。レポート、カテゴリ別 SCORE、total SCORE、proof portfolio、cycle section、Next Frontier / phase boundary メモは、候補カードの期待値ではなく G4 監査後の値で同時に更新する。`seed-only` は `genius-target` seed 専用であり、`base_score: 0`、`final_score: 0` として total SCORE とカテゴリ別 SCORE には加算しない。`seed-only` の場合は report を更新せず、tracking Issue に target、claim boundary、support map、unlock 条件、次に必要な support cycle を記録する。`genius_verdict: confirm` の場合は、なぜ通常の `80-100` では足りず `1000` 基本点に値するのかを report と tracking Issue に明示する。`downgrade-to-normal` の場合は通常基本点へ戻し、減点ではなく希少枠不成立として扱う。`genius-target` を採った場合は、tracking Issue に target theorem seed を残し、target 自体が未証明なら stop state は通常どおり `continue` にする。`genius-support` を採った場合は、support map のどの node が進んだか、target unlock に近づいたか、target を修正すべきかを tracking Issue と report に書く。`target-theorem` では、G4 が `target_progress`、`proof_obligation_delta`、material premise / hypothesis の discharge 状態を必ず返し、report と tracking Issue に support map のどの node が完了・変更・反証されたかを書く。`target-proof` が completion criteria を満たす可能性がある場合でも、実質的前提が未 discharge のまま残るなら G6 へは `target-proof-candidate` または `target-proof-checkpoint-candidate` として渡し、`target-proved` としない。
G4 完了前に、report 内の total SCORE、active threshold または not-applicable state、remaining、proof portfolio、Next Frontier、phase boundary / target checkpoint status が今回の SCORE 台帳と矛盾していないかを確認する。

各成果には次を残す。

- 候補名と種別。
- 証拠段階: `proved-in-research`、`conjectured-sorry`、`finite-evidence`、`orientation-evidence` など。
- final SCORE とカテゴリ。
- GOAL に対する delta。
- rival に対する delta。
- まだ開いている問い。

### G5 PR レビューとマージ

ひとつの picked の成果をひとつの PR にまとめる。PR には候補カード、Lean ファイルまたは証拠、レポート、tracking Issue の SCORE 更新を含める。G4 が `seed-only` を返し、committed artifact がない場合は PR を作らず、tracking Issue コメントだけを成果物にして次サイクルへ進む。候補カードなどの committed artifact を作った場合は通常どおり PR に入れるが、SCORE と report は更新しない。

tracking Issue は研究状態の正本であり、フェーズ区切りでも自動で閉じない。PR 本文では原則 `Refs #<tracking-issue>` を使う。人間が明示的に GOAL / tracking Issue の終了を指示した場合だけ `Closes #<tracking-issue>` を使う。

PR 前にセルフレビューを行い、次を確認する。

- G2 の価値判断、G3 の証拠、G4 の SCORE が diff に反映されている。
- 審判 D の rival 比較と G4 の rival_delta が diff に反映されている。
- Lean 形式化品質監査の結果が diff と SCORE に反映されている。
- `git diff --check` が通る。
- `git diff --cached --check` が通る。
- `git ls-files --others --exclude-standard` の未追跡ファイルを確認し、必要なものは含め、不要なものは PR に入れない。
- 不可視 Unicode と双方向制御文字が混入していない。
- ローカル絶対パス、個人情報、私的 fixture が公開物に入っていない。
- 保護対象の数学本文や docs/note を編集していない。
- PR 本文が tracking Issue を誤って close しない。

PR レビューは原則として `$review-pr <PR番号>`、すなわち [review-pr](../review-pr/SKILL.md) skill に従って独立サブエージェントに行わせる。レビュー対象は diff、GOAL、候補カード、SCORE 監査結果、ゲート基準だけにする。マージ可能、要修正、判定不能の三つで判定する。同じ PR の修正は二巡までとし、それを超えたらレビューの停滞として止まる。

マージするのは、独立レビューがマージ可能と判じ、かつ CI または必要なローカル検証が通っているときだけである。`gh pr merge` がローカル worktree の `main` checkout 競合などで非ゼロ終了した場合は、直ちに blocked とせず、`gh pr view <PR> --json state,mergedAt,mergeCommit` で GitHub 上の merge 状態を確認する。
SCORE update、merge update、genius target seed / support update、target proof progress update は ledger template を使い、PR 番号、merge commit、SCORE、total、active threshold、target proof state、stop state を tracking Issue に残す。

### G6 研究フェーズ区切り判定

PR マージ後、tracking Issue に iteration コメントを残す。

```text
cycle N: picked <candidate> / type <type> / score +S(category C) / total T / evidence E / PR #Y merged|open|blocked / stop continue|<停止条件名>
```

続いて独立サブエージェントに研究フェーズ区切り判定を行わせる。渡すのは GOAL、tracking Issue の active threshold、tracking Issue の SCORE 台帳、レポート、カテゴリ別 SCORE、証拠段階、phase boundary criteria だけにする。本体の期待は渡さない。`target-theorem` では、target theorem、completion criteria、premise discharge policy、target proof artifacts、support map、failure policy、tracking Issue の proof state、今回の proof_obligation_delta も渡し、target completion 判定を行わせる。

`score-phase` の GOAL は「完全達成」を判定する対象ではない。判定するのは、この時点でひとつの研究フェーズとして区切るだけの成果とまとまりがあるかである。フェーズを区切るには次を満たす。

- total SCORE が tracking Issue の active threshold 以上。
- `portfolio constraint` を満たす。
- 低 SCORE の補助結果だけで到達していない。
- report が coherent な節または paper seed として読める。
- report が GOAL の `rival` に対して、このフェーズの成果がどの能力で有効かを説明している。
- 独立審判が、GOAL の研究能力が実質的に増え、次のサイクルを続けるより整理・執筆・次フェーズ設計へ移る方が研究としてキリが良いと判定する。

フェーズ区切りなら Issue は閉じず、phase summary コメントを残して止まる。phase summary には、merged PR、merge commit、cycle ごとの SCORE、total SCORE、active threshold、portfolio constraint、rival に対する phase delta、CI / 独立レビュー結果、report の現在地、次の frontier、人間に返す判断を含める。`phase boundary` は、phase summary コメント URL を取得し、tracking Issue が open のままであることを確認した時点で完了とする。GOAL を閉じる、次フェーズへ移す、reward rubric を改訂する、別 GOAL を立てる、といった判断は人間に返す。区切りでなければ同じ GOAL で次サイクルへ戻る。

`target-theorem` では、G6 は先に target completion を判定する。GOAL カードの target theorem completion criteria を満たし、target theorem artifact が G3/G3.5/G4/G5 を通り、独立審判が theorem statement の弱体化や claim boundary 越えを認めなければ、`target-theorem-proved` として止める。G6 は theorem statement の `#check` 相当を読み、結論を支える実質的前提、class/structure 引数、hypothesis 引数、certificate 引数を列挙する。completion criteria が premise discharge を要求している場合、各前提が Lean theorem、finite witness、または concrete certificate で discharge されていることを確認する。未 discharge の実質的前提を引数として残した conditional theorem package は `target-theorem-proved` ではなく `target-proof-checkpoint` とする。証明が未完なら、SCORE threshold 到達だけでは phase boundary にしない。ただし人間に整理判断を返す価値がある場合は `phase boundary` ではなく `target-proof-checkpoint` として、完了 support node、未完 support node、blocker、次サイクル候補を tracking Issue にまとめて止めてよい。target theorem が反例により成立しないと判明した場合は `target-refuted` として止め、target 改訂または GOAL 改訂を人間に返す。

## 停止条件

止まることは失敗ではない。止める理由を tracking Issue に残し、人間へ返す。

サイクル段階で止まる条件は次である。Issue は閉じない。

- `low-value stagnation`: 二サイクル続けて期待 final SCORE が 30 未満の候補しか出ない。
- `proof stagnation`: 高 SCORE 候補はあるが、二サイクル続けて証拠固定に失敗する。
- `target-blocked`: 大定理証明モードで、target theorem の未完 support node または proof blocker が二サイクル続けて解消しない。
- `review stagnation`: 同じ PR が二巡してもマージ可能にならない。
- `score dispute`: 独立審判間で SCORE が大きく割れ、根拠を読んでも解消できない。
- `undecidable`: diff、CI、Lean 検証、証拠、tracking Issue のいずれかが確認できない。

フェーズ段階または GOAL 運用段階で止まる条件は次である。GOAL の tracking Issue は原則閉じない。GOAL の打ち切りや完了扱いは人間の判断である。

- `phase boundary`: tracking Issue の active threshold、portfolio constraint、phase boundary criteria を満たし、研究としてキリが良い。
- `target-theorem-proved`: GOAL カードの target theorem completion criteria を満たし、target theorem または theorem package の証明と、completion に必要な実質的前提の discharge が完了した。
- `target-proof-checkpoint`: 大定理証明モードで、target theorem は未証明、または conditional theorem package はあるが completion に必要な実質的前提が未 discharge であり、support map のまとまり、blocker、次判断を人間に返す必要がある。
- `target-refuted`: target theorem の現在の statement に反例または必要仮定不足が固定され、GOAL カード改訂なしには続けられない。
- `threshold missing`: `score-phase` で tracking Issue に active threshold がなく、起動引数でも threshold が指定されていない。
- `exhausted`: frontier を探索しても、非自明な高 SCORE 候補が尽きた。
- `max-cycles`: 指定された回数上限に達した。
- `goal defect`: GOAL の reward rubric、claim boundary、threshold policy、portfolio constraint に欠陥がある。
- `all blocked`: 残る高 SCORE 候補が、人間の判断、理論上の未解決問題、外部入力を待っている。

## サブエージェント規律

候補生成、G2 審判 A/B/C/D、G3 公理検査、G3 Lean 形式化品質監査、G4 SCORE 監査、G5 PR レビュー、G6 フェーズ区切り判定は、独立したサブエージェントに行わせる。サブエージェントを使えない環境では止まり、人間のレビューに委ねる。

サブエージェントには、対象ファイル、GOAL、rubric、claim boundary、必要な証拠だけを渡す。本体の期待、推測、採点意図、成功させたい候補は渡さない。返答には `checked` と `unchecked` を必ず含めさせる。未確認の項目を合格やフェーズ区切りに倒さない。

## サブエージェント標準プロンプト

標準プロンプト本文は [references/subagent-prompts.md](references/subagent-prompts.md) に置く。

サブエージェントを起動するときだけ、対応するゲートの見出しを読んで使う。必要なパス、PR 番号、候補名だけを置換し、期待する結論、本体の推測、採点意図、成功させたい候補は追記しない。

## 安全規則

- `docs/aat/algebraic_geometric_theory/`、`docs/sft/software_field_theory.md`、`docs/sft/aat_interface.md`、docs/note は編集しない。本文への取り込みや canonical への昇格はループ外で人間が判断する。
- `research/GOALS.md` は research-loop 中に編集しない。GOAL の昇格、終了、threshold policy、rubric、frontier、spine、research mode、target theorem、target theorem completion criteria、target premise discharge policy、target failure policy の改訂は人間判断であり、必要なら提案として tracking Issue または別 Issue に残す。active threshold の設定・変更は tracking Issue にコメントとして残す。
- AAT の内側に source observation、measurement tooling、ArchMap validation の完全性 claim を持ち込まない。
- Lean の依存は `Formal/AG/Research` から `Formal/AG` への一方向に保つ。`Formal/AG` 本体は参照のみ可とし、このループでは直接編集しない。
- `axiom`、予想以外の `sorry`、`unsafe` を相談なく持ち込まない。
- tracking Issue は研究状態の正本であり、明示的な人間指示なしに `Closes` で閉じない。
- staged diff と unstaged diff の両方を検査し、未追跡ファイルを確認してから PR を出す。
- 破壊的な git 操作(`reset --hard`、`checkout --`、force push)は使わない。
- `.lake` を一時出力置き場に使わない。一時出力は `.tmp/` または `/private/tmp` に置く。

## 報告

終えるときは、日本語で次を短く報告する。

1. 停止条件または継続状態。
2. 今サイクルの picked 候補、種別、証拠段階。
3. 確定 SCORE、カテゴリ、total SCORE。
4. PR とマージ結果。
5. GOAL に対する実質的 delta。
6. 次に狙うべき高 SCORE frontier。
7. `target-theorem` では target proof state、完了 support node、未完 support node、次の proof obligation。
