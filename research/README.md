# research — ループ研究の作業場

この `research/` は、AAT / SFT(代数的アーキテクチャ理論とソフトウェア場の理論)の数学を研究として育てていくための作業場である。確定した内容を読むための `docs/` に対して、こちらは候補を出し、検証し、研究貢献を SCORE として積み上げていく場所、つまり手を動かす側にあたる。

研究は、ひとつの研究 GOAL のもとで進める。通常の GOAL は「証明したい定理の一覧」ではない。文字通り、研究で成し遂げたい能力や到達像である。たとえば「アーキテクチャ品質を定量的に計測できるようにする」のように、理論が獲得すべき力を表す。例外として、GOAL カードが `research mode: target-theorem` を持つ場合は、その能力を代表する一つの大定理を GOAL カードで定義し、その証明を完了条件にしてよい。

その GOAL のもとで、次の流れを繰り返す。

```text
GOAL(研究で成し遂げたいこと)
  → 候補を出す
  → 四審判が価値とライバルに対する有効性を判定する
  → Lean 検証または証拠固定を行う
  → SCORE を監査して report / PR にまとめる
  → 研究フェーズとしてキリが良ければ止まり、そうでなければ同じ GOAL で次へ進む
```

`target-theorem` の GOAL では、探索型ループとは別に大定理証明専用ループを使う。SCORE と候補カードは使わず、次に潰す proof obligation を一つ選び、Lean theorem / finite witness / concrete certificate または blocker として固定する。完了条件は GOAL カードの `target theorem completion criteria` を満たすことであり、target theorem 本体が未証明なら checkpoint に留める。完了判定では final_review_packet を作り、`$math-lean-review` の 4 並列査読を必須 gate にし、実行できない場合、reviewer veto がある場合、または `No major findings` 以外の場合は `target-theorem-proved` にしない。

探索型の流れを自動で回すのが `$research-loop` であり、`$research-loop <goal-id>` で起動する。`research mode: target-theorem` の GOAL は `$target-theorem-loop <goal-id>` で起動する。回せるのは active な GOAL だけで、draft を active に昇格させるのは人間が判断する。各段のゲート、止まる条件、安全規則は、探索型は [`$research-loop` の定義](../.codex/skills/research-loop/SKILL.md)、大定理証明型は [`$target-theorem-loop` の定義](../.codex/skills/target-theorem-loop/SKILL.md) にある。

## 置き場所

研究の途中で生まれるものは、役割ごとに次の場所へ分けて置く。

| 場所 | 置くもの |
| --- | --- |
| `goals/README.md` | GOAL 一覧、GOAL card contract、運用規則 |
| `goals/<goal-id>.md` | 個別 GOAL の静的定義と reward function。`target-theorem` では target theorem、proof scope、proof obligation priority、completion criteria、failure policyもここに置く |
| `ideas/` | 候補を一件ずつ書いたカード。選にもれたものや保留は `ideas/archived/` へ移す |
| `reports/` | GOAL の能力がどう増えたかを書くレポート。GOAL ひとつにつき一つ |
| `DESIGN.md` | この仕組みをいまの形にした理由の記録 |
| `research/lean/ResearchLean/` | Lean による検証の作業場。`Formal/AG` には入れず、`research/lean` の独立 package に置く。`Formal/AG` 本体は参照のみ可 |

2026-07-12 の Research Lean package 移動に伴い、それ以前の ideas / reports にある
filesystem path と検証 command は、移動後に再利用できる同等手順へ正規化している。
移動前の日付に付いた `pass` は当時の実行結果を表し、正規化後の command を再実行したという
意味ではない。現行の focused check は
`cd research/lean && lake env lean ResearchLean/AG/<file>.lean` とする。
Research Lean の配置と検証手順は、この README、`lean/README.md`、両 package の
`lakefile.toml`、`.github/workflows/lean.yml` を現行 source of truth とする。

## 状態の正本

ループの進行状態の正本は、GOAL ごとに一本立てる GitHub の tracking Issue `Research Loop: <goal-id>` に置く。候補ごと、サイクルごとの tracking Issue は作らず、探索型 GOAL では active SCORE threshold、current SCORE、候補カード、PR、iteration comment をこの Issue に集約する。`goals/<goal-id>.md` は GOAL 定義、カードの frontmatter と検証結果のレポートは証拠 artifact であり、作業を中断してもこの Issue を読めば同じ地点から再開できる。`target-theorem` では候補カードを作らず、target theorem の statement と completion criteria は `goals/<goal-id>.md` が正本で、tracking Issue には proof state、完了 / 未完 proof obligation、blocker、PR、target_cycle_result、`$math-lean-review` の completion gate 結果を置く。

tracking Issue は、通常 GOAL の「完全達成」を機械的に閉じるためのものではない。tracking Issue の active SCORE threshold、portfolio constraint、phase boundary criteria を満たしたら、研究フェーズとしてキリが良いかを判定し、phase summary を残して人間に返す。GOAL を閉じる、次フェーズへ移す、reward rubric を改訂する、といった判断はループ外で行う。`target-theorem` では、GOAL カードの completion criteria を満たし、さらに `$math-lean-review` gate を通った場合だけ `target-theorem-proved` として止まる。target が未証明、または `$math-lean-review` が通らない場合は checkpoint にすぎない。

GOAL は `rival` を持つ。`rival` は、その GOAL が比較対象にする既存概念、手法、tooling、理論枠組みである。候補は GOAL の内部で面白いだけでなく、rival がすでに得意なことを踏まえ、どの能力で優位性、新規性、統合力、分離力、検証可能性を作るかを示す。G2 では審判 D がこの比較を担当し、rival の言い換えに留まる候補を落とす。

## 候補カードの状態

探索型 GOAL の候補カードは一件につき一ファイルとし、frontmatter で二つの状態を持つ。`target-theorem` GOAL では候補カードを作らず、cycle result を report と tracking Issue に同期する。

ひとつは候補そのものの進み具合を表す `status` で、生成された時点の `idea` から、四審判を通った `picked`、選にもれたか検証に失敗した `archived` へと移る。もうひとつは証拠段階を表す `evidence_stage` で、`proved-in-research`、`conjectured-sorry`、`finite-evidence`、`orientation-evidence` などをとる。

Lean に関する細かい段階を記録する場合は、補助的に `lean` を使ってよい。値は `none`、`stated`、`conjectured-sorry`、`proved-in-research`、`failed` とする。ただし SCORE は Lean ファイル数や定理数ではなく、GOAL の能力がどう増えたかに対して与える。
