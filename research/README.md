# research — ループ研究の作業場

この `research/` は、AAT / SFT(代数的アーキテクチャ理論とソフトウェア場の理論)の数学を研究として育てていくための作業場である。確定した内容を読むための `docs/` に対して、こちらは候補を出し、検証し、研究貢献を SCORE として積み上げていく場所、つまり手を動かす側にあたる。

研究は、ひとつの研究 GOAL のもとで進める。GOAL は「証明したい定理の一覧」ではない。文字通り、研究で成し遂げたい能力や到達像である。たとえば「アーキテクチャ品質を定量的に計測できるようにする」のように、理論が獲得すべき力を表す。

その GOAL のもとで、次の流れを繰り返す。

```text
GOAL(研究で成し遂げたいこと)
  → 候補を出す
  → 四審判が価値とライバルに対する有効性を判定する
  → Lean 検証または証拠固定を行う
  → SCORE を監査して report / PR にまとめる
  → 研究フェーズとしてキリが良ければ止まり、そうでなければ同じ GOAL で次へ進む
```

この流れを自動で回すのが `$research-loop` であり、`$research-loop <goal-id>` で起動する。回せるのは active な GOAL だけで、draft を active に昇格させるのは人間が判断する。各段のゲート、止まる条件、安全規則は、すべて [`$research-loop` の定義](../.codex/skills/research-loop/SKILL.md)にある。

## 置き場所

研究の途中で生まれるものは、役割ごとに次の場所へ分けて置く。

| 場所 | 置くもの |
| --- | --- |
| `GOALS.md` | GOAL そのものと、候補を採点する reward function。threshold policy と phase boundary criteria もここに置く |
| `ideas/` | 候補を一件ずつ書いたカード。選にもれたものや保留は `ideas/archived/` へ移す |
| `reports/` | GOAL の能力がどう増えたかを書くレポート。GOAL ひとつにつき一つ |
| `DESIGN.md` | この仕組みをいまの形にした理由の記録 |
| `Formal/AG/Research/` | Lean による検証の作業場。`research/` には入れず、リポジトリ内の別ディレクトリに置く。`Formal/AG` 本体は参照のみ可 |

## 状態の正本

ループの進行状態の正本は、GOAL ごとに一本立てる GitHub の tracking Issue `Research Loop: <goal-id>` に置く。候補ごと、サイクルごとの tracking Issue は作らず、active SCORE threshold、current SCORE、候補カード、PR、iteration comment をこの Issue に集約する。`GOALS.md` は GOAL 定義、カードの frontmatter と検証結果のレポートは証拠 artifact であり、作業を中断してもこの Issue を読めば同じ地点から再開できる。

tracking Issue は、GOAL の「完全達成」を機械的に閉じるためのものではない。tracking Issue の active SCORE threshold、portfolio constraint、phase boundary criteria を満たしたら、研究フェーズとしてキリが良いかを判定し、phase summary を残して人間に返す。GOAL を閉じる、次フェーズへ移す、reward rubric を改訂する、といった判断はループ外で行う。

GOAL は `rival` を持つ。`rival` は、その GOAL が比較対象にする既存概念、手法、tooling、理論枠組みである。候補は GOAL の内部で面白いだけでなく、rival がすでに得意なことを踏まえ、どの能力で優位性、新規性、統合力、分離力、検証可能性を作るかを示す。G2 では審判 D がこの比較を担当し、rival の言い換えに留まる候補を落とす。

## 候補カードの状態

候補のカードは一件につき一ファイルとし、frontmatter で二つの状態を持つ。

ひとつは候補そのものの進み具合を表す `status` で、生成された時点の `idea` から、四審判を通った `picked`、選にもれたか検証に失敗した `archived` へと移る。もうひとつは証拠段階を表す `evidence_stage` で、`proved-in-research`、`conjectured-sorry`、`finite-evidence`、`orientation-evidence` などをとる。

Lean に関する細かい段階を記録する場合は、補助的に `lean` を使ってよい。値は `none`、`stated`、`conjectured-sorry`、`proved-in-research`、`failed` とする。ただし SCORE は Lean ファイル数や定理数ではなく、GOAL の能力がどう増えたかに対して与える。
