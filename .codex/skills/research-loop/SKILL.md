---
name: research-loop
description: 研究 GOAL に対して、定理候補・反例・構成・不変量を探索し、Lean 検証、ライバル比較、独立審判で研究貢献 SCORE を確定しながら反復する研究ループ。Use when the user says "$research-loop <goal-id>", "研究ループを回して", or wants Codex to autonomously search, score, prove, compare against rivals, report, and PR research contributions toward a standing research goal.
---

# Research Loop

この skill は、研究 GOAL に向けて候補を探索し、価値の高いものを Lean で検証し、研究貢献 SCORE を積み上げるためのループである。応答、Issue、PR はすべて日本語で行う。

GOAL は「証明したい定理の一覧」ではない。GOAL は文字通り、研究で成し遂げたい能力や到達像である。たとえば AAT なら「アーキテクチャ品質を定量的に計測できるようにする」のように、理論が獲得すべき力を表す。skill が行うのは、その GOAL に貢献する定理、反例、構成、不変量、比較、計算可能性結果、予想の鋭化を探し、証拠に応じて SCORE を確定することである。

Lean proof は主報酬ではない。Lean は成果の信頼度を上げる検証ゲートである。主報酬は、GOAL の能力をどれだけ増やしたか、見方をどれだけ変えたか、複数の現象をどれだけ圧縮したか、次の研究をどれだけ開いたか、ライバルとなる既存概念に対してどれだけ有効な差分を作ったかに対して与える。

## 入口

起動は `$research-loop <goal-id>` とする。`goal-id` は [research/GOALS.md](../../../research/GOALS.md) の active な GOAL を指す。任意で `max-cycles <N>`、対象カテゴリ、探索寄りまたは証明寄りの指示を渡してよい。

最初に次を読む。

- [research/README.md](../../../research/README.md)
- [research/GOALS.md](../../../research/GOALS.md)
- [research/ideas/TEMPLATE.md](../../../research/ideas/TEMPLATE.md)
- [research/reports/README.md](../../../research/reports/README.md)
- [research/DESIGN.md](../../../research/DESIGN.md)

GOAL が active でなければ Issue を作らずに止まる。draft を active に昇格させるのは人間の判断である。

`research/GOALS.md` は research-loop の不変入力として扱う。この skill は GOAL 本文、`status`、`rival`、`score threshold`、`portfolio constraint`、`reward rubric`、`spine`、`frontier` を直接編集しない。欠陥を見つけた場合は `goal defect` として止まり、tracking Issue コメントまたは別 Issue に改訂案を書く。

## GOAL の型

active な GOAL は、候補を落とすための報酬関数を持つ。足りない場合は「goal 欠陥」として止まり、改訂案を報告する。

GOAL には次を要求する。

- `id` と `status: active`。
- `research aim`: 研究で成し遂げたい能力や到達像。
- `core tension`: 何が分かれば本当に非自明で、何が解ければ理論の景色が変わるか。
- `rival`: この GOAL が比較対象にする既存概念、手法、tooling、理論枠組み。候補は、この rival が得意なことを把握したうえで、どの能力で勝つ、統合する、分離する、または測定可能にするのかを述べる。
- `claim boundary`: どの語彙、law universe、coverage topology、係数、profile の上で語るか。
- `capability categories`: SCORE を配分する能力カテゴリ。例: quantity、invariance、computability、interpretation、obstruction、unification。
- `score threshold`: ひとつの研究フェーズを区切るために必要な合計 SCORE。
- `portfolio constraint`: ひとつの方向だけで点を稼いでフェーズを区切らないための条件。例: 3 カテゴリ以上で正の SCORE、最低 1 件は Lean proved。
- `phase boundary criteria`: 研究としてキリが良いと判定する条件。例: coherent な report section / paper seed になる、主要な insight が揃った、次は探索より整理が有利である。
- `reward rubric`: SCORE の採点規則。
- `dullness filter`: 定義展開、既存定理の即時系、名前替え、小補題量産を弾く基準。
- `frontier`: 探索してよい周辺領域。反例、obstruction、予想の強化、新しい不変量、別領域との橋を含めてよい。

`spine` を置いてもよいが、それは固定計画ではなく現在の仮説として扱う。探索結果が spine を壊す、鋭くする、置き換えるなら、それ自体を高く評価する。

## SCORE の原則

SCORE は研究能力の増分に対して与える。証明数、ファイル数、定理数には与えない。

基本点は、候補が GOAL に与える価値で決める。

- `0`: 定義展開、既存結果の言い換え、GOAL の能力を増やさない局所補題。
- `10-20`: 小さいが必要な補助結果。単独では GOAL の景色を変えない。
- `30-40`: 新しい測定量、構成、比較、計算手段を与え、既存の AAT 構造と接続する。
- `50-70`: 複数の品質概念、obstruction、cohomology、metric、lawfulness を一つの枠で説明する。
- `80-100`: 反例、obstruction、新しい不変量、主定理候補により、GOAL の見方や到達像を変える。

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
4. 未完の PR があれば新しいブランチを切らずに続ける。
5. tracking Issue から現在の SCORE、カテゴリ別 SCORE、直近サイクル、停止条件を読む。

GOAL 定義の正本は `research/GOALS.md` に置くが、ループ中は read-only invariant として扱う。実行状態の正本は GitHub の tracking Issue に置く。候補 frontmatter とレポートは証拠 artifact である。README や committed docs を頻繁に変わる台帳にしない。

### G1 探索と候補生成

候補生成では、spine を埋めるものだけでなく、GOAL の見方を変えるものを探す。毎サイクル、可能なら性質の異なる候補を複数出す。

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

候補カードは [research/ideas/TEMPLATE.md](../../../research/ideas/TEMPLATE.md) に従って `research/ideas/` に置く。frontmatter か本文に次を必ず書く。

```text
goal:
candidate_type:
capability_category:
expected_base_score:
expected_evidence_multiplier:
expected_final_score:
score_reason:
mathematical_interest:
goal_advancement:
dullness_risk:
proof_or_evidence_plan:
planned_theorem_names:
rival_advantage:
visible_projection:
protected_structure:
exactness_or_minimality_claim:
nonfaithfulness_or_failure_mode:
previous_cycle_delta:
```

### G2 価値スコア審判

四人の独立サブエージェントに審判させる。渡すのは GOAL、候補カード、GOAL の `rival`、関連する既存結果、reward rubric、dullness filter、必要な repo overview だけにする。本体の期待や途中判断は渡さない。

審判 A は厳密性を見る。

- claim boundary を守っているか。
- 既存結果の即時系や名前替えではないか。
- 証明または反例の筋が破綻していないか。
- Lean で狙う命題が候補の主張を弱めていないか。

審判 B は研究価値を見る。

- GOAL の能力を増やすか。
- core tension を閉じる、鋭くする、壊す、置き換えるか。
- surprise、compression、leverage があるか。
- paper の節または主定理候補になりうるか。

審判 C はプロジェクト全体の価値を見る。

- AAT / SFT / Tooling / Website / Research の全体像に照らして価値があるか。
- repo の現在の source of truth、claim boundary、公開面、研究計画に対して自然な前進か。
- 局所的には面白くても、プロジェクトの主軸から外れすぎていないか。
- 将来の docs、Lean、paper、tooling surface のいずれかに接続する見込みがあるか。

審判 D はライバル比較を見る。

- GOAL の `rival` がすでに提供する能力を正しく捉えているか。
- 候補が rival に対して、どの能力で優位性、新規性、統合力、分離力、検証可能性を持つか。
- rival が得意な静的検出、ADL 構造解析、architecture conformance、metric dashboard などの水準を、単に別名で繰り返していないか。
- rival では取り落とす support、transport、obstruction、trace、repair、failure mode のうち何を新しく扱えるか。

各審判は次の形式で返す。

```text
verdict: accept | revise | reject
base_score:
category:
reason:
dullness_risk:
required_evidence:
checked:
unchecked:
```

四者が `accept` した候補のうち、期待 SCORE、研究価値、rival に対する有効性が最も高いものを picked にする。A が `reject` した候補は数学的に進めない。B が `reject` した候補は GOAL に貢献しない。C が `reject` した候補は repo 全体の研究価値が不足している。D が `reject` した候補は rival に対する新規性または有効性が不足している。正しいが低 SCORE の候補は、必要な補助結果でない限り採らない。`revise` は一度だけ直して再審判する。審判が exactness、minimality、nonfaithfulness、typed transport、preservation/reflection、rival separation などを要求した場合は、G3 へ進む前に候補カードと Lean 予定 statement に明示する。`reject` は `status: archived` とし、理由を残す。

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

G4 へ進む前に、候補カード、証拠、Lean declaration、審判メモを同期する。候補カードは生成時の期待値ではなく、実際に固定された証拠の index として読める状態にする。

候補カードには最低限、次を反映する。

- `status: picked`。
- 実際の `evidence_stage`。
- 実際に通った Lean ファイルと declaration 名。
- G3 後の `expected_base_score`、`expected_evidence_multiplier`、`expected_final_score`。期待値が実証済みの証拠とかけ離れていれば下げる。
- proof/evidence plan の実績化。予定ではなく、何が証明され、何が証明されていないかを書く。
- exactness、minimality、nonfaithfulness、failure mode、typed transport、preservation/reflection など、G2/G3 で追加要求された構造。
- 審判 D が要求した rival separation と、実際の証拠が rival に対して何を示したか。
- `#print axioms` と Lean 形式化品質監査の要約。
- resolved revise と残った unchecked。

候補カード、Lean declaration、report に載せる theorem 名、SCORE 監査入力がずれている場合は G4 に進まない。

### G4 SCORE 確定とレポート

検証と G3.5 同期後、独立サブエージェントに SCORE 監査を行わせる。渡すのは GOAL、GOAL の `rival`、同期済み候補カード、証拠、G2 の四審判結果、G3 の監査結果、diff だけにする。

監査は次を返す。

```text
score_verdict: confirm | reduce | reject
base_score:
evidence_multiplier:
penalty:
final_score:
category:
goal_delta:
rival_delta:
project_value_delta:
formalization_quality:
reason:
checked:
unchecked:
```

`confirm` または `reduce` の場合だけ `research/reports/<goal-id>.md` に書く。レポートは定理一覧ではなく、GOAL の能力がどう増えたかを書く。レポート、カテゴリ別 SCORE、total SCORE、proof portfolio、cycle section、Next Frontier / phase boundary メモは、候補カードの期待値ではなく G4 監査後の値で同時に更新する。

各成果には次を残す。

- 候補名と種別。
- 証拠段階: `proved-in-research`、`conjectured-sorry`、`finite-evidence`、`orientation-evidence` など。
- final SCORE とカテゴリ。
- GOAL に対する delta。
- rival に対する delta。
- まだ開いている問い。

### G5 PR レビューとマージ

ひとつの picked の成果をひとつの PR にまとめる。PR には候補カード、Lean ファイルまたは証拠、レポート、tracking Issue の SCORE 更新を含める。

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

### G6 研究フェーズ区切り判定

PR マージ後、tracking Issue に iteration コメントを残す。

```text
cycle N: picked <candidate> / type <type> / score +S(category C) / total T / evidence E / PR #Y merged|open|blocked / stop continue|<停止条件名>
```

続いて独立サブエージェントに研究フェーズ区切り判定を行わせる。渡すのは GOAL、tracking Issue の SCORE 台帳、レポート、カテゴリ別 SCORE、証拠段階、phase boundary criteria だけにする。本体の期待は渡さない。

GOAL は「完全達成」を判定する対象ではない。判定するのは、この時点でひとつの研究フェーズとして区切るだけの成果とまとまりがあるかである。フェーズを区切るには次を満たす。

- total SCORE が `score threshold` 以上。
- `portfolio constraint` を満たす。
- 低 SCORE の補助結果だけで到達していない。
- report が coherent な節または paper seed として読める。
- report が GOAL の `rival` に対して、このフェーズの成果がどの能力で有効かを説明している。
- 独立審判が、GOAL の研究能力が実質的に増え、次のサイクルを続けるより整理・執筆・次フェーズ設計へ移る方が研究としてキリが良いと判定する。

フェーズ区切りなら Issue は閉じず、phase summary コメントを残して止まる。phase summary には、merged PR、merge commit、cycle ごとの SCORE、total SCORE、threshold、portfolio constraint、rival に対する phase delta、CI / 独立レビュー結果、report の現在地、次の frontier、人間に返す判断を含める。最後に tracking Issue が open のままであることを確認する。GOAL を閉じる、次フェーズへ移す、reward rubric を改訂する、別 GOAL を立てる、といった判断は人間に返す。区切りでなければ同じ GOAL で次サイクルへ戻る。

## 停止条件

止まることは失敗ではない。止める理由を tracking Issue に残し、人間へ返す。

サイクル段階で止まる条件は次である。Issue は閉じない。

- `low-value stagnation`: 二サイクル続けて期待 final SCORE が 30 未満の候補しか出ない。
- `proof stagnation`: 高 SCORE 候補はあるが、二サイクル続けて証拠固定に失敗する。
- `review stagnation`: 同じ PR が二巡してもマージ可能にならない。
- `score dispute`: 独立審判間で SCORE が大きく割れ、根拠を読んでも解消できない。
- `undecidable`: diff、CI、Lean 検証、証拠、tracking Issue のいずれかが確認できない。

フェーズ段階または GOAL 運用段階で止まる条件は次である。GOAL の tracking Issue は原則閉じない。GOAL の打ち切りや完了扱いは人間の判断である。

- `phase boundary`: SCORE threshold、portfolio constraint、phase boundary criteria を満たし、研究としてキリが良い。
- `exhausted`: frontier を探索しても、非自明な高 SCORE 候補が尽きた。
- `max-cycles`: 指定された回数上限に達した。
- `goal defect`: GOAL の reward rubric、claim boundary、threshold、portfolio constraint に欠陥がある。
- `all blocked`: 残る高 SCORE 候補が、人間の判断、理論上の未解決問題、外部入力を待っている。

## サブエージェント規律

候補生成、G2 審判 A/B/C/D、G3 公理検査、G3 Lean 形式化品質監査、G4 SCORE 監査、G5 PR レビュー、G6 フェーズ区切り判定は、独立したサブエージェントに行わせる。サブエージェントを使えない環境では止まり、人間のレビューに委ねる。

サブエージェントには、対象ファイル、GOAL、rubric、claim boundary、必要な証拠だけを渡す。本体の期待、推測、採点意図、成功させたい候補は渡さない。返答には `checked` と `unchecked` を必ず含めさせる。未確認の項目を合格やフェーズ区切りに倒さない。

## サブエージェント標準プロンプト

各サブエージェントには、次のプロンプトを必要なパス、PR 番号、候補名に置換して渡す。期待する結論や本体の推測は追記しない。

**G1 候補生成**

```text
Use the research-loop criteria to generate candidate research contributions for GOAL <goal-id>.
Read only: research/GOALS.md, research/ideas/TEMPLATE.md, research/reports/<goal-id>.md if it exists, and the source references explicitly named by the GOAL.
Do not edit files.
Generate mathematically nontrivial, interesting candidates that create visible progress toward the GOAL. Avoid definition unfolding, immediate corollaries, renaming, vague conjectures, and candidates whose value is only that they look easy to formalize.
Return 5 candidates. For each candidate, provide:
title:
candidate_type: closure | orientation | unification | computability | bridge
capability_category:
claim:
why_nontrivial:
mathematical_interest:
goal_advancement:
rival_advantage:
expected_base_score:
expected_evidence_multiplier:
expected_final_score:
score_reason:
dullness_risk:
proof_or_evidence_plan:
planned_theorem_names:
visible_projection:
protected_structure:
exactness_or_minimality_claim:
nonfaithfulness_or_failure_mode:
previous_cycle_delta:
checked:
unchecked:
```

**G2 審判 A: 厳密性**

```text
Judge this candidate only for rigor and boundary fidelity.
Inputs: GOAL <goal-id>, candidate card <path>, reward rubric, dullness filter, and named source references.
Do not assume the candidate should pass.
Return:
verdict: accept | revise | reject
base_score:
category:
reason:
boundary_fidelity:
is_immediate_corollary_or_rename:
proof_or_counterexample_risk:
required_evidence:
checked:
unchecked:
```

**G2 審判 B: 研究価値**

```text
Judge this candidate only for research value toward GOAL <goal-id>.
Inputs: GOAL, candidate card <path>, reward rubric, dullness filter, current report if any.
Do not judge by ease of proof. Judge by surprise, compression, leverage, and GOAL capability gain.
Return:
verdict: accept | revise | reject
base_score:
category:
reason:
goal_delta:
surprise:
compression:
leverage:
paper_section_potential:
dullness_risk:
required_evidence:
checked:
unchecked:
```

**G2 審判 C: プロジェクト全体価値**

```text
Judge this candidate from the viewpoint of the whole repository and research program.
Inputs: GOAL <goal-id>, candidate card <path>, reward rubric, dullness filter, research/README.md, research/GOALS.md, docs/README.md, and other repo overview files explicitly named by the GOAL.
Do not judge only local mathematical interest. Judge whether this is valuable for AAT / SFT / Tooling / Website / Research as a whole.
Return:
verdict: accept | revise | reject
base_score:
category:
reason:
repo_wide_value:
alignment_with_project_sources:
future_surface: docs | Lean | paper | tooling | website | none
strategic_risk:
dullness_risk:
required_evidence:
checked:
unchecked:
```

**G2 審判 D: ライバル比較**

```text
Judge this candidate only against the GOAL's rival.
Inputs: GOAL <goal-id>, its rival field, candidate card <path>, reward rubric, dullness filter, and current report if any.
Do not judge by mathematical elegance alone. Judge whether the candidate creates a capability that the rival does not provide, combines rival capabilities into a stronger object, or gives a precise failure / nonfaithfulness / obstruction that the rival misses.
Return:
verdict: accept | revise | reject
base_score:
category:
reason:
rival_understanding:
advantage_over_rival:
novelty_against_rival:
not_merely_rival_rephrasing:
required_evidence:
checked:
unchecked:
```

**G3 公理検査**

```text
Check the Lean evidence for candidate <candidate>.
Inputs: candidate card <path>, Lean file <path>, GOAL claim boundary.
Run or inspect #print axioms for every declaration that will be reported as evidence.
For finite witness, computability, trace/support, repair frontier, or minimal counterexample claims, do not automatically treat propext/Classical.choice/Quot.sound as clean. If standard axioms remain, explain why the construction still deserves its evidence multiplier.
Confirm that Formal/AG is only imported/referenced and not edited by this loop.
Return:
verdict: pass | fail | cannot-determine
build_status:
axioms:
has_sorryAx:
allowed_axioms_only:
standard_axiom_justification:
fidelity_to_candidate:
formal_ag_boundary_ok:
reason:
checked:
unchecked:
```

**G3 Lean 形式化品質監査**

```text
Audit whether the Lean formalization is an appropriate formal expression of the candidate's mathematical claim.
Inputs: candidate card <path>, Lean file <path>, GOAL claim boundary, and the relevant theorem / definition names.
Do not judge only whether Lean builds. Check whether the statement captures the intended proposition at the right strength.
Return:
verdict: pass | revise | fail | cannot-determine
statement_matches_candidate:
not_too_weak:
not_too_strong_or_vacuous:
parameters_and_assumptions_explicit:
claim_boundary_encoded:
definitions_fit_for_reuse:
names_and_structure_clear:
formal_ag_boundary_ok:
reason:
checked:
unchecked:
```

**G3.5 候補カード同期**

```text
Audit whether candidate card <path>, Lean/evidence files, judge memos, and the planned report entry agree.
Inputs: GOAL <goal-id>, candidate card <path>, evidence files, G2 judge outputs including judge D rival comparison, G3 axiom check, G3 formalization quality audit.
Do not change the score. Check synchronization only.
Return:
verdict: synced | revise | fail | cannot-determine
status_is_picked:
evidence_stage_matches:
lean_declarations_match:
expected_scores_not_stale:
proof_plan_reflects_actual_evidence:
exactness_minimality_or_failure_mode_reflected:
rival_separation_reflected:
axiom_and_formalization_audits_summarized:
resolved_revises_recorded:
report_names_match:
reason:
checked:
unchecked:
```

**G4 SCORE 監査**

```text
Audit the final SCORE for candidate <candidate>.
Inputs: GOAL <goal-id>, GOAL rival, synchronized candidate card <path>, evidence files, G2 judge A/B/C/D outputs, G3 axiom check, G3 formalization quality audit, G3.5 sync audit, and current diff.
Do not preserve the proposed score unless the evidence supports it.
Return:
score_verdict: confirm | reduce | reject
base_score:
evidence_multiplier:
penalty:
final_score:
category:
goal_delta:
rival_delta:
project_value_delta:
formalization_quality:
research_kiri_contribution:
reason:
checked:
unchecked:
```

**G5 PR レビュー**

```text
Use $review-pr <PR-number> and apply the review-pr skill.
In addition to the normal PR review, check the research-loop gates:
- candidate card, evidence, report, and tracking Issue SCORE update agree
- SCORE audit is represented faithfully
- G2 judge D rival comparison and G4 rival_delta are represented faithfully
- Lean formalization quality audit is represented faithfully
- Formal/AG is not directly edited
- protected math docs and docs/note are not edited
- git diff --check, git diff --cached --check, and untracked-file hygiene were checked
- PR body uses Refs for the tracking Issue unless the human explicitly requested closure
- GitHub merge state is verified after merge attempts
Return the review-pr verdict and any research-loop-specific findings.
```

**G6 フェーズ区切り判定**

```text
Judge whether the current work forms a good research phase boundary for GOAL <goal-id>.
Inputs: GOAL, GOAL rival, tracking Issue SCORE ledger, research/reports/<goal-id>.md, category scores, evidence stages, phase boundary criteria.
Treat research/GOALS.md as a read-only invariant. If status, threshold, rubric, frontier, or spine should change, return that as a human action proposal.
Do not judge the GOAL as completely achieved. Do not close the tracking Issue. Judge whether this phase is coherent enough to stop and return to the human with a phase summary.
Return:
verdict: phase-boundary | continue | blocked | goal-defect
total_score:
portfolio_constraint:
coherent_report_or_paper_seed:
rival_phase_delta:
research_kiri:
phase_summary_required_fields:
tracking_issue_remains_open:
next_best_action:
reason:
checked:
unchecked:
```

## 安全規則

- `docs/aat/algebraic_geometric_theory/`、`docs/sft/software_field_theory.md`、`docs/sft/aat_interface.md`、docs/note は編集しない。本文への取り込みや canonical への昇格はループ外で人間が判断する。
- `research/GOALS.md` は research-loop 中に編集しない。GOAL の昇格、終了、threshold、rubric、frontier、spine の改訂は人間判断であり、必要なら提案として tracking Issue または別 Issue に残す。
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
