# DESIGN — 設計の理由

この文書は、研究ループ(候補を生成し、価値を審判し、Lean 検証または証拠固定を行い、SCORE を確定してフェーズの区切りまで回す仕組み)をいまの形にした理由を記録する。一見遠回りに見える判断にもそれぞれ背景があり、設計を見直すときはここを起点にできる。実際の手順は [`$research-loop` の定義](../.codex/skills/research-loop/SKILL.md)に、全体の地図は [README](README.md) にある。

**GOAL を、研究で成し遂げたい能力として据える。** GOAL は証明したい定理の一覧ではない。ループは、GOAL のもとで定理、反例、構成、不変量、比較、計算可能性結果、予想の鋭化を探索する。候補が真であるだけでは足りず、その候補によって GOAL の能力がどう増えたかを SCORE として読む。

**SCORE を theorem count ではなく研究貢献に与える。** 定理数、ファイル数、証明の容易さは主報酬ではない。主報酬は、GOAL の見方を変えること、複数の現象を圧縮すること、新しい測定量や obstruction を作ること、次の研究を開くことに与える。証拠段階は multiplier であり、Lean proof は研究価値を検証する強い証拠として扱う。

**大定理証明モードを、SCORE 積み上げとは別の制御ループとして持つ。** SCORE phase は広い frontier を探索し、研究能力の増分を積み上げるのに向いている。一方で、特定の大定理へ向かう研究では、補題や反例の価値を SCORE で測りつつ、完了条件を「target theorem の証明」に置く必要がある。このため GOAL カードに `research mode: target-theorem`、target theorem、proof boundary、support map、completion criteria を定義できるようにし、tracking Issue には proof state と support node の進行状態を置く。target theorem の statement や completion criteria は人間が定める GOAL 定義であり、ループはそれを弱めて成功扱いしない。

**候補は四審判で落とす。** 審判 A は厳密性と claim boundary を見る。審判 B は GOAL への研究価値を見る。審判 C は repo 全体の価値、つまり AAT / SFT / Tooling / Website / Research の全体像に照らした自然さを見る。審判 D は GOAL の `rival` に対する有効性を見る。四者のどれかを通らない候補は、正しくても picked にしない。

**ライバルを GOAL の報酬関数に入れる。** 研究成果は、内部的に綺麗な定式化であるだけでは足りない。静的解析器、ADL 解析器、architecture conformance checker、metric dashboard など、既存の強い相手がすでに与える能力を踏まえ、その相手に対して何を新しく扱えるかで評価する。候補カード、G2 審判 D、G4 SCORE 監査、report の `rival_delta` を連動させることで、既存手法の言い換えを高 SCORE にしない。

**Lean をループの中の検証ゲートにする。** 生成した主張をそのまま信じないために、`lake build`、公理検査、Lean 形式化品質監査を通してからレポートに残す。定理候補は証明の穴(sorry)を残さず完全に証明し、予想は結論部だけを sorry で保留する。Lean 形式化品質監査では、命題が強すぎて自明化していないか、弱すぎて元の主張を失っていないか、claim boundary が型と仮定に反映されているかを見る。

**検証は独立したライブラリ `FormalAGResearch` で行う。** Lean のライブラリ `Formal` は起点から参照を辿って到達するファイルしかビルドしないため、どこからも参照されていない壊れたファイルがあっても `lake build Formal` は通ってしまう。これでは検証の合否を判定できない。そこで `Formal/AG/Research/` のすべてのファイルをビルドする独立したライブラリを用意し、その成否を合格の信号とする。正式版である `Formal/AG` とは疎結合に保ち、依存は `Formal/AG/Research` から `Formal/AG` への一方向だけに限る。`Formal/AG` 本体は参照のみ可とし、このループでは直接編集しない。

**状態の正本は tracking Issue 一つに集める。** active SCORE threshold、current SCORE、カテゴリ別 SCORE、サイクル履歴は tracking Issue の状態である。GOALS.md の GOAL 定義、候補カードの frontmatter、検証結果のレポートはいずれも証拠 artifact であり、進行状態そのものではない。リポジトリの中にもう一つ台帳を置くと、サイクルのたびに両者がずれていく。だからサイクルの履歴と threshold 設定は Issue のコメントとして残し、そのための専用ファイルは作らない。

**停止は通常 GOAL では完全達成ではなく研究フェーズの区切りとして読む。** 通常 GOAL は、完全達成を機械的に判定できる性質のものではない。tracking Issue の active SCORE threshold、portfolio constraint、phase boundary criteria を満たしたら、独立審判が「ここで整理・執筆・次フェーズ設計へ移る方が研究としてキリが良いか」を判定する。フェーズ区切りなら Issue は閉じず、phase summary を残して人間に返す。`target-theorem` GOAL では例外的に、GOAL カードの completion criteria を満たす target theorem proof が完了条件になる。ただし、この場合も tracking Issue の closure は人間判断であり、ループは proof completion summary を残して返す。

**research はトップレベルに置き、検証結果は `research/reports/` にまとめる。** docs は読むための場所、research は手を動かす場所という住み分けである。検証または証拠固定を経た結果は `research/reports/` に置き、メモにすぎない docs/note には置かない。AAT の数学本文への取り込みや正式版への昇格をループの外に置くのは、検証ゲートでは判定できない人間の判断、すなわち本文へどう位置づけるかや理論との整合を、ループの不変条件に紛れ込ませないためである。
