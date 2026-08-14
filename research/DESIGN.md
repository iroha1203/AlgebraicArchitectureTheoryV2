# DESIGN — 設計の理由

この文書は、研究ループ(候補を生成し、価値を審判し、Lean 検証または証拠固定を行い、SCORE を確定してフェーズの区切りまで回す仕組み)をいまの形にした理由を記録する。一見遠回りに見える判断にもそれぞれ背景があり、設計を見直すときはここを起点にできる。探索型の手順は [`$research-loop` の定義](../.codex/skills/research-loop/SKILL.md)、大定理証明の手順は [`$target-theorem-loop` の定義](../.codex/skills/target-theorem-loop/SKILL.md) に、全体の地図は [README](README.md) にある。

**GOAL を、研究で成し遂げたい能力として据える。** GOAL は証明したい定理の一覧ではない。ループは、GOAL のもとで定理、反例、構成、不変量、比較、計算可能性結果、予想の鋭化を探索する。候補が真であるだけでは足りず、その候補によって GOAL の能力がどう増えたかを SCORE として読む。

**SCORE を theorem count ではなく研究貢献に与える。** 定理数、ファイル数、証明の容易さは主報酬ではない。主報酬は、GOAL の見方を変えること、複数の現象を圧縮すること、新しい測定量や obstruction を作ること、次の研究を開くことに与える。証拠段階は multiplier であり、Lean proof は研究価値を検証する強い証拠として扱う。

**大定理証明モードを、SCORE 積み上げとは別の skill として分離する。** SCORE phase は広い frontier を探索し、研究能力の増分を積み上げるのに向いている。一方で、特定の大定理へ向かう研究では、毎サイクル一つの proof obligation を潰し、Lean theorem / finite witness / concrete certificate または blocker として固定する方が速く厳密である。このため `$research-loop` は探索型 GOAL 専用にし、`research mode: target-theorem` の GOAL は `$target-theorem-loop` で扱う。GOAL カードには target theorem、proof boundary、proof obligation priority、completion criteria を定義し、tracking Issue には proof state、完了 / 未完 proof obligation、blocker、PR、final review 結果を置く。target theorem の statement や completion criteria は人間が定める GOAL 定義であり、ループはそれを弱めて成功扱いしない。

**PRレビューと大定理の完了判定を分ける。** 各PRは標準`$review-pr`で差分を監査する。完了候補は別の`$math-lean-review`4本で固定GOALと累積証拠を照合し、PRレビューの判定を代用しない。全査読を完了できない、coverage gapが残る、reviewer vetoがある、または`No major findings`以外ならcheckpointとする。

**候補は四審判で落とす。** 審判 A は厳密性と claim boundary を見る。審判 B は GOAL への研究価値を見る。審判 C は repo 全体の価値、つまり AAT / SFT / Tooling / Website / Research の全体像に照らした自然さを見る。審判 D は GOAL の `rival` に対する有効性を見る。四者のどれかを通らない候補は、正しくても picked にしない。

**ライバルを GOAL の報酬関数に入れる。** 研究成果は、内部的に綺麗な定式化であるだけでは足りない。静的解析器、ADL 解析器、architecture conformance checker、metric dashboard など、既存の強い相手がすでに与える能力を踏まえ、その相手に対して何を新しく扱えるかで評価する。候補カード、G2 審判 D、G4 SCORE 監査、report の `rival_delta` を連動させることで、既存手法の言い換えを高 SCORE にしない。

**Lean をループの中の検証ゲートにする。** 生成した主張をそのまま信じないために、対象fileのfocused elaboration、必要なtargeted module check、公理検査、Lean 形式化品質監査を通してからレポートに残す。定理候補は証明の穴(sorry)を残さず完全に証明し、予想は結論部だけを sorry で保留する。Lean 形式化品質監査では、命題が強すぎて自明化していないか、弱すぎて元の主張を失っていないか、claim boundary が型と仮定に反映されているかを見る。

**検証は独立したライブラリ `ResearchLean` で行う。** 研究中のLean証拠を正式版`Formal/AG`から分離し、対象fileと必要なtargeted moduleだけを検証する。Research package全体、全Research module、aggregate root、全file loopのelaborationは実行しない。受理はfixed headに結びつくfocused結果、全報告宣言のaxiom audit、placeholder scan、独立PR reviewで判定する。依存は`ResearchLean`から`Formal/AG`への一方向だけに限り、`Formal/AG`本体はこのループでは参照のみとする。

**状態の正本は tracking Issue 一つに集める。** active SCORE threshold、current SCORE、カテゴリ別 SCORE、サイクル履歴は tracking Issue の状態である。`goals/<goal-id>.md` の GOAL 定義、探索型 GOAL の候補カード frontmatter、target-theorem の cycle result、検証結果のレポートはいずれも証拠 artifact であり、進行状態そのものではない。リポジトリの中にもう一つruntime台帳を作らない。target-theoremのcycle resultは実装PRに含め、merge後にtracking Issueへ索引する。

**停止は通常 GOAL では完全達成ではなく研究フェーズの区切りとして読む。** 通常 GOAL は、完全達成を機械的に判定できる性質のものではない。tracking Issue の active SCORE threshold、portfolio constraint、phase boundary criteria を満たしたら、独立審判が「ここで整理・執筆・次フェーズ設計へ移る方が研究としてキリが良いか」を判定する。フェーズ区切りなら Issue は閉じず、phase summary を残して人間に返す。`target-theorem` GOAL では例外的に、GOAL カードの completion criteria を満たし、かつ `$math-lean-review` gate を通った target theorem proof が完了条件になる。ただし、この場合も tracking Issue の closure は人間判断であり、ループは proof completion summary を残して返す。

**完了 GOAL の Lean 成果物は退役させ、現役 tree には進行中の研究だけを置く。** 検証ゲートの合格は受理時点の固定 head に紐づく事実であり、成果物を現在の基礎語彙へ追随させ続けても研究価値は増えない。追随を義務にすると基礎語彙の改訂のたびに完了済み研究へ移行費が発生し、放置すると「受理済み証拠」を名乗る Lean が elaborate しない状態になる。どちらも避けるため、完了 GOAL の成果物は markdown 記録と Git 履歴に証拠を固定して退役する。条件と手順は [README](README.md) の「Lean 成果物の退役」を正本とする。

**research はトップレベルに置き、検証結果は `research/reports/` にまとめる。** docs は読むための場所、research は手を動かす場所という住み分けである。検証または証拠固定を経た結果は `research/reports/` に置き、メモにすぎない docs/note には置かない。AAT の数学本文への取り込みや正式版への昇格をループの外に置くのは、検証ゲートでは判定できない人間の判断、すなわち本文へどう位置づけるかや理論との整合を、ループの不変条件に紛れ込ませないためである。

**GOAL id はグローバル通し番号にする。** 当初の id は `G-<領域>-<テーマ>-<連番>` で、会話や文書では `G-06` のような短い略称に潰れていた。テーマ内連番は同じ短い番号を領域・テーマごとに再生産するため略称が一意にならず、周辺文書の定理番号などの他の採番体系とも紛れやすい。そこで G-101 以降、`G-<NNN>-<領域>-<テーマ>`(NNN は領域をまたぐ3桁の通し番号)へ移行した。101 開始は旧略称の数字帯と重ならない帯を選ぶためであり、既存カードは改名しない(既存文書のリンクと略称を壊さないことを、遡及的な一貫性より優先する)。
