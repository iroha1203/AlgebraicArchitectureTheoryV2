# ArchSig AAT Analysis Engine PRD

この PRD は、ArchSig を AAT のための解析機として再設計するための要求を定義する。

ArchSig は、ArchMap を入力として、AAT 本文が扱う Atom、Configuration、ArchitectureObject、
Invariant、LawUniverse、ObstructionCircuit、ArchitectureSignature、Operation、Path、
Homotopy、Diagram、AnalyticRepresentation を、LLM と human reviewer が読める structured
artifact として出力する。

North Star は、巨大なコードベースを「読めない塊」から「設計判断できる構造体」へ変換する
ことである。ArchSig は、エンジニアが日々直面する設計理解、変更影響、レビュー、リファクタ、
技術的負債、AI 生成コードの統制というペインを、AAT の構造語彙で扱える問題へ変換する。

中心方針は次である。

```text
ArchMap
  -> ArchSig AAT analysis engine
  -> AAT analysis packet
  -> LLM interpretation
  -> human judgement / repair planning
```

ArchSig は静的解析器でも rule violation checker でもない。static extractor、AST scan、
import graph、runtime trace、manual annotation、LLM source reading は観測源であり、
ArchSig の責務は、それらを ArchMap に記録された Atom 観測として読み、AAT の構造語彙へ
持ち上げることである。

## 要求

### R0. AI 時代のアーキテクチャ品質計測を定義する

ArchSig のユーザーは、AAT の研究者ではなく一般のソフトウェアエンジニアである。
ユーザーは、自分のコードベースから生成した ArchMap を ArchSig に入力することで、
実装の表面的な lint 違反ではなく、開発現場で繰り返し発生する構造的ペインを扱える。

ArchSig が解くべき根本ペインは次である。

- **大規模コードベースが読めない**: 新任者、レビュアー、AI agent が、コードのどこに
  state、effect、authority、trust、contract、semantic boundary があるかを再構築するのに
  長い時間を使っている。
- **変更影響が読めない**: 小さな PR や feature extension が、どの workflow、boundary、
  state transition、runtime behavior、semantic contract に波及するかを事前に見積もれない。
- **レビューが主観化する**: 「責務が混ざっている」「危ない気がする」「抽象が悪い」といった
  コメントが、source refs、構造、invariant、obstruction、coverage gap に結びつかない。
- **リファクタが改善か移転か分からない**: cycle や依存方向は直ったが、semantic mismatch、
  runtime coupling、state/effect ordering、operation cost が別軸に移っただけかもしれない。
- **未観測をゼロ扱いしてしまう**: tests 未読、runtime trace 不在、production data 不在、
  private provider behavior、coarse projection が、いつの間にか「問題なし」と読まれてしまう。
- **定量化が浅い**: lint count や単一 score では、reachable cone、propagation depth、
  spectral radius、curvature、signature trajectory のような構造的状態を表せない。
- **結合度と凝集度が表面的にしか測れない**: 既存の coupling / cohesion 指標は、
  import、call、class、module の静的関係に寄りやすい。実際の設計上の結合や凝集は、
  semantic contract、shared state、effect ordering、authority、trust、runtime interaction にも
  現れるため、静的な依存本数だけでは見落としやすい。
- **古典的な設計原則が静的検査に落ちない**: information hiding、encapsulation、
  separation of concerns、substitutability、open-closed extension、dependency inversion、
  idempotency、representation independence などは重要だが、名前、import、型、依存方向だけでは
  十分に検知できない。多くは contract、semantic meaning、state transition、effect relation、
  authority / trust boundary の保存問題として現れる。
- **AI 生成コードのレビューが追いつかない**: AI が高速にコードを生成する一方で、人間の
  architecture review は同じ速度で増やせない。単体 test や CI は局所的なミスを防げるが、
  boundary erosion、semantic mismatch、state/effect ordering、hidden coupling、
  invariant preservation failure のようなアーキテクチャ問題には気づきにくい。
- **AI 生成コードで設計一貫性が崩れる**: AI が局所的には動く patch を大量に出すほど、
  architecture state、invariant preservation、complexity transfer を人間だけで追えなくなる。

ArchSig がユーザーへ返すアウトカムは次である。

- **Architecture state**: 巨大なコードベースを、Atom、molecule、workflow、boundary、
  invariant、signature axis の地図として説明する。
- **Design pressure**: どの finite Atom configuration が obstruction molecule / circuit を作り、
  どの law universe、signature axis、coverage assumption に相対化されるかを示す。
- **Change impact**: PR、feature extension、migration、refactor が、signature、curvature、
  spectrum、coverage boundary、operation path をどう変えるかを示す。
- **Semantic coupling / cohesion**: ArchMap の semantic、contract、state、effect、authority、
  trust 観測を使い、静的依存だけでは見えない結合度と凝集度を multi-axis に読む。
- **Design principle observability**: 重要な設計原則を slogan や lint rule ではなく、
  AAT の invariant、law、obstruction、operation preservation として観測可能にする。
- **Repair calculus**: 候補 repair operation が何を保存し、何を減らし、どの complexity を
  別 axis へ転送しうるかを比較する。
- **Review focus**: human reviewer と LLM が見るべき source refs、boundary、unmeasured evidence、
  exactness blocker、repair precondition を提示する。
- **Shared language**: 「この設計は悪い」ではなく、どの Atom configuration、invariant、
  law universe、obstruction circuit、operation delta、coverage gap の話かを共有する。
- **AI-ready packet**: 抽象的で複雑な AAT analysis を LLM が読める packet にし、チーム向け説明、
  review comment、repair plan、follow-up issue へ翻訳できるようにする。

ユーザーが得るべき直接的なメリットは次である。

- 大規模コードベースの architecture state を短時間で説明できる。
- 変更前に、どの設計境界と invariant を壊しそうかを把握できる。
- 静的な import / call graph ではなく、semantic coupling、effect coupling、state cohesion、
  contract cohesion、authority / trust coupling を含む設計上の結合度・凝集度を把握できる。
- information hiding、encapsulation、separation of concerns、substitutability などを、
  静的な命名・依存方向ではなく、source refs と semantic evidence に基づく設計原則の
  preserved / stressed / unmeasured reading として把握できる。
- PR review で、主観的な違和感を evidence-backed な構造診断へ変換できる。
- refactor が本当に改善か、別の axis への complexity transfer かを見分けやすくなる。
- static flat でも semantic / runtime / state transition obstruction が残るケースを見落としにくくなる。
- AI が生成した patch を、局所的な動作確認だけでなく architecture operation として評価できる。
- LLM に AAT packet を読ませることで、解析結果をチーム向けの説明、review comment、
  repair plan に翻訳しやすくなる。

ArchSig は、ユーザーに「合格 / 不合格」を返す道具ではない。ArchSig は、開発現場の
曖昧な設計不安を、architecture diagnosis、change impact analysis、repair planning、
review focus へ変換する道具である。

### R1. ArchSig を AAT のための解析機として定義する

ArchSig は AAT の実コード向け解析機である。ArchSig の出力は、AAT 本文の中心図式に対応する。

```text
AtomFamily
  -> AtomConfiguration
  -> ArchitectureObject
  -> InvariantFamily
  -> LawUniverse
  -> ObstructionCircuit
  -> ArchitectureSignature
```

ArchSig は、AAT の概念を `violation`、`rule`、`score` へ縮約しない。
ArchSig output は、少なくとも次の surface を持つ。

- observed Atom family surface
- Atom configuration / molecule surface
- architecture object projection surface
- invariant family surface
- selected law universe reference surface
- obstruction circuit / obstruction valuation surface
- architecture signature surface
- operation / repair / extension / synthesis candidate surface
- path / homotopy / diagram filling surface
- analytic representation surface
- coverage / exactness / reflection boundary surface
- LLM interpretation packet surface

### R2. ArchSig は ArchMap を入力とする

ArchSig の primary input は ArchMap である。

ArchMap は source-grounded Atom observation map であり、ArchSig は ArchMap の
`atomObservations`、`moleculeObservations`、`semanticObservations`、`projectionInfo`、
`concernHints`、`observationGaps`、provenance、non-conclusions を読む。

ArchSig は ArchMap を bypass して source repository を直接 architecture truth として
読まない。source repository、static scan、runtime trace、manual review は ArchMap authoring
または ArchMap enrichment の入力であり、ArchSig analysis の primary contract ではない。

ArchSig は、ArchMap の観測ゆらぎを hidden assumption として潰さない。粗い観測、同一視、
missing coordinate、private / unavailable / out-of-scope evidence は、analysis packet 内の
coverage / projection / exactness boundary として保持する。

### R3. AAT 本文の構成要素をすべて扱える surface を持つ

ArchSig は、AAT 本文が言っていることを 100% 扱えることを目標にする。
ここでいう「扱える」とは、AAT の全概念を ArchSig output の schema / packet / validation
boundary に表現できることである。

これは、次を意味しない。

- ArchSig がすべての AAT theorem を証明する。
- ArchSig が source から canonical Atom family を完全抽出する。
- ArchSig が全 law universe の soundness / completeness / exactness を保証する。
- ArchSig が zero curvature、lawfulness、semantic correctness を無条件に判定する。

ArchSig は、AAT の各概念について、少なくとも次を表現できなければならない。

- その概念が観測済みか、未観測か、private か、unavailable か、out-of-scope か。
- どの ArchMap observation / source ref / projection に支えられているか。
- どの selected law universe、witness family、signature axis、exactness assumption に相対化されるか。
- Lean theorem claim ではなく tooling analysis である境界。
- LLM が解釈するための短い structured reading と、human reviewer が追える evidence refs。

### R4. LawPolicy を主役にしない

ArchSig の中心は `LawPolicy` ではなく AAT analysis packet である。

LawPolicy は、selected law universe、witness family、signature axis、coverage assumption、
exactness assumption を選ぶための profile として扱う。LawPolicy は AAT 理論そのものではなく、
design rule collection でもない。

ArchSig は `law` を rule violation の名前として扱わない。law は architecture object に対する
可換性、保存性、不在性、整合性の述語であり、design rule や static lint rule は witness
provider または observation cue に落とす。

### R5. Non-conclusion を実務判断の境界として扱う

ArchSig の出力は、LLM の Atom 観測と bounded evidence に依存するため、確定した
architecture truth ではない。しかし、ArchSig output が単に `non-conclusion` の集合として
読まれるなら、実務では使えない。

ArchSig の距離感は、経済学に近い。経済は巨大で、経済学者であっても全体を直接観測する
ことはできない。統計、価格、制度、行動、局所的な出来事から間接的に構造を読む。
それでも、経済学の理論や診断は単なる `non-conclusion` ではない。観測境界、モデル仮定、
信頼区間、反証可能性、政策含意を明示したうえで、実務判断に使える bounded judgement を
返す。

ArchSig も同じである。巨大な software architecture は直接には見えない。
ArchMap の Atom 観測、source refs、runtime evidence、tests、LLM reading、manual review から
間接的に architecture state を読む。したがって ArchSig は、確定的な神の視点ではなく、
観測境界つきの architecture economics として、設計状態、設計圧、変更影響、repair option を
判断可能な形で返す。

ArchSig は、`non-conclusion` を「何も判断できない」という意味で扱わない。
`non-conclusion` は、出力を使うための境界条件、禁止される読み、追加確認が必要な点を
明示するための metadata である。

ArchSig output は、各 reading を少なくとも次に分類する。

- `actionable`: human review や repair planning に使える bounded judgement。
- `needsReview`: source refs、coverage、exactness、runtime evidence の追加確認が必要な reading。
- `blocked`: private、unavailable、out-of-scope、missing source などにより、現時点では
  実務判断へ使えない reading。
- `nonConclusion`: ArchSig が結論しない読み。global truth、theorem proof、semantic correctness、
  automatic repair safety、merge approval など。

`actionable` な reading は、確定事実である必要はない。ただし、次を持たなければならない。

- source refs または ArchMap observation refs。
- confidence / uncertainty。
- coverage boundary。
- exactness blocker または exactness assumption。
- user-facing interpretation。
- recommended next action。
- non-conclusions。

ArchSig は、実務で使える出力を次の形で返す。

```text
bounded judgement
  = observed evidence
  + AAT reading
  + confidence / uncertainty
  + boundary
  + non-conclusions
  + recommended next action
```

この形式により、ArchSig は「確定事実ではないが、レビューや設計判断に使える」出力を作る。
`non-conclusion` は免責文ではなく、誤用を防ぎながら actionable judgement を成立させるための
boundary contract である。

### R6. LLM interpretation を first-class output とする

ArchSig output は LLM に読ませて判断させることを前提にする。

LLM interpretation は ArchSig の代替判定ではなく、ArchSig の structured packet を読む
後段である。ArchSig は、複雑で抽象的な出力の認知負荷を下げ、Atom 観測のゆらぎを吸収するために、
LLM が解釈しやすい packet を出力する。

LLM-facing packet は少なくとも次を持つ。

- short diagnosis
- AAT concept map
- observed atoms / molecules summary
- obstruction molecules / circuits summary
- signature axes and boundary states
- spectral / analytic quantitative readings
- repair operation candidates
- complexity transfer notes
- coverage gaps and exactness blockers
- non-conclusions
- recommended human review focus

LLM interpretation は、global truth、merge approval、automatic repair safety、Lean theorem
discharge を結論しない。

### R7. Spectrum / analytic quantitative axes を扱う

ArchSig は、AAT の analytic representation のうち、graph、matrix、signature、curvature、
state algebra を扱える必要がある。

特に、スペクトル周辺の定量化軸を first-class に扱う。

候補 axis は次である。

- adjacency matrix / weighted adjacency matrix
- walk count / reachable cone size
- nilpotence boundary
- spectral radius
- selected subgraph spectrum
- propagation depth
- semantic coupling / cohesion
- state / effect coupling
- contract cohesion
- authority / trust coupling
- curvature valuation
- zero-reflecting aggregate boundary
- notComparable / unmeasured / unavailable / outOfScope status

スペクトル値は architecture quality score ではない。ArchSig は、スペクトル値を
selected graph / matrix representation に相対化し、値域、重み、coverage、zero-reflecting
条件を明示する。

結合度と凝集度も単一 score ではない。ArchSig は、static dependency coupling だけでなく、
semantic coupling、contract cohesion、state cohesion、effect coupling、authority / trust
coupling を別軸として扱う。これらの軸は ArchMap の意味論的観測に依存するため、
confidence、coverage boundary、non-conclusions を持つ。

ArchSig は、analytic value だけから architecture object 全体を復元できるとは主張しない。
スペクトル軸は、AAT analysis packet の multi-axis diagnosis の一部であり、obstruction、
operation、repair、coverage boundary と一緒に読む。

### R8. Operation / repair / signature delta を重視する

ArchSig は単発状態の report だけでなく、operation による変化を扱う。

PR、feature extension、refactor、migration、isolation、protection、split、merge は
ArchitectureOperation として読める必要がある。

operation analysis は少なくとも次を保持する。

- support
- precondition
- atom transformation
- transition relation
- invariant preservation claim
- obstruction transport
- signature delta
- decreased axis
- transferred obstruction / complexity
- excluded readings

ArchSig は、ある obstruction が減ったことを総合的改善として扱わない。
repair candidate は、減らす selected obstruction measure、保存する invariant family、
増加を主張しない axis、転送されうる obstruction を明示する。

### R9. 静的検査しにくい設計原則を AAT reading として扱う

ArchSig は、CS / software engineering で重要とされてきたが静的ツールでは簡単に検知できない
設計原則を、AAT の invariant、law、obstruction、operation preservation として扱う。

ArchSig は、設計原則を slogan として report しない。各 principle reading は、ArchMap の
Atom observation、molecule、semantic observation、source refs、coverage boundary、
non-conclusions に接続されなければならない。

ArchSig が first-class に扱うべき principle reading は次である。

- `InformationHiding`: representation、state、effect、provider detail が declared boundary を
  越えて漏れていないか。
- `Encapsulation`: state mutation、effect execution、authority check が owner boundary を
  迂回していないか。
- `SeparationOfConcerns`: semantic concern、state transition、effect、policy、presentation が
  同じ molecule に過剰に混線していないか。
- `Substitutability`: replacement が contract、effect、state transition、semantic reading を
  保存するか。
- `OpenClosedExtension`: feature extension が core invariant を保存し、interaction obstruction や
  lifting failure を生んでいないか。
- `DependencyInversion`: dependency direction だけでなく、abstract boundary の semantic contract が
  実装側と整合しているか。
- `RepresentationIndependence`: 内部 representation の変更が selected observation と contract を
  保存するか。
- `IdempotencyAndReplaySafety`: retry、event replay、job execution、external effect が selected
  state transition law を満たすか。
- `AuthorityAndTrustBoundary`: authority label、trust handoff、external provider output が
  operation path の中で失われていないか。

各 principle reading は少なくとも次を返す。

- `preserved`: selected evidence の範囲で保存されている。
- `stressed`: obstruction、coupling、coverage gap、complexity transfer があり、review が必要。
- `unmeasured`: 必要な evidence がないため測れていない。
- `notApplicable`: selected source universe では対象外。

この分類は theorem proof ではない。ArchSig は、各 reading の source refs、confidence、
coverage boundary、exactness blockers、recommended next action を一緒に出力する。

## スコープ

この PRD のスコープは次である。

- ArchSig を AAT analysis engine として定義する要求。
- ArchMap を ArchSig の primary input とする責務境界。
- 一般のソフトウェアエンジニアが抱える開発現場のペインと、ArchSig が返すアウトカム。
- AAT 本文の全概念を扱える output surface の要求。
- LawPolicy を selected profile として下げ、AAT analysis packet を主役にする方針。
- non-conclusion を免責ではなく、bounded judgement を成立させる boundary contract として
  扱う要求。
- LLM interpretation packet を first-class output にする要求。
- spectrum / analytic quantitative axes を ArchSig の multi-axis diagnosis に入れる要求。
- operation / repair / signature delta / complexity transfer を扱う要求。
- 静的検査しにくい設計原則を AAT reading として扱う要求。

後続設計で具体化するものは次である。

- 新しい ArchSig analysis packet schema。
- LLM interpretation packet schema。
- spectrum / graph / matrix axis schema。
- operation delta / repair delta schema。
- existing LawPolicy schema の分割または改名方針。
- CLI workflow と validation rule。
- fixture / golden corpus / migration plan。

## Non-Goals

この PRD は次を目標にしない。

- ArchSig を static lint / rule violation checker として定義する。
- 単一の architecture quality score を定義する。
- LLM output を architecture truth として扱う。
- ArchSig が source extraction completeness を証明する。
- ArchSig が AAT theorem、Lean theorem、lawfulness、zero curvature を無条件に証明する。
- `non-conclusion` を理由に、すべての analysis reading を実務判断不能として扱う。
- ArchSig が all runtime behavior、production data、private provider behavior を復元する。
- spectrum / aggregate value だけで architecture object 全体を代替する。
- repair candidate を automatic safe patch として扱う。
- FieldSig の forecast、governance、calibration、operational feedback schema をこの PRD で再設計する。
- Lean の theorem package や proof API をこの PRD で確定する。

## Acceptance Criteria / 完了条件

- 一般のソフトウェアエンジニアが抱えるペインが、大規模コードベース理解、変更影響、
  主観的レビュー、リファクタの complexity transfer、未観測 evidence、浅い定量化、
  AI 生成コードのレビュー遅れと設計一貫性として定義されている。
- ArchSig が返すアウトカムが、architecture state、design pressure、change impact、
  semantic coupling / cohesion、design principle observability、repair calculus、review focus、
  shared language、AI-ready packet として定義されている。
- ArchSig が合格 / 不合格判定器ではなく、曖昧な設計不安を architecture diagnosis、
  change impact analysis、repair planning、review focus へ変換する道具であることが
  明記されている。
- ArchSig が AAT のための解析機であることが明記されている。
- ArchSig の primary input が ArchMap であることが明記されている。
- AAT 本文の Atom、Configuration、ArchitectureObject、Invariant、LawUniverse、
  ObstructionCircuit、ArchitectureSignature、Operation、Path、Homotopy、Diagram、
  AnalyticRepresentation を扱う output surface が定義されている。
- 「AAT が言っていることを 100% 扱える」が、証明完全性や抽出完全性ではなく、
  schema / packet / validation boundary に表現できることとして定義されている。
- LawPolicy が主役ではなく、selected law / witness / axis / coverage / exactness profile として
  扱われることが明記されている。
- non-conclusion が免責文や「何も判断できない」という意味ではなく、bounded judgement の
  境界条件、禁止される読み、追加確認点を示す boundary contract として定義されている。
- ArchSig output が `actionable`、`needsReview`、`blocked`、`nonConclusion` を区別し、
  actionable reading には evidence、confidence / uncertainty、coverage boundary、
  exactness boundary、recommended next action が要求されている。
- ArchSig output を LLM に読ませて判断させるための LLM interpretation packet が
  first-class output として要求されている。
- Atom 観測のゆらぎ、coarse projection、missing coordinate、private / unavailable /
  out-of-scope evidence を boundary として保持することが明記されている。
- spectrum / graph / matrix / curvature / state algebra の quantitative axes が
  multi-axis diagnosis として要求されている。
- spectral radius、nilpotence、walk count、reachable cone、zero-reflecting boundary が
  score ではなく selected analytic representation として扱われている。
- semantic coupling、contract cohesion、state cohesion、effect coupling、authority / trust
  coupling が、静的依存本数とは別の ArchSig 独自の multi-axis 計測として定義されている。
- operation / repair / signature delta / complexity transfer が ArchSig の実用価値として
  要求されている。
- information hiding、encapsulation、separation of concerns、substitutability、
  open-closed extension、dependency inversion、representation independence、
  idempotency / replay safety、authority / trust boundary が、静的 lint ではなく
  AAT reading として扱われることが要求されている。
- Non-Goals が、static lint 化、single score 化、LLM truth、extractor completeness、
  theorem discharge、automatic repair safety を明確に除外している。
- 後続の schema / CLI / fixture / docs migration issue を切れる粒度になっている。
