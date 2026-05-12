# Software Architecture as a Field: ソフトウェア進化を計算可能にする

## 変わり続けるソフトウェアは、なぜ重くなるのか

- 現場の痛みから始める。
  - 同じ feature なのに、触る場所が増える。
  - 正しい実装 path はあるのに、近くにある shortcut の方が見つけやすい。
  - review で違和感は出たが、次の PR には残っていない。
  - AI agent は、きれいな設計だけでなく、過去の妥協も学ぶ。
- これは単なる review failure ではない。
- software evolution の問題である。
- Lehman は、長寿命ソフトウェアが環境に適応し続け、変化し続ける限り複雑性を増す傾向があると問うた。
- この問いは AI-assisted development の時代にも終わっていない。
- むしろ PR、CI、review、incident、AI proposal によって変更速度と feedback が増え、問いは鋭くなっている。
- この記事の主題は「良い review をしよう」ではない。
- 主題は、software evolution を計算可能な対象として扱えるか、である。
- 読者への約束:
  - architecture degradation を「悪いコードが増えた」ではなく、「進化の可能性空間が歪んだ」として見る視点を渡す。
  - Lehman の問いを、AAT / ArchSig / SFT によって現代的に扱う道筋を示す。

## 計算可能にするとは、未来を予言することではない

- ソフトウェア進化は、PR や diff の列だけではない。
- artifact、agent、governance、feedback が future architecture を形づくる過程である。
- 「計算可能」とは、未来を完全に予測することではない。
- 明示された boundary の下で、進化の一部を bounded な計算問題として切り出すこと。
- 必要な boundary:
  - 対象 artifact
  - architecture universe
  - observation axis
  - operation support
  - operation policy
  - horizon
  - non-conclusions
- 詳細な claim boundary は Appendix に置く。

## 変更とは、何を保存する操作なのか - AAT

- 問い: ある変更が起きたとき、ソフトウェアの何が保存され、何が破れたと言えるのか。
- AAT は、個々の変更を局所的に読むための理論。
- diff ではなく `ArchitectureOperation` として変更を見る。
- operation の前後で保存されるべき性質を `InvariantFamily` として扱う。
- invariant が破れた証拠を `ObstructionWitness` として扱う。
- `ArchitectureSignature` は破れやリスクを多軸で読む診断表。
- `TheoremBoundary` は、何を結論してよく、何を結論してはいけないかを明示する。
- Architecture zero curvature theorem を入れる。
  - 選んだ law universe、obstruction witness、signature axis、observation boundary の中で、lawful であることと required obstruction witness が消えていることを対応させる。
  - 「システム全体が完全」という主張ではない。
  - 測った範囲と明示した前提の中で、architecture lawfulness を signature / witness と結びつける定理として説明する。
  - AAT が単なる語彙ではなく、定理を持つ局所理論であることを示す。
- AAT は SFT に対して「局所法則」を渡す。
- ここでは exhaustive taxonomy は出さない。

## 「設計が悪い」は、どんな証拠として残せるのか - ArchSig

- 問い: その保存や破れを、実際の repository、PR、review、CI からどのように観測できるのか。
- ArchSig は review 改善ツールではなく、measurement layer。
- AAT 的な観測量を実 artifact から取り出す。
- 入力:
  - codebase
  - PR diff
  - dependency graph
  - CI result
  - review comment
  - incident / runtime evidence
- 出力:
  - measured signature axes
  - obstruction witness candidates
  - measured / unmeasured status
  - theorem boundary
  - non-conclusions
- ArchSig は SFT に渡す observation record を作る。
- 「検出されなかった」と「存在しない」を分ける。

## 進化は、どこまで計算可能なのか - SFT

- 問い: 観測された変化は、次に到達しやすい architecture future をどう変えるのか。
- SFT は Lehman の問いを、現代の artifact-rich な開発環境で扱い直す。
- SFT は software evolution を field-shaped computation として見る。
- `SoftwareFieldEstimate`:
  - development field のうち計算可能な断面
  - 完全な組織モデルではない
  - boundary と unknown remainder を持つ
- `OperationSupport`:
  - その field で可能 / 許容される operation の集合
- `OperationPolicy`:
  - どの operation が自然、低コスト、高コスト、禁止、review 必須に見えるか
- `ForecastCone`:
  - selected support / policy / horizon の下で到達可能な field path の集合
  - 未来予測ではなく reachable future の範囲
- `ConsequenceEnvelope`:
  - ForecastCone を reviewer / tech lead が読める report に畳む
  - affected region、signature axis、missing invariant、recommended intervention
- `FieldUpdate`:
  - forecast と実際の PR / review / CI / incident outcome の差分を field memory に戻す
- SFT は review ではなく、software evolution 全体を計算対象にする。

## 良い変更が選ばれやすい場を作る - Attractor Engineering

- Attractor Engineering は記事全体の主題ではなく、SFT の応用。
- 主題は software evolution を計算可能にすること。
- Attractor Engineering は、計算可能な field に介入して future operation distribution を設計する実務。
- 良い変更が見つけやすい。
- 良い変更が真似しやすい。
- 良い変更が検証しやすい。
- unsafe shortcut が高コストになる。
- unsafe shortcut が観測可能になる。
- review / CI / AI policy / examples / ownership を `GovernanceIntervention` として扱う。

## まとめ: Lehman の問いを計算可能な形へ

- Lehman の問いは、現代にも生きている。
- SFT は、その問いへの回答として software evolution を計算可能な対象に切り出す。
- AAT は局所法則を与える。
- ArchSig は観測可能にする。
- SFT は field-shaped computation として reachable architecture futures を扱う。
- Attractor Engineering は、その field へ介入する実務である。
- 技術的負債を、この枠組みだけで定義し直すとは言わない。
- ただし、technical debt の一部は、future operation distribution が悪い方向へ偏った field state として観測できるかもしれない。
- その claim は theorem ではなく、SFT / ArchSig / empirical validation の対象として扱う。

## Appendix: Claim Boundary

- 計算可能性を主張するには、claim の種類を混ぜない。
- structural theorem、tool observation、empirical hypothesis、future obligation を区別する。
- Lean はこの boundary を守るための補助線として位置づける。
- 例:
  - selected graph has no cycle: structural theorem
  - ArchSig detected no boundary violation on selected axis: tool observation
  - this reduces review cost: empirical hypothesis
  - runtime behavior is safe: not concluded
