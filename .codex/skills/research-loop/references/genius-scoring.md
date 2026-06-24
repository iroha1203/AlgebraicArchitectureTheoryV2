# Genius Scoring

`genius` は通常の `80-100` 点候補の延長ではなく、大定理レベルの希少枠である。G1 で genius 候補を出すとき、G2 で `genius_eligibility` を判定するとき、G4 で `genius_verdict` を監査するときだけ読む。

## 1000 点の条件

`1000` 基本点は、次をすべて満たす場合だけ採用する。

- AAT の core tension または到達像を実質的に変える。
- 数学的構造と CS / SWE / tooling / architecture 理論の少なくとも二領域を、比喩ではなく同じ定理、構成、不変量、反例、または予想強化の中で橋渡しする。
- 既存 rival が提供できない能力を明確に作る、または rival の強みを AAT 内部のより強い構造へ統合する。
- claim boundary を守りながら、通常の incremental closure では到達しない射程、圧縮、反例性、または新しい研究プログラムを開く。
- 証拠計画があり、名前だけの大きな予想、願望、未検証のスローガンではない。

一つでも満たさない場合は通常の `0-100` 基本点に戻す。`genius` は「とても良い 90 点」ではない。

## Target / Support / Unlock

`genius-target` は後続サイクルで攻略する大定理、大予想、または theorem program を立てる候補である。target を置くだけで `1000` 点を加算してはならない。

- `genius-target`: target、claim boundary、support map、unlock condition を tracking Issue に seed する。証拠が足りなければ `seed-only` とし、SCORE は `0`。
- `genius-support`: 既存 genius target を証明、反証、鋭化する補題、有限 witness、obstruction、bridge。通常の `0-100` 基本点で採点する。
- `genius-unlock`: target theorem そのものが Lean proof、十分強い theorem package、または GOAL が明示的に許した conjectural evidence として G2 / G3 / G4 を通った時だけ `1000` 基本点を確定する。

G4 は unlock 時に、support cycles で既に得た SCORE と今回 unlock する `1000` 点が何を別々に評価しているかを説明し、二重計上を避ける。

## Gate

`genius` 基本点を採るには、四つの G2 審判がすべて `genius_eligibility: yes` を返し、G4 が `genius_verdict: confirm` を返す必要がある。一人でも `no` または `cannot-determine` なら通常 SCORE に戻す。
