# GOAL Card Contract

G0 で GOAL card を検査するときだけ読む。GOAL は通常、「証明したい定理一覧」ではなく、研究で成し遂げたい能力や到達像である。ただし `research mode: target-theorem` を持つ GOAL は、その能力を代表する一つの大定理を GOAL カードで定義し、証明完了をループの完了条件にしてよい。

## 必須項目

active な GOAL は、候補を落とすための報酬関数を持つ。次が不足する場合は `goal defect` として止める。

- `id` と `status: active`。
- 任意の `research mode`: 省略時は `score-phase`。指定する場合は `score-phase` または `target-theorem`。
- `research aim`: 研究で成し遂げたい能力や到達像。
- `core tension`: 何が分かれば非自明で、何が解ければ理論の景色が変わるか。
- `rival`: 比較対象にする既存概念、手法、tooling、理論枠組み。候補は、その rival が得意なことを把握したうえで、どの能力で勝つ、統合する、分離する、または測定可能にするのかを述べる。
- `claim boundary`: どの語彙、law universe、coverage topology、係数、profile の上で語るか。
- `capability categories`: SCORE を配分する能力カテゴリ。例: quantity、invariance、computability、interpretation、obstruction、unification。
- `threshold policy`: active SCORE threshold を tracking Issue でどう設定・読むかの方針。固定値ではなく、フェーズごとの運用パラメータとして扱う。
- `portfolio constraint`: ひとつの方向だけで点を稼いでフェーズを区切らないための条件。例: 3 カテゴリ以上で正の SCORE、最低 1 件は Lean proved。
- `phase boundary criteria`: 研究としてキリが良いと判定する条件。例: coherent な report section / paper seed になる、主要な insight が揃った、次は探索より整理が有利である。
- `reward rubric`: SCORE の採点規則。
- `dullness filter`: 定義展開、既存定理の即時系、名前替え、小補題量産を弾く基準。
- `frontier`: 探索してよい周辺領域。反例、obstruction、予想の強化、新しい不変量、別領域との橋を含めてよい。

## 大定理証明モードの必須項目

`research mode: target-theorem` の GOAL は、通常の必須項目に加えて次を持つ。足りない場合は `goal defect` として止める。

- `target theorem`: 証明したい大定理の名前と自然言語 statement。定理一覧ではなく、GOAL の能力を代表する一つの主ターゲットとして書く。
- `target theorem boundary`: どの語彙、有限性、law universe、coverage topology、係数、site / cover、Lean 置き場所、証拠段階の上で主張するか。
- `target proof artifacts`: 完了時に存在すべき Lean theorem / theorem package / report section / candidate card。
- `target proof strategy`: support lemma、normalization、counterexample exclusion、bridge、既存成果の利用 map。
- `target theorem completion criteria`: 何をもって証明完了と判定するか。原則は sorry なし Lean proof、対象 declaration の axiom audit、material premise / hypothesis の discharge audit、G3.5 同期、G4 監査、G5 レビュー、G6 target completion 判定である。
- `target premise discharge policy`: target theorem が faithfulness、exactness、nondegeneracy、coverage、transport、representation adequacy などの実質的前提を含む場合、その前提を target boundary として残すのか、Lean theorem / finite witness / concrete certificate で discharge して completion 条件に含めるのかを書く。
- `target material premise ledger`: target theorem の結論を支える実質的前提を列挙する。各 premise について、名前、何を支えるか、許される role (`direction-hypothesis` / `ambient-boundary` / `discharge-required`)、completion までに必要な discharge artifact、結論相当 premise ではない理由を書く。faithfulness、exactness、nondegeneracy、coverage、transport、representation adequacy、sheaf condition、stack effectiveness、finite-shadow adequacy などは原則 `discharge-required` とする。
- `target anti-weakening rule`: target proof が結論相当の仮定を theorem argument、typeclass、structure field、certificate field、opaque class membership に移して成功扱いすることを禁じる規則を書く。`ambient-boundary` に残せるのは対象 site、finite vocabulary、cover、coefficient object、supplied observation contract などの入力幾何だけであり、target conclusion、faithfulness、effectivity、triviality、global coherence、obstruction vanishing と同値または片方向に近い条件を隠してはならない。
- `target failure policy`: 反例、仮説不足、証明停滞が出たときに、`target-refuted` / `target-blocked` / GOAL 改訂提案のどれとして扱うか。

## 任意項目

`spine` を置いてもよいが、それは固定計画ではなく現在の仮説として扱う。探索結果が spine を壊す、鋭くする、置き換えるなら、それ自体を高く評価する。

## 欠陥判定

次のいずれかに当たる場合は G1 へ進まない。

- GOAL が active ではない。
- reward rubric または dullness filter がなく、候補を落とせない。
- rival が空、または rival に対する有効差分を候補へ要求できない。
- claim boundary が曖昧で、成果がどの語彙や profile の上の主張か判定できない。
- `score-phase` で、threshold policy はあるが、tracking Issue に active threshold がなく、起動引数にも threshold がない。この場合は `goal defect` ではなく `threshold missing` とする。
- `target-theorem` で、target theorem / boundary / proof artifacts / proof strategy / completion criteria が不足している。
- `target-theorem` で、completion criteria が SCORE threshold 到達だけになっており、target theorem の証明完了を判定できない。
- `target-theorem` で、target theorem の結論に必要な実質的前提があるのに、それを target boundary として残すのか、completion までに discharge するのかを completion criteria または premise discharge policy が判定できない。
- `target-theorem` で、target material premise ledger または target anti-weakening rule がなく、結論を支える仮定、class field、certificate field、structure membership を completion 時に監査できない。
- `target-theorem` で、material premise ledger が faithfulness、exactness、coverage、sheaf condition、effectivity、triviality、representation adequacy などの実質的前提を `ambient-boundary` として残しているのに、それが結論相当 premise ではない理由と独立した input-boundary 理由を示していない。
- `target-theorem` で、completion criteria が「target theorem package が条件付きで証明された」ことを許し、未 discharge の `discharge-required` premise を残した theorem argument / typeclass / structure field / certificate field を `target-theorem-proved` にできる。
- `target-theorem` で、target theorem が GOAL の research aim や rival delta と切り離され、ただの定理一覧項目になっている。
- portfolio constraint または phase boundary criteria がなく、SCORE 到達後にフェーズ区切りを判定できない。
- frontier が狭すぎて定義展開しか許さない、または広すぎて GOAL への寄与を判定できない。

欠陥を見つけたら、GOAL 本文は編集せず、tracking Issue コメントまたは別 Issue に改訂案を残す。
