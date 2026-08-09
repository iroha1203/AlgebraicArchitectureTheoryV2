# G-104 条件C 必要性地図ハント PRD

- 状態: merge 後 Active(進行状態の正本は Issue #3948)
- 位置づけ: Atlas 定理(G-104 Diagnostic Resolution Invariance Theorem)の条件 C を
  必要十分化する二段計画の第一段(off-loop 計算探索)。第二段(必要十分定理の
  target-theorem GOAL 化と Lean 証明)は本 PRD の裁定後に別途起草し、依存は
  GitHub Issue の dependency で管理する。
- 実装者: Codex(prd-loop)。探索は #3912 と同じく vibe coding による off-loop
  ハントであり、research loop の cycle ではない。

## 問い

> **C0–C6 の各条項は、係数側を law family 全体で量化した一様不変性に対して必要か。
> 必要でない条項をどう弱めれば、一様不変性の必要十分条件 C\* が
> incidence / support レベルの条項として得られるか。**

この問いが本 PRD の採否判定規律である。成果物は次の形でこの問いに答えていなければ
受理しない。

1. C0–C6 の**7条項すべて**に、verdict ごとの evidence schema(R1-3 で定義)に
   従う証拠付きの verdict(`not-necessary` / `necessary-evidence` / `undecided`)が
   付いている(C / R0-fail 終端の場合は checkpoint 受理条件で代替する)。
2. 終端 A(確定)・B(構造的否定)・C(停滞)・R0-fail(還元反証)のいずれかへの
   到達が明示されている。

条項の意図的な後続送り、evidence schema を欠いた verdict、事前登録なしの探索
bound は、問いに答えたと数えない(**スコープの縮小禁止**)。blocker と coverage
limit の記録を伴う C / R0-fail 終端の報告は縮小と数えない。

## 現状診断

- G-104 は `target-theorem-proved` で完了済み。証明されたのは
  **C(C0–C6、C1–C4 は座標 subnerve 相対化)⟹ H¹ comparison map 全単射**の
  片向きである(claim (ii))。
- 必要性方向に現在あるのは条項独立反例(C から一条項を外すと同型が破れる例)だけで、
  これは「どの条項も冗長でない」ことの証拠であり「全単射 ⟹ C」ではない。
  G-104 カードの frontier「条件 C の必要性方向の特徴づけ」が本 PRD の対象である。
- **pointwise の必要性(個々の instance で 全単射 ⟹ C)は成立しない**。両側の
  H¹ が零なら C の破れと無関係に全単射が自明に成立するため、反例が安く作れる。
  したがって必要十分化の対象は、係数側を量化した次の一様不変性に取る。

### 一様不変性(本 PRD の量化対象)

固定した comparison data(L-adequate pair `q ≤ q'`、factor 写像 `π`、nerve 対
`N` / `N'`、nerve 射 `φ`、chart 台。well-formedness は G-104 カードの規律に従う)に
対し、

> **任意の** FiniteLawFamily(pair が adequate であるもの)の K0 / K1 生成係数に
> ついて、H¹ comparison map が全単射である

とき、この comparison data は**一様不変**であると言う。

### 値部分集合還元(作業仮説。R0 で検証する)

K0 / K1 の下では law 側の量化は有限に落ちる見込みである。根拠:

- descend の π-可換(`lawDescend_comparisonFactor`)により、細側 descend 値 =
  粗側 descend 値 ∘ `π`。
- 座標 `(law, 値 v)` の block は、部分集合 `A := (粗側 descend)⁻¹(v) ⊆ Target_q` が
  誘導する **A-subnerve**(粗側: K1 導出台が `A` と交わる cell、細側: 導出台が
  `π⁻¹(A)` と交わる cell)上の定数 `ℚ` 係数比較に一致する(G-104 の block 直和
  分解 theorem の言い換え)。
- 逆に任意の非空 `A ⊆ Target_q` は indicator law(`Target_q` 上の特性関数の `q` に
  よる引き戻し)の値 fiber として実現され、その law は `q` を factor するので
  `q = π ∘ q'` より `q'` も factor する(adequacy を保つ)。

したがって

> **一様不変性 ⟺ すべての非空 `A ⊆ Target_q` について A-subnerve の
> 定数 `ℚ` 係数 H¹ 比較が全単射**

が見込まれる。この還元(実現可能性と block 分解の一致)の検証を R0 の義務とし、
成立すれば量化は `Target_q` の部分集合全体という有限対象になる。これは G-104
frontier の「自由係数反例の law 実現可能性の判定」の消化を兼ねる。

### 予想される帰結

現行の C0–C6 がそのまま必要十分の右辺になる見込みは低い。例えば C0(台合併)は、
破れても当該 A-subnerve が H¹ 的に無内容なら一様不変性が保たれうる。本ハントの
実体は「必要性の証明」ではなく、**必要でない条項の検出と、その弱化による C\* の
研磨**である。

## 参照(source of truth。編集禁止)

- 正本: `research/goals/G-104-aat-resolution-invariance.md`(条件 C・K0 / K1・
  anti-weakening rule の正確な文言)
- 設計根拠: `docs/note/aat_g104_coefficient_generation_contract.md`
- 先行 engine: `research/experiments/g104-condition-hunt/`(Issue #3912 の固定
  artifact。**変更禁止**。fork 元として copy する)
- Lean 固定済み素材(calibration に使う。編集禁止):
  - `research/lean/ResearchLean/AG/ResolutionInvariance/FaceLiftObstruction.lean`(C4)
  - `research/lean/ResearchLean/AG/ResolutionInvariance/EdgeFiberObstruction.lean`(C5)
  - `research/lean/ResearchLean/AG/ResolutionInvariance/LoopLiftObstruction.lean`(C6)
  - `research/lean/ResearchLean/AG/ResolutionInvariance/ComparisonData.lean`
    (`lawDescend_comparisonFactor`)
  - `research/lean/ResearchLean/AG/ResolutionInvariance/LawGeneratedComplex.lean`
    (K0 / K1 生成複体)
  - 同 dir 配下の現行確定実体(calibration (e) と R0 手順3 の対応表で参照):
    `ResolutionInvarianceConditions.lean`、`LawValueCoordinateSubnerve.lean`、
    `GeneratedComparisonMap.lean`、`LawValueBlockCohomology.lean`
    (`lawGeneratedH1BlockEquiv` = H¹ の block 直和分解)、
    `LawValueBlockDecomposition.lean`(cochain レベルの下位根拠)、
    `LawValueBlockComparison*.lean`(`Naturality` 含む)、
    `ResolutionInvarianceFiringWitness.lean`

## target statement(task 固有。一次仕様 = 本節)

**C\* 予想(必要十分化)**: well-formed な comparison data について、

> comparison data が一様不変 ⟺ C\* が成立

となる incidence / support レベルの条項系 C\*(C0–C6 の研磨版)が存在する。

本 PRD の納品物はこの予想の**計算的裁定**(C\* 候補+両方向の bounded 無反例+
手証明スケッチ、または構造的否定)であり、証明ではない。第二段の GOAL カードが
この statement を target theorem として固定し直す。

## 実装計画

### R0: engine fork と calibration gate

1. `research/experiments/g104-necessity-map/` を新設し、`condition_hunt.py` を
   copy して拡張する(既存 dir は完了 GOAL の固定 artifact なので import 依存も
   しない)。exact 線形代数(`fractions.Fraction`)・supported nerve・条項判定は
   再利用する。
2. calibration(全 pass するまで探索に入らない):
   - (a) G-104 既知反例3種(C4 / C5 / C6 の Lean witness)の再構成と判定一致。
   - (b) 値分配 derived support hole 例(考察ノート §5 に固定した全データ)の
     再構成と、相対化 C による除外の再現。
   - (c) **block 還元の検証**: law 生成係数の comparison map が、非空 `A` ごとの
     A-subnerve 定数係数比較の直和と一致することを、非定数 law descent を持つ
     小 fixture 上で数値検証する。
   - (d) **indicator 実現可能性の検査**: 任意の非空 `A ⊆ Target_q` に対し
     indicator law が adequate な law family を成し、その座標 subnerve が
     A-subnerve に一致することをテストで固定する。
   - (e) **現行 canonical 実体の oracle 化**: 歴史的 fixture 3種だけで calibration を
     通過してはならない。現行 G-104 の確定実体
     (`ResolutionInvarianceConditions.lean` = 現行条件C、
     `LawValueCoordinateSubnerve.lean` = 座標 subnerve、
     `GeneratedComparisonMap.lean` = 生成 comparison map、
     `LawValueBlockComparisonNaturality.lean` = block 自然性、
     `ResolutionInvarianceFiringWitness.lean` = 現行発火 witness)の固定データと
     判定を engine 上で再構成し、Lean の結論と一致させる。
3. **還元の一般手証明**(探索非依存): 値部分集合還元
   (一様不変性 ⟺ 全非空 `A` の A-subnerve 定数係数比較全単射)を、fixture の
   数値一致とは別に、一般の数学的手証明として report 付録に固定する。conjunct を
   分解し、既存 Lean declaration に対応がある conjunct は対応表で引用する
   (**H¹ の block 直和分解 = `LawValueBlockCohomology.lean` の
   `lawGeneratedH1BlockEquiv`**(cochain レベルの下位根拠として
   `LawValueBlockDecomposition.lean` を区別して併記する)、block の subnerve
   定数係数比較への還元・自然性 = `LawValueBlockComparison*.lean` /
   `LawValueBlockComparisonNaturality.lean`、descend の π-可換 =
   `ComparisonData.lean` の `lawDescend_comparisonFactor`)。対応がない conjunct
   (indicator law の adequacy と値 fiber による任意非空 `A` の実現、全単射の
   block ごと判定への分解)は手証明を必須とする。
4. R0 の失敗は次の2種を峻別する(混同は Failure Contract 違反):
   - **calibration failure((a)–(e) の不一致)**: engine 実装または modeling の
     欠陥として扱い、engine を修正して再 calibration する。oracle 不一致から
     還元の偽は従わない。修正で解消できない場合は blocker として停止条件 C を
     踏む(**pre-R1 停止**。監査単位と成果物は停止条件 C の pre-R1 規定に
     従う)。一般手証明(手順3)を完成も反証もできない場合も同じ経路を取る。
     不一致のまま探索へ進むことは許さない。
   - **R0-fail(還元反証)**: 一般手証明(手順3)が破れた場合、または還元への
     数学的反例が **engine の外で独立再現**(手計算または独立実装)された場合に
     限る。探索に入らず、R0-fail 終端(停止条件節)として反例データと機構分析を
     固定して停止する(還元が誤りなら量化の定義から立て直す必要があり、
     本 PRD の前提が崩れるため)。

### R1: 必要性地図

1. comparison data(粗側 / 細側 nerve、`φ`、`π`、chart 台)を bounded normal form で
   全数列挙する。bound と normal form(粗側 / 細側 Target のサイズ、chart / edge /
   face 数、chart 台パターン、`π` / `φ` の列挙範囲、退化 cell の許容、同型類除去・
   枝刈りが列挙の被覆を欠かさないことの根拠)は、**探索実行前に** Issue #3948 へ
   コメントで事前登録してから run する。結果を見た後の bound 変更は新ラウンド
   として再登録し、全ラウンドを report に記録する(`necessary-evidence` の母集団を
   engine 実装依存にしないため)。最低限、既知反例3種・値分配例・G-103 由来
   proper pair の規模(coarse chart 3 / fine chart 4 級)を包含すること。
2. 各データについて、全非空 `A ⊆ Target_q` の A-subnerve 定数係数比較を判定し、
   一様不変性を決定する。同時に相対化 C の条項 vector を全 `A` について評価する。
3. 各条項 `Ci`(C0–C6)の verdict を、**verdict ごとの evidence schema** に従って
   確定する(schema の混用・省略は不可):
   - `not-necessary`: evidence = **再現可能な必要性反例**(一様不変 ∧ Ci 破れの
     comparison data)。非退化な反例(ある `A` で両側 H¹ 非零、かつ Ci の破れが
     非空虚に発火)を優先探索し、bound 内に退化例しか無い場合はその旨を明記する。
   - `necessary-evidence`: evidence = **事前登録済み探索母集団の明示+反例
     ゼロ件の zero-result+Ci の破れから非全単射 block を生む機構スケッチ**
     (bound 内無反例は証明ではない)。
   - `undecided`: evidence = **blocker の特定+試行履歴+coverage limit** の記録。
4. 7条項の verdict 表を report に置く。

### R2: C\* 研磨ループ

1. `not-necessary` 判定の条項ごとに破れ機構を一段分析し、incidence / support
   レベルの弱化 `Ci*` を提案する(例: 条項の適用対象を「H¹ に寄与しうる subnerve
   構成」へ絞る形の incidence 条件)。
2. C\* 候補全体に対し**二方向の反例探索**を行う:
   - 十分性破れ: C\* 成立 ∧ ある `A`-block が非全単射。
   - 必要性破れ: 一様不変 ∧ C\* 破れ。
3. 反例が出たら条項を改訂して再探索する。「候補 → 反例 → 機構分析 → 改訂」を
   成果が出るまで反復する。
4. **候補の資格制限**(G-104 anti-weakening rule の継承): C\* は incidence /
   support レベルの条項に限る。comparison map・粗側複体・両側 global H¹ の同型・
   消滅・rank 一致と同値または片方向に近い条項、およびその `A`-量化
   (「全 `A` で全単射」を条項と称する恒真化)は不受理。明示の例外は C3 型の
   局所 fiber acyclicity のみ(G-104 カードの理由の範囲を超えて拡張しない)。

### R3: まとめ

1. 手証明スケッチ: C\* ⟺ 一様不変性の両方向を、block ごとの相対複体経由
   (既存 hunt-report §4 スケッチの拡張)で素描する。
2. 条項独立性: C\* の各条項について、外すと反例が現れることを列挙データで示す。
3. 非退化正例: C\* を満たし G-104 (v) 相当の発火条件(π 非単射・両側 H¹ 非零・
   2元以上の fiber・C4 / C5 / C6 非空虚・値分配で subnerve ≠ 全体)を伴う正例を
   少なくとも1つ固定する。
4. report・results.json・README(off-loop 注記)を整備する。

## 停止条件と終端(どれかに達したら報告して停止)

各終端に必須成果物・Issue #3948 の扱い・本 PRD の扱いを固定する。いずれの
終端でも PRD の削除は PRD guideline の削除条件に従う(C / R0-fail 終端では
PRD は削除せず改訂対象として残す)。

- **A(成功)**: C\* が (1) R1 の必要性地図と整合 (2) 二方向の bounded 探索で
  反例ゼロ(事前登録済み bound と探索空間の normal form を報告) (3) 非退化
  正例あり (4) 各条項の独立性証拠あり (5) 両方向の手証明スケッチ付き。
  必須成果物 = completion acceptance criteria 全点。Issue の close は成果 PR
  (non-draft)の merge 後に行い、第二段の起票へ進む。
- **B(構造的否定)**: **探索範囲に依存しない一般論法(2点分離型)**により、
  incidence / support レベルの条項系では一様不変性を特徴づけられないことを
  示した場合に限る。条項の文法・有限生成規則・複雑度 bound を固定した有限
  候補族の全滅は B と数えず、coverage limit 付きの限定的結論として report に
  置き、C 終端の証拠として扱う。必須成果物 = 一般論法の report 固定+R0 / R1
  成果物。Issue の close は成果 PR(non-draft)の merge 後(人間裁定へ)。
- **C(停滞)**: 同一 blocker で2ラウンド進展がなければ中間報告で停止。
  監査単位を固定する: **ラウンド** = R1-1 / R2 では事前登録単位(bound または
  候補 C\* の改訂を伴う Issue への登録1回)、**R1 到達前(R0)では engine 修正
  または手証明試行の Issue への記録1回**。**同一 blocker** = 同じ失敗機構への
  帰着、**進展** = 新規 verdict の確定・新規反例・候補条項の実質改訂・
  calibration 不一致の解消のいずれか。自己申告のみの早期停止は不可(Issue の
  登録・記録で監査する)。
  必須成果物 = 停滞点までの partial verdict 地図+blocker の特定+coverage
  limit。**pre-R1 停止(R0 blocker)では partial verdict 地図の代わりに、
  verdict 未着手の記録+R0 blocker の特定+試行履歴+coverage limit を提出
  する**。この終端では7条項完備の verdict 地図を要求しない(blocker 記録付きの
  停滞は縮小禁止の対象外)。Issue は open のまま人間裁定を待つ。
- **R0-fail(還元反証)**: 還元の一般手証明の破れ、または engine の外で独立
  再現(手計算または独立実装)された数学的反例に限る。calibration (a)–(e) の
  不一致は engine 側の欠陥であり、この終端に数えない(R0 手順4)。必須成果物 =
  破れの再現可能な反例データ(独立再現の記録込み)+機構分析+一様不変性の
  量化定義を立て直すための示唆。**負の成果として受理可能**(還元の誤りの発見は
  本ハントの正当な成果である)。Issue は open のまま、本 PRD を量化定義から
  改訂する。

## completion acceptance criteria(A / B 終端のみ)

本 PRD 内で completion 判定に使うのは本節だけである。ただし PRD の**削除**には、
加えて PRD guideline の全削除条件の充足が必要である: 恒久 contract・恒久ルール・
status の現行 source of truth への反映、および対象 PRD の path / filename /
title / 固有 identifier についての repository 全体 zero-reference scan を
closeout で実施する。

1. R0 calibration 5点((a)–(e))が回帰テストとして固定され全 pass し、還元の
   一般手証明(R0 手順3。Lean declaration との conjunct 対応表込み)が report
   付録に固定されている。
2. C0–C6 の7条項すべてに、verdict ごとの evidence schema に従う証拠付きの
   verdict が付いた必要性地図が report にあり、事前登録済みの探索 bound と
   normal form(Issue #3948 への登録記録)が明記されている。
3. 終端 A または B への到達が report で明示され、A の場合は C\* の条項文
   (第二段の GOAL カードにそのまま書ける形)が固定されている。
4. C\* 候補(中間候補を含む)に cohomological 条項が混入していない
   (R2-4 の資格制限)。
5. 成果物一式(engine、tests、results.json、report、README)が
   `research/experiments/g104-necessity-map/` に置かれ、README 冒頭に
   「off-loop 探索 artifact であり、GOAL 完了の証拠ではない」と明記されている。
6. 再現契約: results.json が決定的に再現される(再実行で SHA-256 一致)。
   canonical 生成コマンド、固定入力と bound、乱数不使用(使用する場合は seed
   固定)、serialization 規約(key 順序・数値表現)、期待 hash の記載場所
   (README と report)を必須項目とする。
7. 変更禁止対象(`research/experiments/g104-condition-hunt/`、G-104 カード、
   `research/reports/`、`research/lean/ResearchLean/` 配下)に diff がない。
8. 成果 PR 1本が **non-draft** で、固定 head へのレビューと CI green を経て
   merge 済みであり、Issue #3948 への完了同期が済んでいる。draft PR のままの
   完了宣言は不可。応答・commit・PR は日本語。

## checkpoint 受理条件(C / R0-fail 終端。task 完了ではない)

checkpoint の受理は task 完了・Issue close・PRD 削除のいずれの根拠にもならない
(PRD は改訂対象として残り、Issue は open のまま人間裁定を待つ)。

- 共通: completion AC の 5(成果物と README 注記)・6(再現契約。得られた
  範囲の results に適用)・7(変更禁止対象)と日本語規律を同水準で満たす。
  checkpoint の提出 PR は draft でよい。
- C 終端: 停滞点までの partial verdict 地図+blocker の特定+coverage limit が
  report にある(停止条件節の監査単位の記録で裏づける)。pre-R1 停止
  (R0 blocker)では partial verdict 地図の代わりに verdict 未着手の記録+
  R0 blocker+試行履歴+coverage limit でよい。
- R0-fail 終端: 破れの再現可能な反例データ(独立再現の記録込み)+機構分析+
  量化定義再設計への示唆が固定されている。

## Failure Contract(本タスクの失敗判定)

- calibration 不一致のまま探索に入った((e) の現行実体 oracle を欠いたまま
  歴史的 fixture 3種のみで通過した場合を含む)。
- 還元の数学的破れ(一般手証明の破れ・独立再現済み反例)を得たのに R0-fail
  終端を踏まず、量化の定義を暗黙に差し替えて続行した。
- calibration 不一致を R0-fail(還元反証)と称した。または不一致のまま engine を
  修正せずに探索へ進んだ。
- checkpoint(C / R0-fail)の受理を task 完了・Issue close・PRD 削除の根拠に
  使った。または draft PR のまま A / B の完了を宣言した。
- bound と normal form を Issue へ事前登録せずに探索した。
- verdict を evidence schema なし・bound 不明のまま宣言した。
- 有限候補族の全滅を停止条件 B(構造的否定)と称した。
- C\* に cohomological 条項(またはその量化形)が混入した。
- 変更禁止対象に手を入れた。
- 同一 blocker で2ラウンド停滞したのに停止条件 C を踏まずに続行した。

## non-goals

- Lean 証明(C\* の必要十分定理の形式化は第二段 GOAL の仕事)。
- 第二段 GOAL カードの起草(本ハントの人間裁定後に別途。番号は起票時に確定)。
- G-104 カード・report・`ResearchLean` の改訂(完了 GOAL は不変)。
- 論文A本文の変更。
- 係数体の一般化(`ℚ` 固定)、無限 regime、doctrine 間 comparison。

## 停止後の接続(参考)

人間裁定の後、第二段として C\*(または現行 C)の必要十分定理を target-theorem
GOAL として固定し、両方向の Lean 証明を `$target-theorem-loop` で行う
(`research/README.md` の routing に従う)。GOAL 番号は本 PRD では固定せず、
第二段の起票時に Issue 側で確定する。論文Aへは、終端 A なら特徴づけ定理として、
B なら現行 Atlas 定理+必要性地図(条項独立性と反例目録)を実証素材として
載せる。C 終端の場合に論文へ載せてよいのは、得られた partial verdict 地図と
blocker の記録に限る(完備な必要性地図として表示しない)。
