# AAT代数幾何版 Lean形式化 PRD-1: 第I部 Atom・対象・法則

対象本文: [第I部 Atom・対象・法則](algebraic_geometric_theory/part_1_atoms_objects_laws.md)

## 問い

Atom公理系 A0–A8 を満たす任意の universe において、

```text
Atom -> AtomFamily -> Configuration
  -> ArchitectureObject -> LawUniverse
  -> ObstructionCircuit -> ArchitectureSignature
```

の塔は、追加の公理なしに、Lean 上で sorry なしに立ち上がるか(定理10.5 AAT Core)。

採否規律: この塔の構成と、その上で成り立つ Lawfulness–Zero Obstruction 同値
(定理9.3)に寄与する定義・命題だけを形式化対象に採る。塔の構成に寄与しない要素
(例、原則、外部設計語彙の読み)は対象外とする。実装中に公理の不足
(塔が立ち上がらない)または過剰(使われない公理)が見つかった場合、それは
本文または本PRDの欠陥であり、ループを停止して報告する。

## 中心方針

AG版AATのLean形式化は、計測定理(第VIII部)への最短路を取らず、本文の塔を
下から積む。本PRDはその第1段であり、第I部のみを対象とする。後続のPRDで
第II部(site・層)、第III部(law algebra・obstruction ideal)、第IV部
(obstruction cohomology)、第VIII部(measurement theory)を積む。

数学本文への忠実性は、次の契約として運用する。

| 本文の要素 | Lean上の扱い |
| --- | --- |
| 定義・公理 | 全数形式化する。各宣言の docstring に本文ラベルを記載する |
| 定理・命題(証明対象、後述の処遇表) | sorry なしで証明する |
| 定理候補 | statement のみ形式化する(第I部には存在しない) |
| 例・原則・証明の読み | 形式化対象外。原則は設計コメントとして反映してよい |

既存の `Formal/Arch`(古典的AAT)とは独立に、`Formal/AG` 以下へ新規実装する。
`Formal/Arch` の定義は import しない。古典版との橋は将来の別PRDとする。

公理系 A0–A8 は Lean の `axiom` 宣言ではなく、structure / typeclass の
フィールドとしてパラメータ化する(既存 `Formal/Arch` と同じ流儀)。すなわち
「A0–A8 を満たす任意の universe」は型パラメータと instance 引数で表し、
公理の使用は型検査で追跡可能にする。`axiom`, `admit`, `sorry`, `unsafe` は
導入しない。

Lean status の台帳は既存の2文書に統合する。

- [Lean 定義・定理索引](lean_theorem_index.md): `Formal/AG` の節を追加し、
  宣言単位の表(Lean 名 / 種別 / 意味 / Status)を維持する。AG 節の表には
  本文ラベル列(例: `I.定義3.2`)を加え、本文との対応を宣言単位で追跡する。
- [証明義務と実証仮説](proof_obligations.md): 第I部の証明対象ラベルを
  `future proof obligation` として初回登録し、ループの進行に応じて
  `proved` へ昇格させる。

## 背景

- 古典的AATの形式化は `Formal/Arch` 以下に sorry なしで存在するが、AG版本文
  (`docs/aat/algebraic_geometric_theory/`)の形式化は存在しない。
  `proof_obligations.md` の規律により、AG本文の theorem label は台帳に対応行が
  ない限り Lean status を持たない。本PRDが第I部の対応行を初めて作る。
- ArchSig v0.4.0(`docs/tool/archsig_v0_4_0_algebraic_geometry_measurement_prd.md`)は
  AG本文の Certified bounded inference 定理を proof-carrying ledger の
  `theoremRef` として参照する。最終的に第VIII部の定理群(PRD-5予定)が
  そのアンカーになるが、それらの証明は第I部の語彙の上に立つ。
- 第I部は有限組合せ論と初等的な代数のみを要し、Mathlib への依存が浅い。
  塔の最下層であると同時に、ループエンジニアリングの立ち上げに適する。

## アウトカム

本PRDの完了時点で、次が成り立つ。

1. 「AAT は Atom 公理系の上で architecture object、law、obstruction、
   signature、operation を持つ純粋な理論として立ち上がる」(定理10.5)が、
   Lean の機械検証された定理として存在する。
2. 「Lawful_U(A) iff omega_U(A) = 0」(定理9.3)が、本文の仮定
   (soundness、completeness、zero-reflecting aggregation)に相対化された
   Lean 定理として存在する。
3. 公理系 A0–A8 が空虚でないこと(有限モデルの存在)が `example` または
   instance として機械検証されている。
4. 第I部の本文ラベルと Lean 宣言の対応が `lean_theorem_index.md` で
   宣言単位に追跡でき、未証明分の残量が `proof_obligations.md` で読める。

## 第I部ラベルの処遇表

ギャップ分析はこの表を基準に行う。「証明」は sorry なしの theorem を要求する。
「定義」は型・structure・def としての形式化を要求する。

| 本文ラベル | 処遇 | 備考 |
| --- | --- | --- |
| 定義1.1 Atom | 定義 | kind / axis / subject / predicate / payload を持つ carrier |
| 例1.2–1.4 | 対象外 | Atom schema の読みは R10 の有限モデルが代替する |
| 公理A0–A8 | 定義(パラメータ化) | R1。A3 は同一性の ext 補題、A8 は doctrine 構造と一意性 |
| 命題A9 観測不完全性と存在一意性 | 定義+証明 | 観測写像 obs / projection / 非単射の読みを定義し、existence と observation の分離を小定理で示す |
| 定義3.1–3.5(Family / Support / Axis Restriction / Compatibility / Closure) | 定義 | closure は least closed superset の特徴付け補題まで(R2) |
| 定義4.1 Configuration / 4.2 Molecule / 4.4 Subconfiguration | 定義 | R3 |
| 例4.3 | 対象外 | |
| 定義5.1 Architecture Object / 5.2 Generated Object / 5.4 Object Equivalence | 定義 | R4 |
| 命題5.3 Atom-Origin | 証明 | 生成原理。構成から従うことを theorem にする |
| 定義6.1–6.3(Invariant / Family / Preservation) | 定義 | R5 |
| 例6.4 / 原則6.5 外部設計語彙の扱い | 対象外 | 6.5 は SOLID / Layered などが AAT primitive ではないことを示す読みであり、塔の構成に寄与しない |
| 定義7.1 Law / 7.2 Law Universe / 7.3 Lawfulness | 定義 | SemanticLawful / NoRequiredObstruction / RequiredSignatureAxesZero の三述語を含む(R6) |
| 例7.4 | 対象外 | 代表 law は R10 の有限モデルで NoCycle を実装する |
| 定義8.1 Obstruction / 8.2 Obstruction Circuit / 8.5 Obstruction Valuation | 定義 | 値域の zero/positive dichotomy と zero-reflecting Agg を含む(R7)。`ObstructionCircuit` は finite witness presentation として読む |
| 例8.3 Cycle / 例8.4 Substitution | 例 theorem | R10 の有限モデル上で obstruction circuit の実例として証明する |
| 命題9.1 Soundness / 命題9.2 Completeness | 定義 | 性質の定義として形式化する(本文も定義的に述べている) |
| 定理9.3 Lawfulness-Zero Obstruction [CBI] | 証明 | R8。後段の三読み一致も含む |
| 定義10.1 Object Algebra / 10.2 Operation / 10.3 Signature | 定義 | R9 |
| 命題10.4 Operation Reading | 定義 | 六つの役割を operation 上の述語として定義する |
| 定理10.5 AAT Core | 証明 | R9。本PRDの中心 |

## 要求

### R0. Formal/AG の立ち上げと CI 統合

- `Formal/AG/` を新設し、第I部を `Formal/AG/Atom/` 以下のモジュール群として
  実装する。ファイル分割は本文の節構成に概ね対応させる(例: `Atom.lean`,
  `Family.lean`, `Configuration.lean`, `ArchitectureObject.lean`,
  `Invariant.lean`, `Law.lean`, `Obstruction.lean`, `Lawfulness.lean`,
  `Algebra.lean`)。
- ルート import ファイル(`Formal/AG.lean` 相当)を置き、`lake build` の
  対象に含める。既存 CI がそのまま `Formal/AG` をビルドすることを確認する。
- namespace は `Formal/Arch` と衝突しないこと(例: `AAT.AG`)。
- 完了条件: CI で `Formal/AG` がビルドされ、空でない最初のモジュールが
  merge されている。

### R1. Atom carrier と公理系 A0–A8

- 定義1.1 の Atom carrier を、kind / axis / subject / predicate / payload を
  持つ型としてパラメータ化する(公理A1 Typing はフィールドの全域性として
  表現される)。
- 公理A3 Predicate Stability を、5成分の一致と Atom の同一性の同値として
  ext 形式の補題で与える。
- 公理A4 Composition: 有限 Atom family から configuration を構成する写像を
  与える(R3 と接続)。
- 公理A5 / A6(Law / Observation Non-Generation): law と observation が
  Atom を生成しないことを、型の構成(law は `Obj -> Prop`、observation は
  `F -> O` であり `At` を生成する写像を持たない)として設計に反映し、
  設計コメントで本文ラベルを引く。独立した theorem は要求しない。
- 公理A7: operation が Atom family を Atom family へ写すことを operation の
  型として表現する。
- 公理A8 Essential Uniqueness: extraction doctrine を構造体
  (vocabulary / semantic reading / resolution / source semantics /
  normalization を成分に持つ)として定義し、`Atomize_D : Source -> AtomFamily`
  が関数であることから canonical Atom family の一意性を theorem として
  取り出す。coarse projection `pi : F -> F_coarse` の読みを定義する。
- 命題A9: 観測写像 `obs : F -> O` を定義し、(a) 非単射な obs の下で
  異なる Atom が同じ観測値に潰れうること、(b) 観測に現れない Atom が
  存在しうること、を有限例の example theorem として示す。canonical family の
  存在一意性(A8)が観測の不完全性と独立であることを theorem として分離する。
- 完了条件: 上記の定義・補題が sorry なしで存在し、`lean_theorem_index.md` に
  本文ラベル付きで登録されている。

### R2. Atom Family(定義3.1–3.5)

- Atom family、support、axis restriction、compatibility を定義する。
- closure `cl_R(F)` を推論規則族 `R` に対して定義し、次の特徴付け補題を
  証明する: (a) `F ⊆ cl_R(F)`、(b) `cl_R(F)` は R-閉、(c) `cl_R(F)` は
  そのような集合の最小である。原始 Atom と導出 Atom の origin marker の
  区別を定義に含める。
- 完了条件: 定義と closure 特徴付け3補題が sorry なしで存在する。

### R3. Configuration と Molecule(定義4.1, 4.2, 4.4)

- configuration `C = (F, R, E)`、molecule(configuration からの制限)、
  subconfiguration `C' <= C` を定義する。
- subconfiguration が前順序(反射・推移)をなすことを補題として証明する。
- 完了条件: 定義と前順序補題が sorry なしで存在する。

### R4. Architecture Object(定義5.1, 5.2, 5.4 / 命題5.3)

- architecture object `A = (C, S, Q)`、生成関係 `F => A`、object equivalence を
  定義する。structure maps `S` と selected quantities `Q` は本PRDでは
  抽象パラメータでよい(graph / category への具体化は後続PRDの仕事)。
- 命題5.3 Atom-Origin(`forall A, exists F, F => A`)を証明する。
- 完了条件: 定義が存在し、命題5.3 が sorry なしで証明されている。

### R5. Invariant(定義6.1–6.3)

- invariant(関数形と述語形)、invariant family、preservation
  (等式形 `I(A) = I(B)` と順序形 `I(B) <= I(A)`)を定義する。
- 完了条件: 定義が sorry なしで存在する。

### R6. Law と Lawfulness(定義7.1–7.3)

- law `L : Obj -> Prop`、law universe(required / optional / derived laws、
  witness family、selected reading、coverage / exactness assumptions の
  成分を持つ)、lawfulness `Lawful_U(A) iff forall L in U, L(A)` を定義する。
- 定義7.2 の三述語 `SemanticLawful(A,U)` / `NoRequiredObstruction(A,W)` /
  `RequiredSignatureAxesZero(A,S)` を定義する。定義の段階では三者を
  同一視しない(同値は R8 の仮定の下でのみ成立する)。
- 完了条件: 定義が sorry なしで存在する。

### R7. Obstruction Circuit と Valuation(定義8.1, 8.2, 8.5)

- obstruction、obstruction circuit `O = (F_O, R_O, L)` を定義する。
- obstruction valuation の値域を、`0` の存在、positive predicate、
  zero/positive dichotomy、no cancellation at zero を成分に持つ構造として
  定義する。count(ℕ)、boolean、非負 weight が instance になることを示す。
- zero-reflecting aggregation `Agg_U` を定義し、
  `Agg_U((v_L)) = 0 iff forall L, v_L = 0` を defining property とする。
  count の和、boolean の disjunction、sup が zero-reflecting であることを
  instance または補題として示す。
- `omega_U(A) := Agg_U((omega_L(A))_{L in U})` を定義する。
- 完了条件: 定義と instance 群が sorry なしで存在する。

### R8. 定理9.3 Lawfulness-Zero Obstruction

- 命題9.1 soundness(`L(A) -> omega_L(A) = 0`)と命題9.2 completeness
  (`not L(A) -> omega_L(A) > 0`)を性質として定義する。
- 定理9.3 を本文の仮定どおりに証明する:
  すべての `L in U` で `omega_L` が sound かつ complete、`Agg_U` が
  zero-reflecting のとき、`Lawful_U(A) iff omega_U(A) = 0`。
- 定理9.3 後段の三読み一致を証明する: witness completeness、axis exactness、
  coverage、selected reading の exactness を仮定として明示した上で、
  `SemanticLawful(A,U) <-> NoRequiredObstruction(A,W) <->
  RequiredSignatureAxesZero(A,S)`。仮定は theorem の引数として現れ、
  暗黙に埋め込まない。
- 完了条件: 両定理が sorry なしで証明され、`proof_obligations.md` で
  `proved` に昇格している。

### R9. 定理10.5 AAT Core(塔の立ち上げ)

- 定義10.1 object algebra(Obj / Op / Inv / Law / Ob / Sig)、定義10.2
  operation、定義10.3 signature(selected quantities の多軸表現)を定義する。
- 命題10.4 の六役割(preservation / reflection / repair / extension /
  synthesis / translation)を operation 上の述語として定義する。
- 定理10.5 を証明する: A0–A8 をパラメータとして受け取り、Atom から
  AtomFamily、Configuration、ArchitectureObject、LawUniverse、
  ObstructionCircuit、ArchitectureSignature を構成し、object algebra を
  返す構成が Lean の関数として存在し、その各成分が本文の定義
  (R1–R7 で形式化したもの)と一致することを theorem package として示す。
- 構成が A0–A8 以外の公理に依存しないこと(`#print axioms` が標準公理のみを
  示すこと)を確認し、検証方法を記録する。
- 完了条件: 定理10.5 の theorem package が sorry なしで存在する。

### R10. 有限モデル(非空虚性)

- 公理系 A0–A8 を満たす具体的な有限 universe を1つ構成する
  (例: component / depends Atom のみの小さな vocabulary)。
- そのモデル上で、(a) NoCycle law、(b) 例8.3 の3頂点 cycle obstruction
  circuit、(c) 定理9.3 の同値の成立、を example theorem として検証する。
  例8.4 substitution obstruction も同様に与える。
- このモデルは後続PRD(第II部以降)のゴールデン例として再利用できる場所
  (例: `Formal/AG/Examples/`)に置く。
- 完了条件: 有限モデルと example theorem 群が sorry なしで存在する。

### R11. 台帳整備

- `lean_theorem_index.md` に `Formal/AG` の節を追加する。表は既存形式
  (Lean 名 / 種別 / 意味 / Status)に本文ラベル列を加えた5列とする。
- `proof_obligations.md` に第I部の証明対象ラベル(処遇表で「証明」の行:
  命題A9、命題5.3、定理9.3、定理10.5、例8.3/8.4 の example theorem)を
  登録し、ループの進行に応じて status を更新する。
- 処遇表で「対象外」とした本文ラベルは台帳に登録しない
  (`proof_obligations.md` の規律: 対応行がないラベルは Lean status を
  持たない)。
- 完了条件: 両台帳が最終実装と一致しており、AG 節の全宣言が本文ラベルを
  持つ。

## 非主張(claim boundary)

- 本PRDは第II部以降の内容(site、層、obstruction ideal、cohomology、
  measurement)を形式化しない。structure maps `S` の graph / category への
  具体化も後続PRDに委ねる。
- 定理10.5 は「公理系を満たす任意の universe で塔が構成できる」ことの
  機械検証であり、実コードベースから Atom family が抽出できることを
  主張しない。source extraction は theorem package の内側に置かない
  (`proof_obligations.md` の規律)。
- 定理9.3 は選ばれた law universe、witness family、値域、集約に相対化された
  certified bounded inference であり、選ばれていない law、witness、axis に
  ついて zero claim を出さない。
- 本PRDの完了は、ArchSig が参照する第VIII部の定理群の証明を意味しない
  (それは PRD-5 の仕事である)。
- 原則6.5(外部設計語彙の扱い)は形式化しない。SOLID / Layered などは
  AAT primitive ではなく、必要な場合だけ law presentation、cover、
  restriction compatibility、obstruction ideal、lawful locus の具体例として読む。

## 完了条件(Acceptance Criteria)

- [ ] AC1. `Formal/AG` が新設され、CI の `lake build` でビルドされる(R0)
- [ ] AC2. Atom carrier と公理系 A0–A8 が処遇表のとおり形式化され、
      A3 ext 補題と A8 一意性 theorem が証明されている(R1)
- [ ] AC3. 命題A9 の分離(existence / observation / projection /
      reconstruction)が定義され、非単射観測の example theorem がある(R1)
- [ ] AC4. 定義3.1–3.5 が形式化され、closure 特徴付け3補題が証明されている(R2)
- [ ] AC5. 定義4.1 / 4.2 / 4.4 が形式化され、subconfiguration の前順序補題が
      証明されている(R3)
- [ ] AC6. 定義5.1 / 5.2 / 5.4 が形式化され、命題5.3 Atom-Origin が証明されて
      いる(R4)
- [ ] AC7. 定義6.1–6.3 が形式化されている(R5)
- [ ] AC8. 定義7.1–7.3 と三述語(SemanticLawful / NoRequiredObstruction /
      RequiredSignatureAxesZero)が形式化されている(R6)
- [ ] AC9. 定義8.1 / 8.2 / 8.5 が形式化され、値域構造の instance(ℕ、Bool、
      非負 weight)と zero-reflecting aggregation の instance が証明されて
      いる(R7)
- [ ] AC10. 定理9.3 本体が sorry なしで証明されている(R8)
- [ ] AC11. 定理9.3 後段の三読み一致が、仮定を明示した theorem として
      証明されている(R8)
- [ ] AC12. 定義10.1–10.3 と命題10.4 の六役割が形式化されている(R9)
- [ ] AC13. 定理10.5 AAT Core の theorem package が sorry なしで証明され、
      標準公理以外に依存しないことが確認されている(R9)
- [ ] AC14. 有限モデルが構成され、例8.3 / 例8.4 / 定理9.3 の example theorem
      が検証されている(R10)
- [ ] AC15. `Formal/AG` 全体に `axiom` / `admit` / `sorry` / `unsafe` が
      存在しない
- [ ] AC16. `lean_theorem_index.md` の `Formal/AG` 節が本文ラベル列付きで
      最終実装と一致している(R11)
- [ ] AC17. `proof_obligations.md` に第I部の証明対象ラベルが登録され、
      証明済み分が `proved` になっている(R11)

## 実行順序の指針

prd-loop のギャップ分析で対象を選ぶ際は、次の依存順を推奨する。

```text
R0 -> R1 -> R2 -> R3 -> R4 -> (R5, R6, R7 は並行可) -> R8 -> R9 -> R10 -> R11
```

R11(台帳)は各周回で増分更新してよい。R10 の有限モデルは R7 完了時点から
着手できる。
