# AAT代数幾何版 Lean形式化 Part II: 第II部 Architecture Geometry・Site・Sheaf

対象本文: [第II部 Architecture Geometry・Site・Sheaf](algebraic_geometric_theory/part_2_architecture_geometry_sites_sheaves.md)

前提となる現行Part: Part I 第I部 Atom・対象・法則

## 問い

第I部で立ち上げた architecture object の上に、

```text
ArchCtx(A) -> admissible cover -> J_U
  -> Site_AAT(A,U,J) -> Sh(ArchCtx(A), J_U)
```

の局所性の舞台は、追加の公理なしに、Lean 上で sorry なしに立ち上がるか。
特に、admissible cover から生成された `J_U` は Grothendieck 位相の公理
(identity / base change / transitivity)を満たすか(定義7.1)。

採否規律: AAT site(定義8.1)と sheaf category(§13)の構成、およびその上で
成り立つ補題7.2A・命題4.2・命題7.2C に寄与する定義・命題だけを形式化対象に
採る。舞台の構成に寄与しない要素(例、原則、context の代表例リスト)は
対象外とする。実装中に、生成位相が公理を満たさない、または舞台の構成に
必要な仮定が本文に不足していることが見つかった場合、それは本文または
本PRDの欠陥であり、ループを停止して報告する。

## 中心方針

Part I で確立した方針を引き継ぐ。

- 本文の塔を下から積む。本PRDは第2段であり、第II部のみを対象とする。
- 忠実性契約: 定義・公理は全数形式化(docstring に本文ラベル)、証明対象は
  sorry なしで証明、例・原則は対象外。
- `Formal/AG` 以下へ実装し、`Formal/Arch` は import しない。
  `axiom` / `admit` / `sorry` / `unsafe` は導入しない。
- 台帳は `lean_theorem_index.md`(AG節、本文ラベル列付き5列表)と
  `proof_obligations.md`(future proof obligation 登録 → proved 昇格)に統合する。

本PRDで新たに加わる方針が一つある。**Mathlib への二段構えの橋**である。
site・層の定義は、まず AAT 固有の語彙(context、coverage、witness)で本文に
忠実に定義し、その上で Mathlib の対応物との一致を bridge theorem / instance と
して証明する。

```text
AAT admissible coverage  --bridge-->  CategoryTheory.Coverage
J_U (生成位相)           --bridge-->  Coverage.toGrothendieck
AAT sheaf condition      --bridge-->  Presieve.IsSheaf
AATSh(A,U,J)             --bridge-->  Sheaf J (Type u)
```

橋の向きは一方向である: AAT の定義が一次であり、Mathlib 対応物は橋を通じて
資産(sheafification、層圏の構造)を借りるために使う。Mathlib の定義を
AAT 語彙の代わりに直接使ってよいのは、本文が一般概念をそのまま指している
場合(関手としての presheaf など)に限る。どちらに該当するかの判断は
処遇表の備考に従う。

## 背景

- Part I(PR #1911 でマージ)が第I部の形式化を定義した。本PRDの実装は
  Part I の成果物(Atom carrier、公理系 A0–A8、ArchitectureObject、
  LawUniverse、ObstructionCircuit、有限モデル)に依存する。Part I の実装は
  本PRD作成時点で進行中であり、依存先が未実装の要求は prd-loop の規律に
  従い `blocked` として台帳に記録する(R0)。
- 第II部は、第III部(law algebra sheaf・obstruction ideal)、第IV部
  (obstruction cohomology)、第VIII部(measurement theory)のすべてが立つ
  舞台である。特に定義7.2B(finite poset AAT site regime)と命題7.2C は、
  ArchSig v0.4.0 の ArchMap v2(finite poset site を一次入力とする)と
  Čech evaluator の理論的土台に直結する。
- 第II部の補題群 7.2A–7.2C は番号の振り直しが保留中である(文体
  ブラッシュアップ時の積み残し)。本PRDの本文ラベルは本PRD作成時点の
  本文に従う。ループ中に振り直しが行われた場合、PRD は不変条件であるため
  ループを停止し、ラベル対応の更新を人間の判断に委ねる。

## アウトカム

本PRDの完了時点で、次が成り立つ。

1. AAT site(定義8.1)と sheaf category(§13)が Lean 上の対象として存在し、
   admissible cover から生成された `J_U` が Grothendieck 位相の公理を
   満たすことが機械検証されている。
2. 補題7.2A(witness-closure cover の U-adequacy)が、本文の仮定に相対化
   された Lean 定理として存在する。
3. 命題7.2C(finite poset regime での Čech complex の有限性と nerve 次元での
   消滅)が証明され、ArchSig の Čech evaluator が依拠する有限計算の形が
   Lean 上に存在する。
4. Part I の有限モデルが第II部の水準へ拡張され、有限 poset site・
   witness-closure cover・Čech 計算の実例が example theorem として
   検証されている。
5. 第II部の本文ラベルと Lean 宣言の対応が両台帳で追跡できる。

## 第II部ラベルの処遇表

ギャップ分析はこの表を基準に行う。

| 本文ラベル | 処遇 | 備考 |
| --- | --- | --- |
| 定義2.1 Architecture Geometry | 定義 | `(A, ArchCtx(A), J_U)` の組。第III部以降が載せる sheaf 群の置き場はコメントで示す |
| 原則2.2 Geometry Relativity | 対象外 | source / vocabulary / law universe / topology の相対化は型パラメータとして設計に反映する |
| 定義3.1 Architecture Context | 定義 | 最小モデル `(Supp, Ax, Obs)` を一次とする。一般 context は最小モデルを含む拡張として抽象化してよい |
| 例3.2 局所 view | 対象外 | |
| 定義4.1 Architecture Context Category | 定義 | 射 = readable restriction / refinement。最小 poset model を含む |
| 命題4.2 Minimal Context Finite-Meet Site | 証明 | finite-meet poset category になること。preorder と equivalence quotient 後の poset の区別を本文どおりに扱う |
| 仮定4.3 Pullback and Overlap | 定義(仮定) | pullback の存在を構造体フィールド / typeclass 仮定として置く。最小モデルでは命題4.2 の meet が実現することを補題にする |
| 原則4.4 Context Non-Generation | 対象外 | 設計コメントとして反映(context 構成は Atom を生成する写像を持たない) |
| §5.1–5.4 Restriction / Projection / Refinement / Base Change | 定義 | context 射の役割述語として。projection の forgotten != zero は非主張に置く |
| 定義6.1 Coverage Family | 定義 | |
| 例6.2 Cover の読み | 対象外 | |
| 定義7.1 AAT Grothendieck Topology | 定義+証明 | admissible cover の5条件と、生成位相 `J_U`。生成位相が Grothendieck 位相の公理を満たすことを証明する(Mathlib 橋: R4) |
| 定義7.2 U-Adequate Cover | 定義 | 5条件の述語 |
| 補題7.2A Witness-Closure Cover [CBI] | 証明 | 本PRD唯一の CBI。仮定(局所有限 witness、representable overlap、restriction-stable ideal、readable axes、visible boundary)は theorem の引数として明示する |
| 定義7.2B Finite Poset AAT Site Regime | 定義 | ArchSig ArchMap v2 の理論対応物 |
| 命題7.2C Finite Poset Computation | 証明 | Čech complex の有限性と `H^n = 0 for n > dim(nerve)`。Čech complex の有限 poset 版定義を含む(R9) |
| 原則7.3 Coverage Relativity | 対象外 | 非主張に反映 |
| 定義8.1 AAT Site | 定義 | |
| 定義9.1 Presheaf | 定義 | Mathlib の反変関手をそのまま使ってよい(本文が一般概念を指す場合に該当) |
| 定義10.1 Sheaf Condition | 定義+証明 | AAT の貼り合わせ条件を本文どおり定義し、Mathlib `Presieve.IsSheaf` との同値を bridge theorem にする(R7) |
| 定義10.2 Architecture Sheaf | 定義 | 名前付き sheaf 族(At / Law / Sig / State / Eff / Auth / Sem / Trace)は carrier をパラメータとする宣言とし、個々の中身は構成しない |
| 原則10.3 Semantic Sheaf | 対象外 | 非主張に反映 |
| 定義11.1 Gluing Data / 定義11.2 Descent | 定義 | compatible 族と cocycle 条件 |
| 定義12.1 Sheafification Gap | 定義 | canonical map `F_raw -> F_raw^+` に相対化して定義する。sheafification は Mathlib 資産または有限 poset regime での具体的構成を使い、一般論を新規開発しない |
| §13 AAT Topos への入口(AATSh) | 定義 | Mathlib の `Sheaf J (Type u)` 圏として(橋経由) |

## 要求

### R0. 前提の確認と Formal/AG/Site の立ち上げ

- 本PRDの実装は Part I の `Formal/AG/Atom` 系列に依存する。各要求の着手時に
  依存する Part I 成果物(該当する Lean 宣言)の存在を確認し、未実装の場合は
  その要求を `blocked` として tracking Issue に記録する。Part I 側の実装を
  本PRDのループで先取りしない。
- 第II部のモジュールを `Formal/AG/Site/` 以下に実装する。ファイル分割は
  本文の節構成に概ね対応させる(例: `Context.lean`, `ContextCategory.lean`,
  `Coverage.lean`, `Topology.lean`, `Adequate.lean`, `Site.lean`,
  `Presheaf.lean`, `Sheaf.lean`, `Descent.lean`, `FinitePoset.lean`)。
- ルート import(`Formal/AG.lean` 相当)に追加し、CI の `lake build` 対象に
  含める。
- 完了条件: 空でない最初のモジュールが CI でビルドされ merge されている。

### R1. Architecture Context と最小モデル(定義3.1、§5)

- architecture context の最小モデル `W = (Supp(W), Ax(W), Obs(W))` を
  定義する。一般 context は最小モデルへの読み出しを持つ抽象として
  定義してよい(本文「一般の context は、この最小モデルを含む拡張で
  あってよい」)。
- §5 の restriction / projection / refinement / base change を context 射の
  役割述語または構成として定義する。
- 完了条件: 定義が sorry なしで存在する。

### R2. Context Category(定義4.1 / 命題4.2 / 仮定4.3)

- `ArchCtx(A)` を圏として定義する。射は readable restriction / refinement
  (Supp / Ax の写り込みと Obs の functorial restriction)とする。
- 命題4.2 を証明する: 最小 context model で、support / axis / observable が
  finite meet を持ち、observable restriction が meet と整合し、morphism
  uniqueness(thin)と quotient 後の antisymmetry を仮定すると、
  `ArchCtx_min(A)` は finite-meet poset category になる。quotient を
  取らない場合の finite-meet preorder category としての読みも形式化する。
  overlap `W_i x_W W_j = W_i meet_W W_j` を構成する。
- 仮定4.3(pullback の存在)を typeclass / 構造体フィールドの仮定として
  定義し、最小モデルでは命題4.2 の meet がこの pullback を実現することを
  補題として証明する。
- 完了条件: 命題4.2 と meet-pullback 補題が sorry なしで証明されている。

### R3. Coverage Family と admissible cover(定義6.1、定義7.1前半)

- coverage family `{ W_i -> W }` を定義する。
- admissible cover の5条件(Atom support coverage / law witness coverage /
  signature axis coverage / boundary coverage / non-generation)を述語として
  定義する。required support、required witness、required axes は law
  universe `U` と selected reading のパラメータとして明示する。
- 完了条件: 定義が sorry なしで存在する。

### R4. 生成 Grothendieck 位相(定義7.1後半)と Mathlib 橋

- admissible cover 族から生成される最小の Grothendieck 位相として `J_U` を
  定義し、`J_U` が identity / base-change stability / transitivity を
  満たすことを証明する。
- Mathlib 橋: admissible cover 族を `CategoryTheory.Coverage` として表現し、
  `J_U` が `Coverage.toGrothendieck` と一致することを bridge theorem として
  証明する。生成位相の公理証明は Mathlib 側の資産を使ってよいが、
  bridge theorem によって AAT 語彙の定義が一次であることを保つ。
- 本文の注意(witness coverage は refinement 後に消えうるが、それは
  topology 側ではなく後続定理の coverage 仮定の失敗として現れる)を
  設計コメントとして記録する。
- 完了条件: `J_U` の Grothendieck 位相性と bridge theorem が sorry なしで
  証明されている。

### R5. U-Adequate Cover と補題7.2A(定義7.2、補題7.2A)

- `U`-adequate cover を、`J_U` の cover であることに加えて5条件
  (required support covered / witnesses on patches or overlaps /
  axes readable / boundary witnesses visible / restriction maps preserve
  selected witness ideals)を満たす述語として定義する。
- 補題7.2A を証明する: 局所有限な required witness family、representable な
  witness support と overlap、restriction-stable witness ideals、readable
  required axes、visible boundary witnesses の仮定の下、witness-closure
  cover は `U`-adequate である。witness-closure cover の構成
  (required witness support と boundary overlaps を含むように閉じる)を
  定義に含める。
- 仮定はすべて theorem の引数として現れ、暗黙に埋め込まない。
- 完了条件: 補題7.2A が sorry なしで証明され、`proof_obligations.md` で
  `proved` に昇格している。

### R6. AAT Site と Architecture Geometry(定義8.1、定義2.1)

- `Site_AAT(A,U,J) = (ArchCtx(A), J_U)` を定義する。
- 定義2.1 の architecture geometry `X_S^{V,U,J} = (A_S^V, ArchCtx(A_S^V), J_U)`
  を、Part I の generated object と接続して定義する。第III部以降が載せる
  sheaf 群(`O_X^U`、`I_Ob^U`、`Flat_U(X)` など)の置き場は設計コメントで
  示すにとどめる。
- 完了条件: 定義が sorry なしで存在する。

### R7. Presheaf・Sheaf 条件・Architecture Sheaf(定義9.1、10.1、10.2)

- presheaf を `ArchCtx(A)^op` 上の関手として定義する(Mathlib の関手を
  そのまま使ってよい)。本文の代表的 presheaf(AtRaw / LawRaw / SigRaw 等)は
  型シグネチャを持つ宣言として置き、中身の構成は要求しない。
- 定義10.1 の sheaf 条件(compatible local sections が一意の global section へ
  貼り合う)を本文どおりに定義し、`J_U` の cover に対する Mathlib
  `Presieve.IsSheaf` との同値を bridge theorem として証明する。
- 定義10.2 の名前付き sheaf 族を、carrier をパラメータとする宣言として置く。
- 完了条件: sheaf 条件の bridge theorem が sorry なしで証明されている。

### R8. Gluing・Descent・Sheafification Gap(定義11.1、11.2、12.1)

- gluing data(局所 section 族と overlap 上の一致)、cocycle 条件、descent
  (compatible gluing data が大域 section から来る)を定義する。
- sheaf 条件と descent の関係(sheaf ならば descent を満たす)を補題として
  証明する。
- sheafification gap を canonical map `F_raw -> F_raw^+` に相対化して
  定義する。sheafification は Mathlib 資産を橋経由で使うか、有限 poset
  regime に限った具体的構成を使う。一般 site での sheafification 理論を
  新規開発しない。
- 完了条件: 定義と sheaf-descent 補題が sorry なしで存在する。

### R9. Finite Poset Regime と命題7.2C(定義7.2B、命題7.2C)

- 定義7.2B の finite poset AAT site regime(finite poset category、finite
  meet による overlap、finite witness-closure cover による生成、係数 sheaf は
  有限 poset 上の関手、restriction の ideal / axis 保存)を定義する。
- cover-relative Čech complex の有限 poset 版を定義する: 加群値係数
  (有限 poset 上の module-valued functor)に対し
  `C^n(𝒰,F) = product over nonempty (n+1)-fold overlaps`、Čech differential、
  `H^n(𝒰,F)`。一般 site での Čech complex は Part IV(第IV部)の仕事であり、
  そちらで本定義との一致を完了条件にする。
- 命題7.2C を証明する: finite witness-closure cover の Čech complex は
  有限複体であり、cover nerve の dimension `d` に対して
  `C^n(𝒰,F) = 0`(`n > d`)、したがって `H^n(𝒰,F) = 0`(`n > d`)。
- 本文の注意(Čech cohomology が sheaf cohomology を計算するには Leray
  条件等を別途固定する)を非主張として記録する。
- 完了条件: 命題7.2C が sorry なしで証明され、`proof_obligations.md` で
  `proved` に昇格している。

### R10. AAT Sheaf Category(§13)

- `AATSh(A,U,J) = Sh(ArchCtx(A), J_U)` を、R4 の橋を経由して Mathlib の
  sheaf category として定義する。
- 第III部が使う入口(law algebra sheaf の置き場)を設計コメントで示す。
- 完了条件: 定義が sorry なしで存在する。

### R11. 有限モデルの拡張

- Part I の有限モデル(`Formal/AG/Examples/`)を第II部の水準へ拡張する:
  (a) その architecture object 上の有限 context poset を構成し、命題4.2 の
  仮定を満たすことを instance として検証する。
  (b) witness-closure cover の実例を構成し、補題7.2A の仮定と結論を
  example theorem として検証する。
  (c) その cover 上で小さい係数 sheaf の Čech complex を計算し、命題7.2C の
  消滅(nerve 次元超過での零)を example theorem として検証する。
- この拡張モデルは Part III 以降(obstruction ideal、cohomology)のゴールデン例
  として再利用できる形を保つ。
- 完了条件: (a)(b)(c) の example theorem が sorry なしで存在する。

### R12. 台帳整備

- `lean_theorem_index.md` の AG 節に第II部の宣言を追加する(本文ラベル列
  付き5列表)。
- `proof_obligations.md` に第II部の証明対象ラベル(命題4.2、補題7.2A、
  命題7.2C、R4 の位相公理、R7 の bridge theorem、R11 の example theorem)を
  登録し、進行に応じて status を更新する。
- 処遇表で「対象外」のラベルは登録しない。
- 完了条件: 両台帳が最終実装と一致している。

## 非主張(claim boundary)

- 本PRDは第III部以降の内容(law algebra sheaf、obstruction ideal sheaf、
  lawful locus、obstruction cohomology の一般論、measurement)を形式化
  しない。Čech complex は命題7.2C に必要な有限 poset 版のみを定義する。
- 命題7.2C は cover-relative Čech cohomology の主張であり、それが sheaf
  cohomology を計算するとは主張しない(Leray 条件、acyclic cover、
  refinement limit は本PRDの範囲外)。
- coverage は law universe と selected reading に相対化される(原則7.3)。
  coverage の外側にある Atom や axis について zero や lawful を主張しない。
  projection で見えなくなった axis は zero ではなく forgotten である(§5.2)。
- semantic sheaf `Sem_A` の section の中身(language game、use-rule への
  相対化)は形式化しない。carrier パラメータとしての宣言にとどめる。
- 定義10.2 の名前付き sheaf 族(At / Law / Sig / State / Eff / Auth / Sem /
  Trace)について、個々が実際に sheaf 条件を満たすことを主張しない。
  sheaf 条件の検証は対象を選んだ後続実装の仕事である。
- Mathlib 橋は AAT 定義と Mathlib 対応物の一致を主張するのみであり、
  Mathlib の sheaf theory の一般定理を AAT の主張として再輸出しない。

## 完了条件(Acceptance Criteria)

- [ ] AC1. `Formal/AG/Site` が新設され、CI の `lake build` でビルドされる。
      Part I 依存の blocked 判定が tracking Issue で運用されている(R0)
- [ ] AC2. 定義3.1 の最小モデルと §5 の射の役割が形式化されている(R1)
- [ ] AC3. 命題4.2(finite-meet poset category)が sorry なしで証明され、
      preorder / quotient 後 poset の区別が形式化されている(R2)
- [ ] AC4. 仮定4.3 が仮定として定義され、最小モデルでの meet-pullback 補題が
      証明されている(R2)
- [ ] AC5. 定義6.1 と admissible cover の5条件が形式化されている(R3)
- [ ] AC6. `J_U` が定義され、Grothendieck 位相の公理(identity / base-change /
      transitivity)が sorry なしで証明されている(R4)
- [ ] AC7. `Coverage.toGrothendieck` との bridge theorem が証明されている(R4)
- [ ] AC8. 定義7.2 U-adequate cover が形式化されている(R5)
- [ ] AC9. 補題7.2A が、仮定を明示した theorem として sorry なしで証明されて
      いる(R5)
- [ ] AC10. 定義8.1 AAT Site と定義2.1 Architecture Geometry が形式化されて
      いる(R6)
- [ ] AC11. 定義9.1 / 10.1 / 10.2 が形式化され、sheaf 条件と
      `Presieve.IsSheaf` の同値 bridge theorem が証明されている(R7)
- [ ] AC12. 定義11.1 / 11.2 / 12.1 が形式化され、sheaf-descent 補題が
      証明されている(R8)
- [ ] AC13. 定義7.2B と有限 poset 版 Čech complex が形式化されている(R9)
- [ ] AC14. 命題7.2C(有限性と nerve 次元での消滅)が sorry なしで証明されて
      いる(R9)
- [ ] AC15. `AATSh(A,U,J)` が橋経由で定義されている(R10)
- [ ] AC16. 有限モデルの拡張(site instance / 7.2A 実例 / 7.2C 消滅実例)が
      example theorem として検証されている(R11)
- [ ] AC17. `Formal/AG` 全体に `axiom` / `admit` / `sorry` / `unsafe` が
      存在しない
- [ ] AC18. `lean_theorem_index.md` の AG 節が第II部の宣言を本文ラベル列付きで
      含み、最終実装と一致している(R12)
- [ ] AC19. `proof_obligations.md` に第II部の証明対象ラベルが登録され、
      証明済み分が `proved` になっている(R12)

## 実行順序の指針

prd-loop のギャップ分析で対象を選ぶ際は、次の依存順を推奨する。

```text
R0 -> R1 -> R2 -> R3 -> R4 -> (R5, R6, R7 は並行可)
   -> R8 -> R9 -> R10 -> R11 -> R12
```

R12(台帳)は各周回で増分更新してよい。R9(finite poset regime)は R4 完了
時点から着手できる。R11 の有限モデル拡張は、Part I の有限モデルが merge 済みで
あることが前提であり、未 merge の間は `blocked` とする。
