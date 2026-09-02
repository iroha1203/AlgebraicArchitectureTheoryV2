# 冪等 exchange 構造と高次整合の研究図 — G-116 改訂の設計と育てる仮説

本ノートは考察ノートである。新しい公理・定義・定理は導入せず、証明済み定理の
statement を変更しない。目的は二つある。一つは、Issue #4341 の議論で決まった G-116
改訂の設計を書き留めること(§1–§5)。もう一つは、同じ議論で出てきた研究仮説を、
数学的な中身、定理になるための条件、置き場所の三点で書き、育てる候補として残すこと
(§6–§7)。経緯は Issue #4341 にある。

## 要旨

1. G-110 の generated comparison `β` は、cell ごとに二つの射の合成 `β_c = α_c ≫ E_c` に
   分かれる。`α` は canonical mate で、可逆である。`E_c` は、cell ごとに diagnostic が
   選んだ射(firing かつ admissible なら canonical normalization、それ以外は恒等射)を
   transport で運んだものである。この成分式は証明済み。finite axis-fold で `E_c` が
   同型にならないことも証明済み。`β` 全体が同型でないことは、G-116 で固定する結論で
   ある。`β` が同型にならないのは exchange が壊れたからではない。観測に見えない fiber
   の方向を `E_c` が潰しているからである。
2. object の水準の canonical normalization `n_P` は、configuration へ落としてから戻す
   写像 `s_P ∘ π_P` である。固定点は `AtomConfiguration U` と一対一に対応する。`n_P` で
   値が変わらない関数は、configuration を通って一意に分解する。これは normalization で
   不変な関数についての局所的な命題で、n1001 の因子化テーゼ(AAT の結論は Atom 層を
   通る)への橋は別の義務になる。
3. exactness は三つの層に分かれる。raw(そのままの圏で `β` が同型か)、image(Karoubi
   の像の上で同型か)、observable(観測できる関数の上で `β` と `α` が一致するか)。raw で
   壊れても、image と observable では回復する。これが G-116 改訂の中心定理候補
   **Split Configuration Descent and Idempotent Beck–Chevalley Exactness** である。
4. G-116 は Gr4 の最後のカードではない。Gr4 達成記録(O19)と、O12 のうち G-114 / G-115
   に関わる部分は、Gr4 を閉じる別のカードへ送る。G-116 は正規化因子の数学的な正体を
   突き止めるカードになる。
5. 高次化の入口は bisimplicial object より手前にある。package の水準で `N ≫ N = N` と
   `N ≠ 𝟙` が立つという仮定のもとで、diagnostic の選択子 `χ_N(g) = if g = 1 then 𝟙 else N`
   は群の積を保たず、壊れるのは `g` と `g⁻¹` が打ち消し合う場合だけになる(候補
   theorem。前者の仮定はまだ未証明)。これが lax projector law として G-117(候補)の
   target になる。
6. G-115 の負例は三つの型に揃っている。垂直方向は情報を運ばない。lossy な collapse は
   可逆性の材料にならない。coefficient の水準では自明な comparator の差が descent を
   反転させる。研究仮説はこう読む。可逆な変更と不可逆な意味射影がぶつかると strict な
   exactness が壊れ、正しい比較は可逆でない 2-cell になる。
7. 育てる候補として、二軸の研究地図(完備化の種類 C と coherence の深さ H)、Semantic
   Equipment、Descent Transporter / Diagnostic Partial Symmetry、semantic coherence
   height、SHIGURE の n-stack 化、SFT への含意、CS への一般化を §6 に置く。§7 の反証
   ゲート 7 本で、どの段でも止まれる。

## 参照

**事実関係の判定基準**:

- [G-116 カード](../../research/goals/G-116-aat-gr4-capstone.md)(改訂前の
  義務台帳 O1–O20 と O12 / O19 の定義)
- [G-110 カード](../../research/goals/G-110-aat-doctrine-fiber-product.md)
  (canonical mate exactness、MateCoherentRel 正負対)
- [G-115 カード](../../research/goals/G-115-aat-upper-stage-lift.md)
  (comparator descent 正負対、carrier-conservativity)
- Lean reviewed artifact(`research/lean/ResearchLean/AG/` 配下):
  `DoctrineFiberProduct/BCAuthoredCanonicalObjectNormalization` (+`Witnesses`)、
  `DoctrineFiberProduct/BCAuthoredDiagnosticObjectCollapseProducer` (+`Witnesses`)、
  `DoctrineFiberProduct/BCAuthoredSupportCanonicalMate`、
  `DoctrineFiberProduct/BCAuthoredComparisonNoGo`、
  `DoctrineFiberProduct/BCAuthoredFixedTargetQuotientNoGo`、
  `DoctrineFiberProduct/BCDiagnosticAxisFoldComparisonWitnesses`、
  `DoctrineFiberProduct/UpperGeometryCompatibleComparatorIncoherence`、
  `DoctrineFiberProduct/UpperGeometryRealizationExactnessWitnesses`、
  `DoctrineFiberProduct/UpperGeometryPairedCoefficientTrivialReselection`、
  `DoctrineFiberProduct/UpperGeometryFullPairedReselection`、
  `CrossStageCoherence/CorePseudofunctor`、`TransportCoherence/FinitePresentation`、
  `StructuralCover/GeneratedH1Vanishing`、`AtomFoundation/Transport`、
  `AtomFoundation/Categories`
- `Formal/AG/ReadingFunctoriality/Core.lean`(`SignedExactCoreReadingHom` の
  `object_formation_eq` / `configuration_eq`)

**上流考察ノート**:

- [n1001](n1001_atom_is_all_you_need_discussion.md)(§1 因子化テーゼ、§3.5 達成階梯
  Gr0–Gr4)
- [n1004](n1004_aat_denotational_semantics_of_architecture.md)(§10 SHIGURE)
- [n1005](n1005_aat_semantic_geometry_route_after_g107.md)(§4.3 exchange-failure
  義務)
- [n1007](n1007_aat_sakura_gr4_completion_design.md)(§3 義務台帳、§7 Gr4
  達成記録の成立条件)

**議論の記録**: Issue #4341(設計案、実査、高次化、研究プログラム案、合意の確定)。

## 記号と証明の状態

本ノートで使う記号を、型と証明の状態ごとに分けておく。

| 記号 | 型 | 定義 | 状態 |
|---|---|---|---|
| `n_P` | `ArchitectureObject U → ArchitectureObject U` | `canonicalObjectNormalization P`。object の写像 | 冪等性は証明済み(`canonicalObjectNormalization_idempotent`) |
| `N_P` | `P ⟶ P`(`PackageTotalHom`) | `canonicalObjectNormalizationTotal P adm`。package の射。underlying の object 写像は `n_P` | package の水準の冪等性 `N_P ≫ N_P = N_P` は未証明 |
| `α` | natural transformation | `authoredSupportCanonicalMate`。canonical mate | 同型であることは証明済み |
| `β` | natural transformation | `generatedAuthoredDiagnosticObjectCollapseComparison`。generated comparison | 成分式 `β_c = α_c ≫ E_c` は証明済み(`..._app`)。`β` 全体が同型でないことは未固定 |
| `E_c` | 各 cell `c` での射 `V_c ⟶ V_c` | `authoredViaBaseDiagnosticObjectCollapseComponentAtCochain`。選択子で選んだ射を transport したもの | finite axis-fold で firing cell では同型でない(`finiteAxisFold_viaBaseGeneratedObjectCollapseComponent_not_isIso`)。global な `E : V ⟶ V` は名前付きの宣言がない |
| `ν` | modification | G-117(候補)で作る、fiber を貫く自然な冪等射 | 未構成 |

以下、`U(h)` で package の射 `h` の underlying の object 写像(`h.upper.objectMap`)を
表す。

## §1 出発点 — 反例の形

G-110 sector の authored lax square には、比較射が二本ある。

- canonical mate `α : D ⟶ V`。`authoredSupportCanonicalMate` で作られ、同型であることが
  証明済み。
- generated comparison `β : D ⟶ V`。`generatedAuthoredDiagnosticObjectCollapseComparison`
  で作られる。cell ごとの式は `authoredDiagnosticObjectCollapseComparisonAtCochain_app` の
  statement そのもので、`β_c = α_c ≫ E_c` である。

`E_c` は、southwest fiber で選ばれた endomorphism を transport functor
(`coreFiberTransportFunctor` から `selectedCoreFiberReindexFunctor`)で運んだものである。
どの endomorphism を選ぶかは `authoredDiagnosticObjectCollapseComponentAtCochain` が
決める。各 cell で、raw defect が `1` なら恒等射、`1` でなく admissible なら `N_P` の
成分、それ以外は恒等射を選ぶ。以下、raw defect が `1` でない cell を firing と呼ぶ。

`N_P := canonicalObjectNormalizationTotal P adm : P ⟶ P` は admissible な support package
`P` ごとの canonical normalization で、underlying の object 写像が `n_P` である。admissible
というのは、選んだ equation / operation / invariant / coordinate の各 reading が `x` と
`n_P x` を区別しないこと(`CanonicalObjectNormalizationAdmissible P`)。

finite axis-fold witness では、次が同時に成り立つ。

| 事実 | 宣言 |
|---|---|
| 全 cell で admissible | `finiteAxisFold_canonicalNormalizationAdmissibleAt` |
| `N_P` は同型でない(`n_P` が単射でない) | `finiteCanonicalObjectNormalizationTotal_not_isIso` |
| support の側の normalization 成分は同型でない | `finiteAxisFoldCanonicalNormalizationSupportComponent_not_isIso` |
| transport 後の `E_c` は firing cell で同型でない(前提 `cochain cell ≠ 1`) | `finiteAxisFold_viaBaseGeneratedObjectCollapseComponent_not_isIso` |
| 公開関係の反証。reselection / replacement をしても変わらない | `finiteAxisFoldBCDatumSquare_not_mateCoherentRel`、`finiteAxisFold_reselectEdges_not_mateCoherentRel`、`finiteAxisFold_replacePresentation_not_mateCoherentRel` |
| admissibility が空虚な条件でないことの対照例 | `auxiliarySensitiveCorePackage_not_admissible` |
| presentation replacement に関する自然性 | `generatedAuthoredDiagnosticObjectCollapseComparison_replacement`、`mateCoherentRel_replacePresentation_iff` |

`α_c` が同型で `E_c` が同型でないので、firing cell では `β_c` は同型でない。`β` 全体が
同型でないことはここから従うが、名前付きの theorem はまだない(G-116 で固定する)。

つまり、ここで見えた「同型でない」は、名前を付けて閉じる種類の反例ではない。比較射の
ずれには二つの因子があり、性質がちょうど裏返しになっている。

| | raw comparator residual(twist) | canonical normalization factor(`N`) |
|---|---|---|
| 可逆か | 可逆(`authoredViaBaseRawDefectComponent_isIso`) | 可逆でない |
| reading への作用 | coordinate に非恒等作用 | admissible なら 4 readings から見えない |
| cofork | 固定した finite target では作れない(`finiteAxisFold_viaBaseRawDefect_no_cofork`: 固定した transported residual と恒等射の標準 `Cofork` が存在しない。この有限 target に限る) | 冪等性が立てば `N` 自身が cofork になる(候補) |
| 分類上の扱い | canonical-post-iso twist は既知の系として数える | 本体。改訂 G-116 の対象 |

反例が教えているのは、この分解である。可逆で観測に見える twist の部分と、冪等で観測に
見えない正規化の部分。§2.4 の見込みが定理になれば、正規化の部分の像は package 圏の中
には作れない。そのとき住める場所は、Karoubi(冪等射を形式的に分裂させた圏)、
configuration の商、localization(候補)のどれかになる。

## §2 中心定理候補 — Split Configuration Descent and Idempotent Beck–Chevalley Exactness

### 2.1 configuration へ落として戻す

package `P` に対して、二つの写像を置く。

```text
π_P : ArchitectureObject U → AtomConfiguration U,   π_P(x) := x.configuration
s_P : AtomConfiguration U → ArchitectureObject U,   s_P(c) := P.reading.objectReading.object c
```

`π_P` は object から configuration を読む。`s_P` は configuration から `P` の object reading
で object を作る。`ObjectReading.configuration_eq` により `π_P ∘ s_P = id`。定義から
`n_P = s_P ∘ π_P`。つまり `n_P` は、configuration へ落としてから戻す写像である。既存の
`canonicalObjectNormalization_configuration`、`..._selected`、`..._idempotent` は、この
落として戻す構造からそのまま出る。object 写像の冪等性は偶然ではない。

ここから `Type` の水準で次が言える(候補、証明は数行)。

```text
Fix(n_P) := {x // n_P x = x}  ≃  AtomConfiguration U
```

行きは `π_P`、帰りは `s_P`。さらに任意の型 `Y` と関数 `f : ArchitectureObject U → Y` に
ついて

```text
f ∘ n_P = f   ↔   ∃! f̄ : AtomConfiguration U → Y,  f = f̄ ∘ π_P
```

証明はこうである。左から右は `f̄ := f ∘ s_P` と置く。`f̄ ∘ π_P = f ∘ n_P = f` なので存在
する。別の `f̄'` が `f = f̄' ∘ π_P` を満たすなら `f̄' = f̄' ∘ π_P ∘ s_P = f ∘ s_P` なので
一意である。右から左は `f ∘ n_P = f̄ ∘ π_P ∘ s_P ∘ π_P = f̄ ∘ π_P = f`。

言い換えると、`π_P` は `n_P` と `id` の split coequalizer である。`ArchitectureObject U`
の上に同値関係 `x ≈_P y :↔ π_P x = π_P y`(同じことだが `n_P x = n_P y`)を置くと、商
`ArchitectureObject U / ≈_P` は `AtomConfiguration U` と同一視できる。

observable の定義はこう固める。

```text
Observable_P(f) :≡ f ∘ n_P = f
```

正規化しても値が変わらない関数のことである。上の同値から、observable な関数は必ず Atom
configuration を通って一意に分解する。

これは n1001 §1 の因子化テーゼ(AAT が語れる結論は Atom 層を通る)の局所モデルで
あって、テーゼそのものではない。テーゼは「AAT の結論」や「doctrine で不変な結論」という
実質的な対象についての主張である。ここで示せるのは「`n_P` で不変な `Type` 値の関数は
configuration を通る」までで、「AAT の結論なら `n_P` で不変」と「configuration から
canonical Atom family へ降りる」の二つの橋がない。同じ Atom family を持ちながら relation
が異なる configuration を、relation の値で読み分ける関数は、この飛躍の反例になる。二つの
橋は別の義務にする。

選んだ reading の共通核で商を取る定義もありうる。しかし reading が configuration を
区別しない場合、その商は configuration より粗くなる。だから observable の主定義には
使わず、後ろに置く。

admissibility の各 field は、reading が `π_P` に沿って降りるためのデータと読める。
`equationResidual_eq` と `coordinate_eq` は、ふつうの関数の分解を与える。
`operation_type_eq` と `operation_naturality` は、object の対に依存する operation family
の dependent な descent data である。`invariant_transport` は invariant を降ろすデータで
ある。operation と invariant の分解が実際に作れるかどうかは、「できる / できない」を
決める義務にする。

### 2.2 冪等因子と三つの exactness

`α_c` が同型なので、cell ごとに次が置ける。

```text
E_c := inv α_c ≫ β_c : V_c ⟶ V_c,      β_c ≫ inv α_c : D_c ⟶ D_c
```

最初に必要なのは、package の射の水準で `E_c ≫ E_c = E_c` を示すことである(§2.3)。

これが通ると、Karoubi の圏で `β_c` は同型になる。Karoubi の圏というのは、対象を「元の
圏の対象と冪等射の組 `(X, e)`」に取り、射を `e` と両立する射に取った圏のこと。`β_c` は
`(D_c, β_c ≫ inv α_c)` から `(V_c, E_c)` への射で、逆射の候補は `E_c ≫ inv α_c` である。
二つの合成 `β_c ≫ E_c ≫ inv α_c = β_c ≫ inv α_c` と `E_c ≫ inv α_c ≫ β_c = E_c` は、
それぞれ projector に戻る。

exactness は三つの層に分ける。observable の層は `Type` の水準で書く。`q` は
`ArchitectureObject U` から適当な型への関数で、`U(·)` は underlying の object 写像である。

```text
raw exactness        : IsIso β_c
image exactness      : Karoubi の像 (V_c, E_c) の上で β_c が可逆
observable exactness : q ∘ U(E_c) = q を満たす q に対して  q ∘ U(β_c) = q ∘ U(α_c)
```

圏の側で書くなら `q : V_c ⟶ Q` とし、`E_c ≫ q = q` から `β_c ≫ q = α_c ≫ q` を言う。
この二つの書き方は分けて扱う。`Type` の側の商 `≈_P` と圏の側の商は別物である。

そのままの圏では壊れていても、意味の像と observable の商の上では成り立つ。これは反例を
消しているのではない。`β_c` が同型でない理由が「冪等像の外側を落としているから」だと
説明している。

observable の層を圏の中へ戻す道には、一つ障害がある。`coforkReturn_not_isIso_of_ne` は、
恒等でない endomorphism と恒等射の cofork から元の対象へ戻す射を取ると、その合成は可逆に
ならない、と言う。つまり raw の package object へ可逆に戻す経路は閉じている。ただし、
この theorem は cofork や商対象の存在、別の弱い射の圏の可能性までは否定していない。
最初の定理候補は「observable の exactness は configuration の水準の exactness と同じ」
という主張である。

raw で壊れる条件は projector の側に移せる。cell ごとに

```text
IsIso β_c ↔ IsIso E_c,        E_c ≫ E_c = E_c なら  IsIso E_c ↔ E_c = 𝟙
```

だから見るべきは「比較射が可逆か」ではなく「選ばれた projector が恒等か」である。
選択子の作り方から、cell の水準では、raw で壊れることと「firing かつ admissible かつ
正規化が非自明」は同じである。これを一般の同値として書くには、transport / reindex
functor が conservativity を持つこと(像が同型なら元も同型)が要る。これは別の義務に
する。証明するか、G-113 の O13・O18 から導くか、成り立たないか、を決める。

### 2.3 自然性と、いちばん難しい一点

`SignedExactCoreReadingHom` は次の二つの field を持つ。

```text
object_formation_eq : ∀ C, objectMap (P.reading.objectReading.object C)
                          = Q.reading.objectReading.object (C.transport atomEquiv)
configuration_eq    : ∀ A, (objectMap A).configuration = A.configuration.transport atomEquiv
```

だから任意の `f : P ⟶ Q`(`PackageTotalHom`)について、`f.upper.objectMap` と
`f.upper.atomEquiv` で

```text
f.upper.objectMap (n_P x)
  = f.upper.objectMap (P.reading.objectReading.object x.configuration)
  = Q.reading.objectReading.object (x.configuration.transport f.upper.atomEquiv)
  = Q.reading.objectReading.object ((f.upper.objectMap x).configuration)
  = n_Q (f.upper.objectMap x)
```

object 写像の水準では、正規化はすべての exact hom に対して自然である。診断の選択で
壊れうるのは `n_P` そのものではない。firing と admissibility という、入力に依存する選択
ゲートの側だけである。

package の水準の冪等性 `N_P ≫ N_P = N_P` は、`PackageTotalHom.ext` を経て
`SignedExactCoreReadingHom.ext` の 7 条件に落ちる。6 つは機械的に閉じる見込みである。
残る一つ、`EquationSystemExactTransport` に関する `HEq` が、いちばん難しい一点である。
ただし `finiteAxisFoldPermutationTotal_comp` は、同じ support package 上の合成で 7 条件
すべてを `rfl` で閉じている。context の圏は常に thin なので、定義的に潰れる余地がある。
そこで最初の義務を「`EquationSystemExactTransport` の ext 補題と refl-trans の等式」に
する。落ちた場合は、どの等式が成り立たないかを theorem の形で示す。`HEq` が難しいこと
と、数学的な coherence が実際に壊れていることは別である。先回りして高次 obstruction と
読まない。

### 2.4 圏の中では分裂しない(見込み、未証明)

主張: 任意の `P Q : AATCorePackage U`、`adm : CanonicalObjectNormalizationAdmissible P`、
`r : P ⟶ Q`、`i : Q ⟶ P` について、`i ≫ r = 𝟙 Q` かつ
`r ≫ i = canonicalObjectNormalizationTotal P adm` は成り立たない。ただし、同じ
configuration の上に相異なる二つの `ArchitectureObject` があるとき(この witness も
theorem の引数に置く)。`adm` は省けない。admissible でない package は実在する
(`auxiliarySensitiveCorePackage_not_admissible`)。

証明の見込み。`a := r.upper.objectMap`、`b := i.upper.objectMap` と置くと `a ∘ b = id`、
`b ∘ a = n_P`。`n_P ∘ b = b ∘ a ∘ b = b` なので、`b` の像は `Fix(n_P)` に入る。
`a ∘ b = id` なので `b` は単射である。同じ configuration の上の `x₁ ≠ x₂` を取る。
`configuration_eq` により `b x₁` と `b x₂` の configuration は等しい。`Fix(n_P)` は
configuration ごとに一点しかないので `b x₁ = b x₂`。単射性と矛盾する。

効いているのは大きさの非対称である。object の fiber は configuration ごとに
`StructureMaps` 全体を走るので大きい。正規化の固定点は configuration ごとに一点しか
ない。有限 witness の性質は使っていない。

ここで問いは四つに分かれる。cofork / coequalizer が存在するか、split retract が存在
するか、return map が存在するか、戻した合成が可逆か。既存の theorem が言うのは最後の
一つだけである。G-116 が固定した義務として引き受けるのは split retract の no-go
(上の主張)で、残りは候補のままにする。no-go の Lean 化で偽・型不能・反例が判明した
場合は、成功枝へ移らず `goal-defect` として止まり、人間の判断で target を改めてから
構成 / no-go の二枝に戻す。

見込みが定理になった場合の帰結は二つある。

- 判定順序の「圏の中で分裂するか、しないか」は、しない側で決まる。
- 分裂しないのは正規化の欠陥ではない。raw な `ArchitectureObject U` を carrier に固定した
  今の package 圏が、意味の像を対象として持てないほど狭い、という圏そのものの定理に
  なる。そのとき Karoubi は便宜的な逃げ道ではなく、意味の像を表すための最小の完備化に
  なる。分裂像 `P ↦ Q` の functor 性を経由して reflective localization を作る道は、前提
  ごと消える。localization を候補に残すなら、正規化射のクラス `W` を形式的に逆転した
  `C[W⁻¹]` として、Karoubi の後に別に立てる。

同じ仕組みが G-115 にも出ている。`negativeCoreUpper_objectMap_not_injective` と
`no_negativeExactUpperEquivalence` である。lossy な upper は、同じ configuration の上の
装飾だけが違う二つの object を潰す。打ち消しが要求する単射性とは両立しない。

### 2.5 有限 witness の六つの役割

| 役割 | 内容 |
|---|---|
| carrier | 同じ configuration の上の相異なる raw object |
| firing | raw defect が `1` でない cell |
| admissibility | 全 cell で admissible |
| noninjectivity | `n_P x = n_P y` かつ `x ≠ y` |
| selected reading preservation | 選んだ reading が `x` と `n_P x` を区別しない |
| separation | 選んだ reading が少なくとも二つの configuration を区別する |

最後の separation がないと、observable 層の正の定理が退化した例(すべてを潰す reading)
でも成り立ってしまう。observable の側では、`q ∘ n_P = q` を満たす具体的な `q` を名前
付きで作り、それが二つの configuration を分けることを theorem にする。`q` が observable
であることを前提として受け取るだけでは、定数関数でも成り立ってしまう。witness packet
は `E_c ≠ 𝟙`、`β_c` が同型でないこと、observable が保たれることの三つを同時に示す。

## §3 G-116 改訂カードの骨格

### 3.1 責務の切り離し

G-116 は Gr4 の最後のカードではない。O19(Gr4 達成記録)と、O12 のうち G-114 の active
refinement mate と G-115 の `upperDecisionSolution` が同型かどうかを決める義務は、Gr4 を
閉じるカード(別途、番号は先取りしない)へ送る。義務は黙って消さず、行き先を表に残す。

| 旧義務 | 行き先 |
|---|---|
| O12 universal 枝 | cell の水準では、firing cell の `E_c` が同型でないことが証明済み(`finiteAxisFold_viaBaseGeneratedObjectCollapseComponent_not_isIso`)。`β` 全体が同型でないことは G-116 で名前付きの theorem に固定し、それをもって反証として記録する |
| O12 named-failure 枝 | 旧 branch は、固定した cell と component の上で、caller が証明書を持ち込まずに `¬ IsIso` を評価する branch だった。その評価は ob.8 / ob.9 に残し、結論を §2 の構造定理に置き換える |
| O12 の G-114 / G-115 成分 | Gr4 を閉じるカードへ |
| O19 | Gr4 を閉じるカードへ |

### 3.2 proof obligations(判定の順)

| # | 義務 | 既存の宣言・状態 |
|---|---|---|
| 1 | package の水準の冪等性 `N_P ≫ N_P = N_P` | object 写像は `canonicalObjectNormalization_idempotent`。ext 補題群は名前付きの artifact にして、後続カードが使う |
| 2 | object 写像の水準の自然性(全 exact hom) | `object_formation_eq` + `configuration_eq` の計算を補題にする |
| 3a | `β_c = α_c ≫ E_c` であること、replacement に関する自然性 | 証明済み(`..._app`、`..._eq_canonical`、`..._eq_provenance`、`..._replacement`) |
| 3b | `E_c ≫ E_c = E_c` | 未証明。ob.1 と transport の functor 性から導く |
| 4 | Karoubi exactness: `β_c : (D_c, β_c ≫ inv α_c) ⟶ (V_c, E_c)` が同型 | 未証明(ob.3b を仮定した条件付き候補)。圏の一般 API は mathlib `Idempotents.Karoubi` にあるが、AAT の instance での theorem はまだない |
| 5 | 圏の中では分裂しないこと(no-go を固定した義務とする。signature に `adm` と同一 configuration 上の相異なる object の witness を含める。偽・型不能・反例なら `goal-defect` で停止) | 未証明(§2.4 の見込み) |
| 6 | configuration descent: `Fix(n_P) ≃ AtomConfiguration U`、一意分解、`ArchitectureObject U / ≈_P ≃ AtomConfiguration U`。dependent な reading は「できる / できない」を決める | 未着手。Čech nerve の装置は G-118(候補)へ |
| 7 | observable exactness(`Type` の側: `q ∘ U(E_c) = q ⇒ q ∘ U(β_c) = q ∘ U(α_c)`)と「observable exactness = configuration 水準の exactness」 | 圏へ可逆に戻す障害は `coforkReturn_not_isIso_of_ne` |
| 8 | raw で壊れる場所: cell ごとに `IsIso β_c ↔ IsIso E_c ↔ E_c = 𝟙`。`β` 全体の `¬ IsIso` を名前付きにする。一般の同値に必要な transport の conservativity は別の義務 | 未着手 |
| 9a | witness packet のうち carrier / firing / admissibility / noninjectivity | 証明済み(`finiteCanonicalObjectNormalizationTotal_not_isIso`、`finiteAxisFold_viaBaseGeneratedObjectCollapseComponent_not_isIso`、`finiteAxisFold_canonicalNormalizationAdmissibleAt`、対照例 `auxiliarySensitiveCorePackage_not_admissible`) |
| 9b | 名前付きの observable `q`、`q ∘ n_P = q`、二つの configuration の分離、`E_c ≠ 𝟙` と observable 保存の同時成立 | 未構成 |
| 10 | 行き先の表と evidence map | §3.1、§3.4 |

### 3.3 定型項目

- 作業名: **Split Configuration Descent and Idempotent Beck–Chevalley Exactness**。
- research aim: generated comparison を、可逆な canonical mate と冪等な normalization
  projector に分解する。raw exactness が壊れる場所を projector の非自明性で分類する。
  image と observable の各層で exactness が回復することを、有限 witness つきで決める。
- rival: Beck–Chevalley の古典論と、冪等射の分裂の古典論(Karoubi の一般論)。差は、
  diagnostic による選択、admissibility、observable の分離を証明の中で実際に使う点に置く。
- dullness filter(新規性のない構成を弾く条件): mathlib の Karoubi API を包み直しただけ
  の構成、二点半束の lax law だけを単独で数える構成を弾く。`E_c` が、選択子で選んだ
  局所の canonical normalization `N_P` の成分を transport / reindex / provenance iso で
  運んだもの(`E_c = transport(selector(rawDefect c, N_P))`)であることを、証明の必須
  要素にする。global な modification `ν` との対応は G-117(候補)の仕事で、G-116 では
  要求しない。
- 命名: id `G-116` は変えない。filename は `G-116-aat-idempotent-exchange-structure.md`
  にする。旧 slug との対応は README に書く。改訂時に同期するもの:
  `research/goals/README.md`、関連 note、GOAL 間の参照、Issue #4248 の「G-116 は現行型で
  走り切る」という記述。
- program context: Gr4 系列。Gr4 完成をどう表現するかは、閉じるカードで決める。
- ArchSig: 後続の client route として分ける。AAT 側は observable predicate と theorem
  interface だけを定める。ArchSig の artifact や実装の挙動を theorem の前提にしない。

### 3.4 evidence map

Issue 備考の 5 module(`BCAuthoredCanonicalObjectNormalization`、
`BCAuthoredDiagnosticObjectCollapseProducer`、両 `Witnesses`、
`BCAuthoredSupportCanonicalMate`)に加えて、行き先の表が根拠として引く群を載せる:
`BCAuthoredFixedTargetQuotientNoGo`、`BCAuthoredFixedTargetCoforkNoGoWitnesses`、
`BCAuthoredComparisonNoGo`(+`Witnesses`)、`BCAuthoredFactorizationComparison`
(+`Witnesses`)、`BCAuthoredPreMateInsertionNoGo`、
`BCAuthoredComparatorInductionObstruction`、`BCAuthoredNonAxisCollapseAudit`、
`BCAuthoredObjectCollapse`、`BCAuthoredDiagnosticObjectCollapse`、
`BCAuthoredDiagnosticPresentationReplacement`(+`Witnesses`)。twist を既知の系として
数える判断と、非可逆性が object 写像にあるという判断は、この群が根拠になる。パスは
すべて `research/lean/ResearchLean/AG/DoctrineFiberProduct/` 配下である。

## §4 後続カードの切り分け(候補)

Issue の解決方針 7 項目と行き先の対応。以下の番号と骨格は仮置きで、カード起票時に
改める。

| 解決方針 | 行き先 |
|---|---|
| 1 冪等性の持ち上げ / 分裂 | G-116 ob.1、ob.5 |
| 2 `β = α ≫ E` と自然性 | G-116(replacement、object 写像)/ G-117(base-arrow、modification) |
| 3 圏論的な住処 | G-116(Karoubi + 圏の中では分裂しないこと)。`W`-inversion は G-118 の候補素材 |
| 4 raw / observable の分離 | G-116 ob.7 |
| 5 同型でない場所 | G-116 ob.8 |
| 6 有限例 | G-116 ob.9 |
| 7 ArchSig の分離 | 後続の client route(番号なし) |
| O12 の G-114 / G-115 成分、O19 | Gr4 を閉じるカード(番号なし) |

### 4.1 G-117(候補)— Natural Idempotent Modification and Lax Diagnostic Projector Theorem

**中身**。admissible な cell の defect group を `G`、非自明な normalization を `N` と
する。今の選択子は、そのまま `χ_N(g) := if g = 1 then 𝟙 else N` である。package の
水準で `N ≫ N = N` が立つと

```text
χ_N(g) ≫ χ_N(h) = χ_N(gh)   ↔   g = 1 ∨ h = 1 ∨ gh ≠ 1
```

が成り立つ。右から左は `N ≫ N = N` で閉じる。左から右には `N ≠ 𝟙` が要る。`g ≠ 1`、
`h ≠ 1`、`gh = 1`、つまり `h = g⁻¹` の場合に

```text
χ_N(g) ≫ χ_N(g⁻¹) = N,      χ_N(gg⁻¹) = 𝟙
```

となり、`N ≠ 𝟙` がこの場合を等式から除く。defect の側では履歴が消える。projector の側
では、一度起きた不可逆な正規化が消えない。

同じ対象の上の可換な冪等射に、像の包含の順序 `e ⪯ f :↔ e ≫ f = e ∧ f ≫ e = e` を
置く。`N ⪯ 𝟙` である。すべての `g, h` について

```text
χ_N(g) ≫ χ_N(h) ⪯ χ_N(gh)
```

が成り立つ。群の作用を strict に保つのではなく、冪等射の順序への lax な作用が本体で
ある。raw の strict exchange が壊れるのは、projector が可逆でないからだけではない。
defect group の逆元と、冪等半束の積とが、本質的に違うからである。

`χ_N` は二段に分かれる。前段は「単位元かどうか」の指示関数 `G → Bool`、後段は
`tt ↦ 𝟙, ff ↦ N` の埋め込みである。lax になる原因は前段にある。これは群の一般論で、
群から冪等射だけを値に取る strict な monoid 準同型は自明なものしかない(可逆な冪等射は
恒等射だけだから)。後段が monoid 射になる条件がちょうど `N ≫ N = N`、順序の埋め込みに
なる条件がちょうど `N ≠ 𝟙` である。AAT に固有の中身は四つに集まる。package の水準の
冪等性、`N ≠ 𝟙` の witness、firing かつ admissible の cell で `E_c` が transport された
`ν` の成分であること、generated orbit で打ち消しが実際に起きること。

**proof obligations(候補)**。

1. admissibility の transport: `CanonicalObjectNormalizationAdmissible P` が canonical な
   transport `transportAlong P f` で保たれる。量化は Atom equivalence から来る transport
   に限る。一般の exact hom では、像の外の object に対する reading に制約がないので、
   admissibility は運べない。自然性は全 hom で成り立ち(object 写像の水準)、
   admissibility は equivalence 型の transport でだけ運べる。この一般性の食い違いは、
   そのままこの構造の正しい記述である。
2. admissible fiber: `CoreFiber X` のうち admissible な package からなる full subcategory
   `AdmCoreFiber X` と、`coreFiberTransportFunctor` の制限。
3. fiber の中の自然性: `ν_X : 𝟭 ⟶ 𝟭`、`ν_X.app P := N_P`、`ν_X ≫ ν_X = ν_X`。
4. base arrow との両立: `(T_f).map (ν_X.app P) = ν_Y.app ((T_f).obj P)`。G-109 の
   `coreFiberCompositor` / `coreFiberUnitor` と合わせて、`ν` を idempotent modification と
   して束ねる。
5. Karoubi への持ち上げと `E_c` の同定: fiber ごとの Karoubi completion の上で、firing
   かつ admissible の cell では `E_c` が transport / provenance iso で運ばれた `ν` の成分
   そのものだと示す。firing でない cell では `E_c = 𝟙` なので、無条件の `E = ν` は成り
   立たない。全 cell で書くなら、gate 込みの `E = χ(ν)` の形になる。既存の
   `..._eq_canonical` と `..._eq_provenance` を `ν` の成分に付け替える形になる。
6. 選択子の分類: 上の strictness の同値、`⪯` の法則、二項と三項の coherence。
7. 二本の有限 witness。**raw cochain の側**: firing の元は隣接 swap で、二乗が恒等に
   なることは `finiteAxisFoldSwapTotal_square` として定理済み。`h := g` で打ち消しの対が
   立つ。pointwise の積 cochain は `DefectCochain` の型上そのまま入力にできる。壊れの
   実体は G-116 の二義務(冪等性と `N ≠ 𝟙`)そのものである。**generated orbit の側**:
   実際の reselection や oriented pasting が `g` と `g⁻¹` の対を作るかを構成するか、
   生成される像には現れないことを定理にする。局所の defect を `δ = u · φ⁻¹` とすると、
   authored と canonical の comparator を別々に反転した逆向きの面は `δ_back = u⁻¹ · φ`
   で、`δ⁻¹ = φ · u⁻¹` とは一般に一致しない。reverse の宣言があるだけでは足りない。

ob.3 と ob.4 で残る field の等式は、G-116 の冪等性と同じ一点(§2.3)に帰着する。ext
補題群を G-116 で一度だけ作り、G-117 は同じ artifact を使う。依存の向きは G-116 →
G-117 の一方向で、G-116 は `ν` を要求しない。

**置き場所**: 独立したカード。dullness filter には、G-109 を `functorExtension₂` で
Karoubi へ持ち上げただけの構成を弾く一文を置く。

### 4.2 G-118(候補)— comparator inertia test から始める mixed descent

**入口(Test B)**。G-115 の対、`upperDecisionSolution_comparatorDescentAt`(正)と
`generatedBaseIdentityPair_not_comparatorDescentAt`(負)は、pulled comparator 以外の
route data と component を共有する。しかも `generatedPulledIdentityComparator_coefficient_id`
により、取り替えた comparator は coefficient の水準では identity である。つまり、
coefficient の水準では自明な差が descent を反転させる。この差 `Δ` を作用元として
束ね、二段で決める。

1. 「descent が成り立つ場所は comparator の取り替えで変わる」を定理にする。両点と反転は
   すでに Lean にある。足りないのは差を一つの対象にすることだけである。
2. その差の class が、presentation replacement と reselection のもとで well-defined かを
   決める。

well-defined なら、指定した coefficient の影では失われるが descent を左右する
proof-relevant な data が実在する。この時点で G-118 の存在理由が決まる。この影が圏論
の意味での 0-truncation(対象・射・普遍性・equivalence での不変性)にあたるかは、別に
構成しないと言えない。失敗した場合に否定されるのは、
今の comparator-inertia / H¹ model である。高次構造一般ではない。comparator の商の取り方、
replacement / reselection の作用の定義、horizontal な対象の粗さ、cohomology class では
なく double category の square でだけ well-defined になる可能性、span / correspondence /
profunctor 型の住処、が残る。

**その後**。Test B が通った場合にだけ、Law が選んだ横方向(cover / diagnostic /
comparator)と configuration の縦方向(Čech)の bisimplicial 構成に進む。横の次数ごとの
対象、face と degeneracy、simplicial identities、mixed square、二つの totalization の
比較を実際に作る。configuration の方向は split なので、単独では obstruction が消える。
横方向の取り方には先例がある。`generatedAllComplex_h1Zero`(G-105)は、Atom と Source が
有限のとき、全 support を無差別に取った generated な `ℚ` 係数複体の `H¹` が消えると
言う。この範囲では、無差別な横方向に残差は住めない。横方向は Law が選んだ非退化な
cover / diagnostic の方向でなければならない。

**Test A**(統一テスト)。G-114 の fiber の中の垂直射は、base への射影が恒等で
atomEquiv が強制され、非恒等な observable は cartesian lift edge(水平側)に置かれて
いる。G-115 の generated vertical component は三つの carrier 値が恒等側と `HEq` で
ある(`solution_supportSigmaMap_carrier_conservative` 系)。この二つを「恒等 base の上の
垂直 2-cell は carrier を保つしかない」という一本の定理で共通に証明できるか。G-117 の
`ν` の自然性(fiber の中では base が恒等側に固定される)と同じ仕組みなので、G-117 か
G-118 に置く。

### 4.3 G-119(候補)と Gr4 を閉じるカード

G-119 は、G-118 の mixed descent に非自明な残差が実際に残った場合にだけ、obstruction
class を設計する。二元の projector 順序では三項の coherence は自動で閉じるので、G-117
から 3-cocycle は出ない。

Gr4 を閉じるカードは O19 と、summand ごとの決定(G-114 active refinement mate、G-115
`upperDecisionSolution` が同型か)を担う。番号は先取りしない。§6.4 の `IsIso c` 枝
(conjugation regime)も、このカードの決定対象である。

## §5 負例の型 — 三つの系統と混合層

G-115 系列の負例は、高次構造を考える前から、三つの系統に揃って Lean に現れている。

**系統 1: 垂直方向は情報を運ばない。** G-114 の垂直 mate 成分は非恒等な Atom 作用を
持てず、非恒等な observable は cartesian lift edge に置かれた。G-115 の generated
vertical component は三つの carrier 値が恒等側と `HEq` であり(carrier-conservativity)、
非退化な例は水平側(edge / comparator / cochain)に置かれた。二つの段で独立に「垂直に
非自明なものを置く」試みが潰れ、どちらも水平へ移して解決した。

**系統 2: lossy な collapse は可逆性の材料にならない。**
`negativeCoreUpper_objectMap_not_injective` と `no_negativeExactUpperEquivalence`。同じ
configuration の上の装飾だけが違う二つの object を潰す以上、打ち消しが要求する単射性と
両立しない。§2.4 と同じ仕組みが、一段上でもう一度出ている。

**系統 3: descent は comparator の取り替えに敏感である。** §4.2 の対。route data を
すべて固定して comparator だけを取り替えると descent が反転する。しかも差は coefficient
の水準では自明である。

三つを並べると、「観測の層では自明なのに、strict な性質を左右するデータ」が両方向に
ある。

| | 垂直(正規化 `N`) | 水平(comparator の差) |
|---|---|---|
| 観測の層 | admissible なら 4 readings から見えない | coefficient identity を保つ |
| strict な層 | 同型性を壊す(単射でない collapse) | descent を壊す(反転) |
| 組織のされ方 | 二点の冪等半束 `{𝟙, N}`(package の水準で `N ≫ N = N`、`N ≠ 𝟙` が立てば) | defect 群の上の cochain / torsor 的な族 |

本当の定理と本当の壊れは、この混合層(`β_c = α_c ≫ E_c`、comparator descent、lax
projector law)にある。証拠として強いのは、負例がこの見方の成立より前に、証明ループ
(target-theorem-loop)の反証としてこの形へ押し込まれてきたことである。設計の意図では
なく、構造の側からの押し返しの跡である。

判定テストは三本。Test A(垂直 strictness の統一定理、§4.2)、Test B(comparator
inertia、§4.2)、Test C(G-117 の generated orbit の側の witness、§4.1)。thin な
context 圏で ext の 7 条件が `rfl` で閉じたことは、高次に見えるものの一部が定義的に
潰れる証拠でもある。`generatedAllComplex_h1Zero` は、有限の範囲で、無差別な方向には
残差が住めないことを示す。だから Test B が本丸である。残差が具体的に生き残る場所を
一つ示せた時点で、G-118 の存在理由が決まる。

## §6 育てる候補 — 研究仮説

各候補を、中身、定理になる条件、置き場所の三点で書く。

### 6.1 可逆な変更と不可逆な意味

**中身**。ソフトウェアの変更には可逆な面がある。意味の抽象化には不可逆な面がある。
両者を strict な 1-圏の等式で統一することは一般にできない。正しい相互作用は、可逆で
ない 2-cell として現れる。最小の Lean 形は §4.1 の一般論(可逆な変更の群を、非自明で
不可逆な projector へ strict に送ることはできない)である。AAT に固有の中身は、この
一般論と diagnostic の選択子 `χ_N`、generated comparison の成分 `E_c`、finite axis-fold
の非自明な witness を一つに繋ぐことにある。これが通れば、raw の exchange の壊れは
「群の可逆な積と、冪等半束の不可逆な積の不一致」として説明される。

**仮説**。G-115 / G-116 の負例は、可逆な base-change / defect の幾何と、不可逆な意味の
正規化との mixed lax geometry を、1-圏の exactness に押し潰したときに現れる影である。
一次元の地図では描けない semantic geometry の影である。

**定理になる条件**: G-116 の ob.1 と ob.9、G-117 の ob.5 と ob.7。
**置き場所**: G-117 の raw cochain 側の背景と、本ノート。

### 6.2 二軸の研究地図 — 完備化の種類 C と coherence の深さ H

**中身**。Gr 軸(どこまでの底変更を扱えるか)とは別に、独立な軸が二つある。

```text
C: semantic completion(どの圏で意味を表すか)
  C0 そのままの圏
  C1 Karoubi / 冪等像
  C2 observable / configuration の商
  C3 localization(実在すれば)

H: coherence depth(正しい意味論を書くのに何次の proof-relevant data が要るか)
  H0 等式 / 命題の水準の exactness
  H1 射 / comparator の data
  H2 可逆でない比較の 2-cell / modification
  H3 mixed descent / interchange の coherence
  H4+ 実際の残差が証明された場合のみ
```

C の四つは、いまの段階では候補の一覧であって、`C0 → C1 → C2 → C3` という包含や強さの
順序を主張しているのではない。相互の比較は、それぞれを構成してから決める。「Karoubi
completion が要るか」と「2-cell が要るか」は別の問いである。G-116 は C1–C2 と H0–H1、
G-117 は H2、G-118 は H3 を扱う。SFT が入れば時間 `T` が加わり、研究空間は
`Gr × C × H × T` になる。

**定理になる条件**。C の各段は、AAT の instance の上でその完備化を実際に作り、前の段
では成り立たない exactness がその段で成り立つと示せたときに定義になる。H の各段は、
二つの theorem が揃ったときに定義になる。一つは有限の分離 witness による下限(その
次数より低い data では足りない)。もう一つは adequacy(その次数の data で observation と
合成則を回収できる)という上限。下限の候補は、0 次が「同じ局所観測で異なる大域的性質」
(G-107 の locality nonfactorization)、1 次が「指定した coefficient の影では同じだが
comparator descent が異なる」(§4.2 の対)、2 次が「同じ 1-truncation で異なる mixed
coherence」。いま言えるのは、指定した影に対する非因子化と下限までである。
**置き場所**: 本ノートの地図。G-118 の判定後にカードへ写す。

### 6.3 Semantic Equipment

**中身**。AAT には二方向の合成がある。横は doctrine change、base change、refinement、
presentation replacement、migration。縦は package morphism、reading transformation、
canonical normalization、semantic collapse。square には mate、comparison、comparator
descent、transport coherence が住む。generated comparison `β_c = α_c ≫ E_c` は「exact な
canonical square に、不可逆な意味の projector が作用した lax square」と読める。だから
高次化の住処は、単なる bicategory より double category / equipment 型の構造が自然で
ある。新しさは double category を使うことにはない。Atom / Law から生成された実際の
data、diagnostic が選ぶ冪等射、raw / image / observable の exactness、有限の正負
witness、generated route との同定にある。高次圏論は住処であって、成果の本体ではない。

**定理になる条件**。まず double category の data を型付けする。共通の object、横の射と
縦の射、square、横と縦の二つの合成と単位、associator と unitor、whiskering、interchange
と、それらの coherence。そのうえで companion と conjoint を構成する。G-109 の
`coreFiberCompositor` / `coreFiberUnitor` と結合律・単位律の coherence は、横方向一つ分の
素材にすぎない。
**置き場所**: G-118 の住処の候補。Test B の後。

### 6.4 Descent Transporter / Diagnostic Partial Symmetry

**中身**。solution component `c : X ⟶ Y`(G-115 では geometry package の間の
`GeometryTotalHom`)を一つ固定し、両端の qualified automorphism を `b`、`p` とする。
G-115 で comparator が属する端点の群は一般の自己同型群ではなく、base の上で恒等になる
部分群 `CompositeFiberAut X`、`CompositeFiberAut Y` である。comparator descent の中心式は
`b ≫ c = c ≫ p` である。そこで

```text
Γ_c := { (b, p) ∈ CompositeFiberAut X × CompositeFiberAut Y | b ≫ c = c ≫ p }
```

と置く。これは arrow category の対象 `c` の自己同型群、つまり `c` の descent transporter
(isotropy group)である。`c` 自身が同型である必要はない。

既存の宣言は、この構造の候補にあたるものを持っている。`UpperComparatorDescentAt` は
cell ごとの所属条件、`CoefficientTrivialUpperReselectionEndpointIntertwining` は edge
ごとの同じ条件、`coefficientTrivialUpperReselectionEndpointIntertwining_one` と
`CoefficientTrivialUpperReselectionEndpointIntertwining.mul`、
`pairedCoefficientTrivialUpperReselection_one` と
`PairedCoefficientTrivialUpperReselection.mul` は reselection の関係についての単位元と
積の閉性、`upperDecisionSolution_comparatorDescentAt` は定理が作る正の元、
`generatedBaseIdentityPair_not_comparatorDescentAt` は同じ route と component を保った
qualified な非所属の元である。ただし、これらは subtype `Γ_c` そのものについての theorem
ではない。`Γ_c` の packaging、その上の単位元・積・逆元、既存の正負 fixture との対応は、
すべて Test 1 の未証明の項目である。閉じれば、G-115 の負例は、個別には qualified な
comparator の対の積の中で、実際に solution component と整合する対が真部分集合 `Γ_c` を
なすことの有限 witness になる。逆元については、`b ≫ c = c ≫ p` から
`b⁻¹ ≫ c = c ≫ p⁻¹` が出るので、型の transport を除けば新しい仮定は要らない見込みで
ある。この段階で得られるのは、固定した `c` ごとの isotropy 群の族である。`c` を動かして
arrow groupoid にするには、source と target、射、合成、逆射を別に構成する必要があり、
それは Test 1 の次の段にする。

`c` が同型なら `p = c⁻¹ ≫ b ≫ c` なので、`Γ_c` は共役のグラフで、両端の自己同型群と
同型である(conjugation regime。Gr4 を閉じるカードの決定対象)。`c` が同型でなくても
`Γ_c` はある。二つの射影 `Γ_c ⟶ CompositeFiberAut X`、`Γ_c ⟶ CompositeFiberAut Y` は一般に全射でも
単射でもない。
射影の像は、反対側へ運べる端点の対称性。核は、`c` を通すと見えなくなる端点の対称性。
一つの base comparator の上の fiber は、両立する pulled comparator の選択肢の空間で
ある。

§4.2 の対では、取り替えた comparator は coefficient の水準で identity である。だから差
`Δ := p` は、coefficient の影 `κ_c : CompositeFiberAut Y → (coefficient 水準の群)`(群
準同型の候補。domain と codomain は Test 3 で固定する)の核に入る候補でありながら、`(b, p) ∈ Γ_c`、
`(b, 1) ∉ Γ_c` と所属を反転させる。replacement と reselection の後にも class として
well-defined なら、Test B の comparator inertia は「coarse な観測からは消えるが、arrow の
対称性を左右する核の作用」として実体を持つ。`Γ_c` が正規部分群であることや、商群の
存在は仮定しない。

G-116 の projector を加えると、群より partial symmetry が本命になる。cell を一つ固定し、
package の水準で `E_c ≫ E_c = E_c` が立てば `β_c† := E_c ≫ inv α_c` を選べて

```text
β_c ≫ β_c† ≫ β_c = β_c,      β_c† ≫ β_c ≫ β_c† = β_c†
```

が成り立つ。`β_c` はそのままの圏では同型でなくても、選ばれた generalized inverse を持つ
regular morphism である。target 側の projector は `β_c† ≫ β_c = E_c : V_c ⟶ V_c`、
source 側の projector は `β_c ≫ β_c† = α_c ≫ E_c ≫ inv α_c : D_c ⟶ D_c` で、二つは
別物である。G-115 は可逆な端点の対称性と arrow の isotropy `Γ_c` を与える。G-116 は、
冪等射で定義域を切られた diagnostic の partial symmetry を与える。関係する射について
generalized inverse が coherent に選べ、restriction idempotent が合成と可換なら、全体は
inverse category / restriction category 型になる。その場合、一つの対称群があるのでは
ない。projector の半束が partial symmetry の定義域を並べ、各 projector の上に G-115 型の
局所 isotropy 群が載る ordered groupoid が本命である。

**採否テスト**(この順で、落ちたら止まる)。

1. transporter group test: `Γ_c` を subtype として束ね、単位元・積・逆元、正の所属、負の
   非所属を証明する。
2. projection classification test: `c` が同型なら共役のグラフと同一視する。一般の `c` では
   二つの射影の像・核・fiber を定義し、有限の decision fixture で非退化に成り立たせる。
3. comparator inertia test: 差 `Δ` を coefficient の影の核の作用元として束ね、replacement
   と reselection のもとでの well-definedness を決める。失敗は今の inertia model の no-go
   であり、他の高次候補まで否定しない。
4. regular comparison test: `β_c†` と二本の regularity の等式を証明し、target 側の
   projector を G-116 の `E_c` と、source 側の projector を `α_c ≫ E_c ≫ inv α_c` と
   同一視する。
5. inverse-category test: 選んだ inverse の一意性、合成の保存、関係する冪等射の可換性を
   決める。

結果は三段になる。1–5 が通れば diagnostic partial symmetry の inverse / restriction
category。1–4 が通り 5 が落ちれば、transporter groupoid と、regular morphism の族(圏に
なるかは 5 の結果次第)。1–2 だけなら G-115 の descent symmetry groupoid を独立の成果
として持つ。どの枝でも、具体的な theorem か no-go が残る。

**置き場所**: transporter group の最小の packaging と Test B への接続は G-118 の候補
素材。regular comparison は G-116 の theorem から導く後続の補題候補。inverse /
restriction category、ordered groupoid、SHIGURE への接続は本ノート。

### 6.5 semantic coherence height

**中身**。選んだ Law family `L` と observation grammar `Ω` に相対して、その意味と合成則を
完全に書くために持たなければならない proof-relevant data の、最小の次数を測る。height 0
は object / value / 集合の水準の意味論で足りる。height 1 は射 / comparator / provenance の
groupoid が要る。height 2 は射の間の coherence 2-cell が要る。height n は n 次の coherence
が要る。下限は有限の分離 witness で証明する(§6.2 の H 軸の下限と同じ)。G-107 の
locality nonfactorization と §4.2 の対は、同じ「coherence height の下限」の系列として
読める。

**定理になる条件**: 最小の次数を定義するには、各候補次数について、下限の theorem(有限の
分離 witness)と adequacy の theorem(その次数で全 observation と合成則を回収できる)の
両方が要る。いま手元にあるのは下限の候補だけである。少なくとも height 1 の下限(Test B)
が最初の判定になる。さらに、observation grammar `Ω` の定義、coefficient の影への写像、
下限を測る対象の範囲(どの coefficient、どの truncation か)を、Test B とは別に固定する
必要がある。
**置き場所**: 本ノート。G-118 の判定後にプログラムの定義へ。

### 6.6 SHIGURE への含意 — scheme か stack かは定理が決める

**中身**。SHIGURE の素描は、coherent realization functor `Sem_{A,r} : CommAlg → Set`
(または `Groupoid`)を `Sem_{A,r}(R) ≃ Hom(Spec R, M_{A,r})` で表現する。高次の
プログラムを経た形は、truncation の高さを人間が選ばないことである。

```text
Sem_{A,r}^{≤n} : CommAlg → nGroupoid,     Sem_{A,r}^{≤n}(R) ≃ Map(Spec R, 𝔐_{A,r}^{≤n})
```

ここで `n` は §6.5 の coherence height で決める。下限だけでは `n` は決まらず、その高さで
足りることを示す adequacy の theorem が要る。`n = 0` なら scheme / algebraic space、
`n = 1` なら stack、`n = 2` なら 2-stack、それ以上は具体的な残差が証明された場合だけ。
scheme か stack かは設計上の好みではなく、software の意味論が要求する証明の次元の定理に
なる。既存の SHIGURE 素描にある案、「`H⁰` の torsor と gauge 自己同型が中心にあるので
groupoid 値の prestack を先に立て、scheme は trivial-inertia locus / 0-truncation として
取り出す」は、この装置で実際に判定される。

**定理になる条件**: coherence height の決定(下限と adequacy の両方)と、その高さでの
表現可能性。表現可能性は独立の義務で、site / topology の選択と descent の条件が要る。
Test B や height の下限だけからは stack の必要性は出ない。
**置き場所**: n1004 / n1005 の SHIGURE 素描。山頂は動かさない。

### 6.7 SFT への含意 — moduli の上の力学と履歴依存

**中身**。SHIGURE の後は、SFT の開発系 `𝔇` の軌道を semantic moduli の上の path / section
`γ : 𝒯 → 𝔐_sem` として読める。変更は関数とは限らないので、correspondence
`𝔐_before ← Change → 𝔐_after` として扱う。review / CI / governance は、SFT v2 の語彙では
統治された到達集合(閉ループ生成子のもとで挙動空間の上に到達できる配置の集合)を
制限する。SFT の到達集合と計器射影を、SHIGURE の意味空間の上で「大域的に到達できる
配置 ≃ 両立する局所的に到達できる配置」という path descent として読めるか、が問いに
なる。可能性の側は変形空間で扱う。

G-117 の `χ(g) ≫ χ(g⁻¹) = N` が generated orbit でも実際に起きるなら、SFT の側に新しい
現象が出る。raw の変更は打ち消し合っても、どの意味の射影 / 証明の経路を通ったかという
不可逆な痕跡は残る(semantic-analysis hysteresis の候補)。AI agent が大量の変更・
revert・再生成を繰り返す状況では、今のコードだけでなく「どの意味の正規化を通ったか」が
将来の安全性を左右しうる。この履歴依存を SFT の力学として扱う。

**定理になる条件**: 三つ。G-117 の generated orbit の側の witness が正で終わること。AAT
の projector の履歴(どの cell でどの `E_c` を通ったか)を SFT の開発系 `𝔇` の配置または
場の記憶へ渡す写像を定義すること。その写像のもとで、到達集合が経路に依存する(同じ
raw 配置に戻っても統治された到達集合が異なる)という SFT 側の theorem を立てること。
**置き場所**: SFT 本文(`docs/sft/software_field_theory.md`)の第VI・VII・IX部と、SFT の
骨格 note。

### 6.8 CS への一般化の候補 — Relative Higher Abstract Interpretation(仮称)

**中身**。従来の抽象解釈では、具体領域、抽象領域、抽象化写像、semantic transformer を
先に固定する。AAT が加える構造は次である。抽象領域そのものが reading / doctrine / base
change とともに変わる。抽象化は固定された入力ではなく、diagnostic から生成される冪等な
projector である。完全性は一点の性質ではなく、base の上の exactness / jump locus をなす。
抽象化の間の比較は lax natural transformation になりうる。必要な proof relevance の次元を、
有限の分離 witness で測る。coherent な意味論の全体を moduli として表す。

応用先の候補。static analysis(抽象領域の族と exactness locus)。compiler / optimization
(意味を保っても不可逆な pass を、意味の projector を持つ lax square として扱う)。
distributed systems(局所状態の descent と version / schema / protocol の base change の
mixed coherence)。database / view synchronization(lossy な view / migration を冪等射と
し、同じ観測 view を持ちながら update の coherence が異なる comparator を保つ)。AI
coding agents(change、Atom / Law の差分、normalization projector、observable の保存、
comparison class、coherence certificate を、一つの proof-carrying change として合成する)。

generic な Lean library の候補: `RelativeSemanticSystem`、`SplitNormalization`、
`IdempotentExactification`、`ReversibilityProjectionNoGo`、`LaxDiagnosticProjector`、
`ComparatorGroupoid`、`SemanticEquipment`、`Bidescent`。generic な theorem を先に置いて
AAT を例にする順番にはしない。AAT の有限 witness から pattern を抜き出し、generic な
theorem にし、AAT の instance で再び接地する、という往復にする。

**定理になる条件**: 少なくとも G-116 と G-117 の theorem が立つこと。
**置き場所**: outreach / 論文。カードの外。

### 6.9 全体像

一つの theorem に詰め込むものではないが、研究全体の最終像は次である。

> finite / Law-selected / admissible な regime で、generated base-change comparison は
> 可逆な canonical mate と diagnostic が生成する冪等 projector に分解される。raw の
> exactness の壊れは projector の非自明性で分類され、意味の像 / observable の商の上では
> exactness が回復する。defect の合成は projector に strict ではなく lax に作用し、必要な
> coherence の深さは、有限の分離 witness による下限と adequacy の theorem で決まる。その高さの coherent realization functor
> は対応する algebraic n-stack で表現され、SFT の software evolution はその moduli の上の
> dynamics として書かれる。

既存の系列は別々の理論ではなく、同じ universal semantic family の異なる切り口になる。
SAGA は obstruction / repair の section、G-107 / Atlas は diagnostic / jump / observability
の locus、Gr4 系列は相対的な transport / base change、G-116 以降は idempotent
exactification と coherence の深さ、SHIGURE は coherent realization の moduli 全体である。

実装は可逆に変えられる。意味は不可逆に圧縮されうる。AAT はその不可逆性を失敗として
隠さず、2-cell として計算する。SHIGURE はそのすべてを一つの空間として表し、SFT はその
空間を動かす。G-115 の負例は山を壊していたのではない。一次元の地図では描けない山だと、
Lean が教えていた。

## §7 反証ゲート

このプログラムは、どの段でも止まれる。ただし、ゲートで落ちたことを確定した成果と
呼べるのは、反例か no-go の theorem が得られた場合だけである。証明が見つからない、
構成が作れない、というだけでは未証明であり、具体的な blocker を記録して止まる。

| ゲート | 反例 / no-go が立った場合 |
|---|---|
| 1 package の水準の冪等性が立たない | object の水準の split descent で止める。どの等式が成り立たないかを theorem の形で残す |
| 2 正規化が base change に対して自然でない | fiber ごとの projector の理論で閉じる |
| 3 generated orbit が打ち消しを実現しない | 一般の lax law だけを残す |
| 4 comparator の差の class が replacement / reselection のもとで well-defined でない | H3 や stack の必要性を主張しない。今の inertia model の no-go として残す |
| 5 横方向の simplicial 構造が作れない | bisimplicial という語を使わない |
| 6 mixed の残差がすべて消える | higher obstruction ではなく vanishing theorem にする |
| 7 SHIGURE の表現可能性が閉じない | 山頂を弱めず、表現不能性の obstruction を成果にする |
