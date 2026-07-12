# Intrinsic law-response circuit descent — 構想と証明ルート

G-07 の Law-Generated Conormal First-Order Descent Theorem の後に狙う
**Intrinsic Law-Response Circuit–Descent Theorem** の構想ノート。
draft GOAL は
[G-aat-quality-surface-08](../../research/goals/G-aat-quality-surface-08.md)とする。

G-07 は law witness から `I/I^2` と first-order section lift の connecting class を生成する。
本構想は、そこからさらに allowed first-order ArchitectureOperation の law response を生成し、
局所 repair 不能性の support-minimal certificate と、局所 repair の大域化 obstruction を
同じ operation-response geometry から構成する。

---

## 1. G-07 から引き継ぐものと新しく作るもの

G-07 の固定 target は

```text
0 -> I/I^2 -> O/I^2 -> O/I -> 0
partial_U(s) = 0
  <-> s has an actual global first-order section lift
```

である。ここで分類されるのは `O/I^2 -> O/I` に沿う section lift である。

本構想で必要な first-order operation は別の対象である。chart `W` のlawful-locus algebraを

```text
B_W = A_W/I_W
```

とする。quotient mapを`q_W : A_W -> B_W`と書く。semantic first-order operationは、
law quotient前のambient algebra`A_0`上にあるtyped presentationから生成する。

```text
Op                 finite primitive operation labels
opSchema           Op -> Formal.Arch.ArchitectureOperation
rho_0              Op -> Der_k(A_0, A_0)
```

generated Zariski chart`W`へ`rho_0(op)`をlocalizeした`rho_W(op)`とquotient mapを合成し、

```text
d_(I,W)(op) = q_W o rho_W(op) : Der_k(A_W, B_W)
```

を作る。semantic first-order operation presentationは、このquotient-valued derivationに対応する
square-zero algebra lift

```text
tilde q_W : A_W -> B_W ⋉ B_W
fst o tilde q_W = q_W
```

として定義する。これは既存`ArchitectureOperation`のtyped first-order realizationであり、
lawごとに無関係なlift familyを入力するものではない。その後でmathlibの
`derivationToSquareZeroEquivLift`へ接続し、

```text
semantic first-order ArchitectureOperation ~= allowed derivation
```

を証明する。`E_A`はfree module sheaf`O_Y^Op`からambient-to-quotient derivation sheafへのmapの
sheaf-category imageとして定義する。初期targetではgenerated chartをtyped Zariski localizationに
限定し、affine quasi-coherent imageとlocalization comparisonからrestrictionとsheaf conditionを
構成する。objectwise spanをsheafと呼ばない。既存`Formal/Arch/Operation/ArchitectureOperation`は
operation kindとwitness transportを与え、`rho_0`がそのfirst-order algebraic realizationを与える。

異なるlaw ideal`I_0`と`I'_0`の間にquotient ring mapがあるとは仮定しない。共通なのは
`A_0`、`Op`、`opSchema`、`rho_0`であり、各quotient mapとの合成から別々の
ambient-to-quotient derivation sheafを作る。この意味でwitness pairは同一ambient operation
presentationから生成される。`rho_W(op)(I_W) <= I_W`は入力条件にせず、対応するconormal responseが
零であること、すなわちoperationがlawful locusに接することと同値なkernel theoremとして証明する。

derivation `d : Der_k(A_W, B_W)` は `I_W^2` 上で零になるので、canonical に

```text
J_W(d) : I_W/I_W^2 -> B_W
J_W(d)([f]) = d(f)
```

を定める。required generator label`e = (lawIndex, atom)`に対応する
`violationWitness lawIndex atom`を`Ideal.toCotangent`へ送って生成した
labeled conormal class `c_(e,W) : I_W/I_W^2` ごとのresponseを

```text
alpha_(e,W)(d) = J_W(d)(c_(e,W))
```

として生成し、operation restrictionとlaw witness restrictionから`alpha_(e,W)`のnaturalityを証明する。
label型はlawごとに任意の代表generatorを一つ選ぶ型ではない。既存law idealがrequired lawの
atom-indexed`violationWitness`全体から生成されることを保持するため、required`(lawIndex, atom)`を使う。
objectwise `Hom_B(I/I^2,B)`にはrestrictionが自動では入らないため、初期主定理は
`J_W`と`alpha_(e,W)`を用いる。`I/I^2`のfinite locally free性とbase changeが証明できた場合に、
internal Hom sheafへのmorphism `J : E_A -> (I/I^2)^vee`としてまとめる。

G-07 から再利用するのは、law-generated `I/I^2`、generated cover、Čech engine、
actual gluing の構成法である。本構想の local repair 差は `I/I^2` ではなく
response kernel に入るため、obstruction class 自体は新しく構成する。

### 1.1 G-08でAATが獲得する能力

G-08はAATをlawful locusの静的幾何から、operationがlawへ与える一次応答の幾何へ進める。

1. `E_A`により、選択されたArchitectureOperationのtangent directionをsheafとして持つ。
2. `J : E_A -> Hom(I/I^2, O_Y)`により、law idealをoperation responseのcovectorへ変換する。
3. support-minimal circuitにより、repair不能性を最小law support付きcertificateとして返す。
4. two-term object`K_P -> O_Y`により、fiberwise local failure`Q = coker(s_t)`と、
   local repair torsorのglobalization failure`H^1(K)`を同じresponse mapから読む。
5. このtwo-stage obstructionは、G-04のhigher / nonabelian / stacky repair towerと、
   operation deformation complexへ進むdegree-zero / degree-oneの土台になる。
6. effective finite measurement regimeでは同じmapをfiber matrixと有限Čech complexへ落とし、
   ArchSigが検証可能なcertificateとして扱える。

---

## 2. 固定したい主定理

affine chart algebra `A_W`、law ideal `I_W`、lawful chart `Y_W = Spec(A_W/I_W)`を持つ
finite atom-generated locally affine Zariski AAT geometryとgenerated cover `U`を固定する。selected chartと
overlapはaffineとするが、global ringed AAT objectを単一`Spec Γ(Y,O_Y)`と同一視しない。lawful locus`Y`上の
conormal sheafを `C = I/I^2` とする。required`(lawIndex, atom)`からなるfinite generator label型`L`、
`P subset L`、`t in L \ P`を固定し、対応する`violationWitness`とrestrictionからlabeled conormal map
`c : O_Y^L -> C`を構成する。`obstructionIdeal`の生成定義から`c`の像が`C`を生成することも証明する。
各fiberでのresponseは

```text
alpha_e(x) = evaluation at c_e(x) after J_x
```

とする。protected response map と target mapを

```text
A_P : E_A -> O^P
K_P = ker A_P
s_t : K_P -> O
K = ker s_t
Q = coker s_t
```

と置く。

主定理は次の二段階で述べる。

### 2.1 局所 circuit theorem

各 geometric fiber `x` で、law responses `alpha_e(x)` が表現するmatroidを `M_x` とする。
`E_A`がfinite locally freeで、protected response map `A_P`がlocally split constant rankを持つとする。
この仮定から`ker(A_P)`のfinite locally free性とresidue-field base change可換性を証明した上で、

```text
normalized repair exists at x
  <-> alpha_t(x) is not in span(alpha_P(x))
  <-> t is not in closure_Mx(P)
```

が成り立つ。

repair が存在しない場合は

```text
t in C subset P union {t}
```

を満たす support-minimal linear circuit `C` が存在する。`alpha_t(x) = 0` の場合は
`{t}` を loop circuit として別に扱う。

さらに

```text
D_(P,t) = Supp(Q)
```

の underlying set は fiber circuit locus と一致する。

### 2.2 global descent theorem

fiberwise repair可能性だけから固定cover上のsectionを無条件には得ない。generated coverを
必要に応じて細分したうえで、各 chart 上に normalized repair `v_i` が存在するとする。
overlap 上の差

```text
g_ij = v_j|U_ij - v_i|U_ij
```

は `K` 値 Čech 1-cocycle を定める。そのclassを

```text
omega_(P,t) in CechH1(U, K)
```

と書くと、local repair の選択に依存せず、

```text
omega_(P,t) = 0
  <-> a global normalized section of E_A exists
```

が成り立つ。

これは「局所 obstruction と大域 obstruction の排他的な二分」ではない。
まず `Q` が局所可解性を判定し、局所可解な場合に `omega_(P,t)` が大域化を判定する
逐次 obstruction theorem である。

---

## 3. 実装フェーズと証明依存

Lean prototypeはactive化前提にせず、G-08の最初のproof stageとして実装する。

1. **Phase 0 — Semantic Operation Foundation**: `BC0`でstatement compatibility、reuse / replacement map、
   API surfaceを固定する。typed`ArchitectureOperation` presentation、typed localization geometry、
   ambient derivationのcanonical localization、`q_W o rho_W`、square-zero adapter、derivation coefficient sheaf、
   operation image sheaf、conormal response、full response kernel theorem、labeled conormal generation、
   G-08用typed Boolean-circle ring layer上の非零responseを構成する。
2. **Phase 1 — Local Circuit and Support**: finite repair、minimal circuit、kernel base-change、support比較。
3. **Phase 2 — Response-Kernel Descent**: `R = image(s_t)`、short exact image sequence、distinguished image section、
   local repair cocycle、choice independence、零classとglobal sectionの同値。
4. **Phase 3 — Witness and Naturality**: `E-pre` witness対、`N0` presentation naturality、unit rescaling transport。
5. **Phase 4 — Effective Measurement Shadow**: full complexからfinite measurement complexへのchain map、
   finite checker、soundness、`E-pre`から`E-cert`への接続。
6. **Phase 5 — Integration and Final Gate**: main package、台帳同期、axiom audit、独立最終査読。

Phase 0は見積り上も独立した実装段である。単一chartのAPI接続だけで終了せず、G-08用typed ring layerを
持つBoolean-circleで非零conormal responseが発火し、Phase 1のcircuit theoremへ渡せることを終了条件とする。

### 3.1 Base Camp 0 — statement compatibility gate

BC0はPhase 0内の最初のgateであり、Lean本体へ進む前に次を固定する。

1. **global geometry**: selected chartとoverlapはaffine`Spec`、restrictionはtyped Zariski localizationとする。
   global object自体はchartsから生成されたlocally affine ringed AAT spaceであり、単一affine`Spec`とは
   同一視しない。global affinenessを要求してpure-descent classを消す設計には進まない。
2. **operation presentation**: 既存`ArchitectureOperation`はkind、source / target、proof obligation、
   witness transportを保持する。ring / derivation realizationはcore structureへ追加せず、外側のtyped
   presentationと`RealizesFirstOrder` theoremで接続する。
3. **reuse / replacement**: G-07のgenerated cover combinatorics、conormal、Čech engine、actual gluingは
   再利用する。既存Boolean-circleのcoefficient restrictionは`killEps`を使いtyped localizationではないため、
   G-08ではsite combinatoricsだけを再利用し、principal-localization ring layerを新設する。
4. **API probe**: Kähler differentialのlocalization base change、`LinearMap.compDer`、
   `TrivSqZeroExt`のsquare-zero ideal adapter、`derivationToSquareZeroEquivLift`、`Ideal.Cotangent`、
   sheaf image、module-action factorizationの型をsingle-file probeで固定する。

BC0のdecision、API probe結果、reuse / replacement map、current blocker、次checkpointは
`research/reports/G-aat-quality-surface-08.md`へ記録する。`.tmp/G08ApiProbe.lean`は統合入口へimportしない。

```text
L0  finite linear repair / support-minimal circuit / loop separation

BC0 statement / API compatibility
 |
 +- J0  typed ArchitectureOperation presentation / RealizesFirstOrder
      |
      +- J1a typed affine-localization geometry
           |
           +- J1b ambient derivation localization
                |
                +- J2  quotient-valued derivation / square-zero adapter
                     |
                     +- J3a derivation coefficient sheaf
                          |
                          +- J3b operation image sheaf / module action
                               |
                               +- J4  conormal Jacobian / labeled response / restriction
                                    |
                                    +- J5a full conormal-response kernel
                                         |
                                         +- J5b labeled conormal generation
                                              |
                                              +- J6 typed Boolean-circle nonzero response

L0 + J6
 |
 +- C0  fiber circuit locus = Supp(coker s_t)
      |
      +- D0  image sequence / distinguished image section
           |
           +- D1  K-valued cocycle / choice independence
                |
                +- D2  class zero iff global normalized E_A-section
                     |
                     +----- E-pre witness pair ----- N0 naturality
                     |
                     +----- M0 generic finite checker
                                      |
                               E-cert certified witness pair
                                      |
                                Summit / MainTheorem
```

proof dependencyと実装gateは区別する。有限線形`L0`は独立に先行できるが、Phase 1は
`BC0 -> J0 -> J1a -> J1b -> J2 -> J3a -> J3b -> J4 -> J5a -> J5b -> J6`を
完了してから開始する。Tor、定量不等式、
scheme structureは支線とし、critical pathを止めない。

### 3.2 checkpoint discipline

一つのPRは原則一つの矢印、多くても二つの隣接checkpointを担当する。各checkpointはtracking Issueへ
`base_sha`、new declarations、generated inputs、proved outputs、remaining premises、negative tests、
focused check、axiom / placeholder audit、next edge、blockerを記録する。J稜線とL0は並行可能だが、
J6を迂回してC0へ入らない。

---

## 4. Lean で最初に固定する面

### 4.1 有限線形核

最初は matroid API を主 statement にせず、`LinearMap` と `Submodule.span` で

```text
exists_normalizedRepair_iff_target_not_mem_span
target_vanishes_on_protectedKernel_iff_mem_span
exists_supportMinimalCircuit_of_target_mem_span
target_loop_is_singletonCircuit
```

を証明する。その後で `Matroid.IsCircuit` と closure へ接続する。

### 4.2 intrinsic Jacobian

```text
semanticFirstOrderOperation_equiv_derivation
derivation_vanishes_on_ideal_sq
derivationToConormalResponse_chartwise
lawResponse_depends_only_on_conormalClass
lawResponse_restriction_natural
ambientIdealPreserving_iff_conormalResponse_eq_zero
labeledConormal_span_top
allLabeledResponses_zero_iff_conormalResponse_eq_zero
```

を構成する。semantic operation比較はmathlib
`derivationToSquareZeroEquivLift`を再包装せず、AAT chart quotientとsquare-zero extensionを
このAPIへ接続する。`Ideal.Cotangent`、`Ideal.toCotangent`、
`KaehlerDifferential.linearMapEquivDerivation`をcomparison先に使う。
`J_W`、response naturality、semantic equivalenceを入力fieldとして受け取る theorem は
proof checkpoint に留める。

kernel theoremは二段に分ける。まずfull conormal responseについて

```text
rho_W(I_W) <= I_W <-> J_W(q_W o rho_W) = 0
```

を証明する。その後でrequired`(lawIndex, atom)` generator labelsのclassが、既存`obstructionIdeal`の
required law / atom-indexed生成定義から`I_W/I_W^2`を生成することを証明し、
全labeled responseの零性とfull responseの零性を比較する。generator spanを証明できない場合、
`forall e, alpha_e(d) = 0`をideal-preserving方向と同一視しない。

### 4.3 cover-relative descent

```text
localRepairDifference_mem_responseKernel
localRepairDifference_cocycle
localRepairClass_choiceIndependent
localRepairClass_eq_zero_iff_exists_globalRepair
```

を既存の cover-relative additive Čech quotient と actual sheaf descent へ接続する。
generic differentialやeffectivityを受け取るだけでなく、generated coverとrestrictionから
対象instanceを構成する。

descent engineへ渡す第三項は`Q = coker(s_t)`ではなく`R = image(s_t)`とする。

```text
0 -> K -> K_P -> R -> 0
R -> O_Y -> Q -> 0
```

を生成し、selected chartwise repairsとsheaf localityから`1`のdistinguished sectionを`R`上に構成する。
`Q`はlocal repair failure、short exact image sequenceの`K`はlocal repairsのgluingを読む。image membership、
short exactness、distinguished sectionをstructure fieldとして供給しない。

### 4.4 two-stage repair object

`K_P = ker(A_P)`と`s_t : K_P -> O_Y`からtwo-term object

```text
R_(P,t) = [K_P -> O_Y]
```

を作る。fiberwise`coker(s_t)`はnormalized repairの局所failureを、局所repairが存在する面では
`R = image(s_t)`上のdistinguished sectionに対する`ker(s_t) = K`値Čech classが大域化failureを読む。
初期completionでは一般hypercohomologyを
導入せず、local coker、repair torsor、`H^1(K)`、actual gluingを明示定理として接続する。
この低次packageを後続のhypercohomology / derived deformation complexへのcomparison sourceにする。

---

## 5. Circuit–Tor 支線

fiber `x` で

```text
S_x = Sym(E_A(x)^*)
I_P = (alpha_p(x) | p in P)
J_t = (alpha_t(x))
```

と置く。`alpha_t(x) != 0` の nonloop locus では、degree-one linear partについて

```text
t in closure_Mx(P)
  <-> Tor_1^Sx(S_x/I_P, S_x/J_t)_1 is nonzero
```

を狙う。

現行 `LawConflict` / Mathlib Tor surface はinternal gradingを保持しない。そのため初期Leanでは

1. linear ideal intersection の degree-one 部分、
2. nonloop span membership から ungraded `Tor_1` nonzero への含意、
3. response polynomial ring 上のTorとPart V `LawConflict`のcomparison、

を分離する。loop circuitをTorで検出したとは主張しない。

実数または複素数上で、`t`を含むnonloop minimal circuit relation

```text
c_t alpha_t + sum_p c_p alpha_p = 0
c_t != 0 and sum_p |c_p| > 0
```

から得る no-free-repair inequality は定量的corollaryとし、主定理には含めない。

---

## 6. 非零 witness

完成には、同一のatom-generated siteとoperation semanticsから少なくとも次の二例を作る。

1. **local circuit witness**: target response が protected response のspanに入り、
   support-minimal circuitがrepair不存在を証明する。
2. **pure descent witness**: 全fiberでtargetはprotected span外で、各selected chartに
   explicit normalized repairが存在するが、local repair差の
   `K` 値classが非零で、global normalized `E_A`-sectionが存在しない。

推奨候補はpunctured affine plane型の3-chart principal-localization modelである。field`k`上で

```text
A_0 = k[x,y,p,t,u,v]
rho_1 = partial_u + x partial_t
rho_2 = partial_v + y partial_t
X = D(x) union D(y)
U_0 = D(x), U_1 = D(y), U_2 = D(x+y)
```

と置く。`U_2`は冗長だがdistinctな第三chartであり、全chartとoverlapをprincipal localizationとして
Boolean-circleの3-chart combinatoricsへ載せられる。既存G-07の`killEps` restrictionは使わない。

pure-descent lawでは`I_desc = (p,t)`、protected classを`[p]`、target classを`[t]`とする。

```text
E_A ~= O_X^2
alpha_p = (0,0)
alpha_t = (x,y)
v_x = (x^-1,0)
v_y = (0,y^-1)
v_(x+y) = ((x+y)^-1,(x+y)^-1)
```

各chartではnormalized repairが存在する。`K = ker[x y]`を`(-y,x)`で読み、二chart subcover上の差を
`(xy)^-1(-y,x)`として表す。exact Laurent monomial`x^-1 y^-1 u^0 v^0`の係数を取る`k`値functionalが
coboundary image上で零、対象cocycle上で`1`となることと、三chart cocycleから二chart subcoverへの
Čech cochain restrictionを証明して非零classを得る。

local-circuit lawでは同じambient dataに対して`I_circ = (t,p^2)`、protected generatorを`t`、
target generatorを`t+p^2`とする。両responseは`(x,y)`となり、`X`上でnonloop 2-circuitを作る。
両例はambient algebra、operation labels、`ArchitectureOperation` presentation、ambient derivationsを共有し、
law idealとquotient mapだけを変える。これはAAT入力がlocal circuit型とpure descent型を分けることを示す。

この模型はcandidateであり、completion evidenceにするにはchart algebra、law ideal、typed restriction、
operation image sheaf、actual overlap、labeled conormal generation、coboundary image非所属を同一Lean packageへ
接続する。

---

## 7. 文献・既存理論監査と新規性

一次資料との比較結果は次の通り。

- [Stacks 04BP](https://stacks.math.columbia.edu/tag/04BP)はsquare-zero extensionのsection差が
  derivationで記述されることを与える。semantic operation–derivation対応そのものは既知である。
- [Stacks 04EA](https://stacks.math.columbia.edu/tag/04EA)と
  [04EE](https://stacks.math.columbia.edu/tag/04EE)はconormal moduleとuniversal first-order
  thickening、localization compatibilityを与える。`I/I^2`とchart restriction自体は既知である。
- [Stacks 01UM](https://stacks.math.columbia.edu/tag/01UM)と
  [04BJ](https://stacks.math.columbia.edu/tag/04BJ)はscheme / ringed-topos上のdifferentialsと
  derivation sheafを与える。operation sheafを持つだけでは新規性にならない。
- [Stacks 07Z6](https://stacks.math.columbia.edu/tag/07Z6)と
  [07ZD](https://stacks.math.columbia.edu/tag/07ZD)はFitting ideal、finite locally free性、
  base changeを与える。coker supportをdegeneracy locusとして読む骨格は既知である。
- [Dinh–Mohammadi](https://arxiv.org/abs/1502.01005)などのOrlik–Terao研究は
  hyperplane arrangementのrelation spaceとminimal dependenceを扱う。circuit抽出だけでは足りない。
- [Curry](https://arxiv.org/abs/1303.3255)はcomputable cellular sheaf cohomologyとglobal sectionを
  扱う。有限sheafのlocal-to-global obstructionだけでは足りない。

個別には次は既知の数学的骨格である。

- matroid closure と minimal circuit
- `Tor_1(S/I,S/J) ~= (I intersect J)/IJ`
- kernel torsor と `H^1` obstruction
- two-term complex と低次hypercohomology
- determinantal locus と Fitting ideal

したがって、これらを並べるだけでは新規性の根拠にしない。本構想の新規性候補は、

1. Atom / law / ArchitectureOperationから `E_A`、chartwise `J_W`、compatible response mapsを生成すること。
2. cover、`P,t`、operation sheaf、conormal sections、response squareを保つlabeled同型に対する
   naturalityを証明すること。
3. fiber circuit、response Tor、descent classを同じgenerated mapから得ること。
4. local circuit型とpure descent型を分離するatom-generated witnessを持つこと。

である。arbitrary generator changeに対するcircuit不変性は主張しない。unit rescalingについては
circuit support、local existence、degeneracy locusと、normalized repair torsor / classのtransportを
分け、target labelのrescalingではnormalizationのtransportも明示する。より強い表示不変性は
文献監査と反例探索後に判断する。

publication-levelの最終判定では、上記に加えてdeformation complex、matroid bundle、
operation-valued cellular sheafの直接的な先行定理をstatement単位で比較する。

---

## 8. Finite measurement shadow

一般の数学certificateとArchSig向けのeffective finite measurement certificateを分ける。full section / Čech
module自体の有限次元性は要求しない。computable coefficient field、selected geometric fiber evaluation、
finite measurement complex、full complexからのchain map、boundary matrixを持つmeasurement regimeに対して
finite certificateを生成する。

```text
fiber response matrix M_x[e,r] = alpha_e(x)(v_r)
local success         normalized repair vector over kappa(x)
local failure         support-minimal circuit coefficients over kappa(x)
globalization input   finite K-valued overlap cocycle coordinates
globalization failure dual functional vanishing on im(delta) but not on the cocycle
provenance             Atom, law, operation, chart, point, cover, bases, transport
```

Lean側ではfull complexからfinite measurement complexへのchain-map law、数学certificateからeffective
certificateへのsoundness、basis変更とlabeled presentation同型に対するtransport、dual witnessによる
coboundary image非所属の検証を証明し、matrix rankだけを不変量と呼ばない。
ArchSig側はArchMap、LawPolicy、MeasurementProfileが選んだfiber evaluation、有限basis、cover、
cochain modelからこのshadowを計算し、repair vector / circuit / cocycle witnessをanalysis packetへ載せられる。
tooling実装は別Issueで扱い、G-08 completionは有限shadowがAAT theoremの正しいcertificateであることを
Leanで証明するところまでとする。

punctured affine candidateではexact Laurent monomial`x^-1 y^-1 u^0 v^0`の係数を取る`k`値functionalを使い、full Čech complexから
`C^0_meas = 0`、`C^1_meas = k`、boundary matrix`0`の一次元measurement complexへ送る。functionalが
full coboundary imageを消し、対象cocycleを`1`へ送ることがcertificate provenanceになる。

---

## 9. active化契約とPhase 0停止規則

G-08のactive化にLean prototypeの完成を要求しない。active化前に固定するのはtarget statement、
material premise ledger、anti-weakening rule、文献監査、Phase 0–5の責務、失敗時の扱いである。

Phase 0では次をLean上で固定する。

1. BC0でlocally affine interpretation、G-07 reuse / replacement map、API probeをreportへ固定する。
2. required`(lawIndex, atom)` generator label型`L`、`P`、`t in L \ P`と対応する`violationWitness`から
   labeled conormal mapを生成し、`obstructionIdeal`の生成定義からspan theoremを導く型。
3. G-07のsection-lift representationをoperation liftと同一視せず、G-07から再利用する`I/I^2`、
   cover、Čech engine、actual gluingのtyped import map。
4. selected`ArchitectureOperation`のstate / witness parametersとambient derivation realizationを結ぶ
   typed presentation、typed localization geometry、ambient derivation localization、quotient-valued composition、
   square-zero adapter、derivation coefficient sheaf、operation image sheafのstatement。
5. chartwise `J_W`と`alpha_(e,W)`のrestriction naturalityを入力fieldにしない構成ルート、full response kernel、
   required label classesのspan theorem。
6. `Y_W = Spec(A_W/I_W)`、stalk、residue field、supportとgenerated AAT coverのcomparison。
7. G-08用principal-localization ring layerを持つBoolean-circle finite modelで非零conormal responseを構成し、
   Phase 1へ渡せること。

locally affine interpretation、typed presentation、typed localization geometry、operation image sheaf、full response
kernel、labeled conormal generationのいずれかが構成不能、restriction naturalityが得られない、またはG-08用
Boolean-circle responseが零へ退化する場合はPhase 1へ進まない。target statementの改訂案を人間へ提示し、
再査読する。

G-03は一般generated nerveを扱う並行研究、G-04はideal-power higher stages、nonabelian、higher、
stacky、universalityを扱う。G-08は両者を再包装せず、operation-response geometryと
local circuit / global descentの逐次obstructionを担当する。

Lean status: G-08はactiveなtarget-theoremであり、対応するtarget theoremは未証明である。
runtime proof stateはtracking Issue [#3282](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/3282)を正本とする。
