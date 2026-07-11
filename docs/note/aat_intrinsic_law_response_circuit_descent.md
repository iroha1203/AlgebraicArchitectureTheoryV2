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

とし、allowed first-order ArchitectureOperation の chartwise tangent object を `E_A(W)` と書く。
semantic operation は derivation とは独立に定義し、その後で

```text
semantic first-order ArchitectureOperation ~= allowed derivation
```

を証明する。この比較を定義や structure field に埋め込まない。

derivation `d : Der_k(A_W, B_W)` は `I_W^2` 上で零になるので、canonical に

```text
J_W(d) : I_W/I_W^2 -> B_W
J_W(d)([f]) = d(f)
```

を定める。compatibleなlabeled conormal class `c_(e,W) : I_W/I_W^2` ごとのresponseを

```text
alpha_(e,W)(d) = J_W(d)(c_(e,W))
```

として生成し、operation restrictionとlaw witness restrictionから`alpha_(e,W)`のnaturalityを証明する。
objectwise `Hom_B(I/I^2,B)`にはrestrictionが自動では入らないため、初期主定理は
`J_W`と`alpha_(e,W)`を用いる。`I/I^2`のfinite locally free性とbase changeが証明できた場合に、
internal Hom sheafへのmorphism `J : E_A -> (I/I^2)^vee`としてまとめる。

G-07 から再利用するのは、law-generated `I/I^2`、generated cover、Čech engine、
actual gluing の構成法である。本構想の local repair 差は `I/I^2` ではなく
response kernel に入るため、obstruction class 自体は新しく構成する。

---

## 2. 固定したい主定理

affine chart algebra `A_W`、law ideal `I_W`、lawful chart `Y_W = Spec(A_W/I_W)`を持つ
finite/small atom-generated ringed AAT geometryとgenerated cover `U`を固定する。lawful locus `Y` 上の
conormal sheafを `C = I/I^2` とする。有限 law label 型 `L`、`P subset L`、`t in L \ P`、
restriction-compatibleなlabeled conormal map `c : O_Y^L -> C`を固定する。各fiberでのresponseは

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
`E_A`がfinite locally freeで、protected response map `A_P`がlocally constant rankを持ち、
`ker(A_P)`の形成がresidue-field base changeと可換であるとき、

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
  <-> an actual global normalized ArchitectureOperation exists
```

が成り立つ。

これは「局所 obstruction と大域 obstruction の排他的な二分」ではない。
まず `Q` が局所可解性を判定し、局所可解な場合に `omega_(P,t)` が大域化を判定する
逐次 obstruction theorem である。

---

## 3. 証明依存

```text
L0  normalized repair iff target is outside protected span
 |
 +- L1  support-minimal circuit extraction
 |
 +- L2  loop/nonloop separation

J0  semantic first-order operation definition
 |
 +- J1  semantic operation ~= allowed derivation
      |
      +- J2  derivation -> Hom(I/I^2, B)
           |
           +- J3  restriction naturality
                |
                +- C0  fiber circuit locus = Supp(coker s_t)
                |
                +- D0  local repair differences form a K-valued cocycle
                     |
                     +- D1  choice independence
                          |
                          +- D2  class zero iff actual global operation
                               |
                               +- E0  atom-generated nonzero witness
```

critical path は `J0 -> J1 -> J2 -> J3 -> D0 -> D2 -> E0` である。
有限線形 circuit は先に独立実装できる。Tor、定量不等式、scheme structure は支線とし、
critical path を止めない。

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
derivation_vanishes_on_ideal_sq
derivationToConormalResponse_chartwise
lawResponse_depends_only_on_conormalClass
lawResponse_restriction_natural
semanticFirstOrderOperation_equiv_derivation
```

を構成する。`J_W`、response naturality、semantic equivalenceを入力fieldとして受け取る theorem は
proof checkpoint に留める。

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
   `K` 値classが非零で、global normalized operationが存在しない。

第二例の候補は、3-chart cycle上のupper-triangular shearである。各chartではtarget responseを
`1`に正規化できる一方、hidden operation方向のtransitionが非零Čech classを作る。
completion evidenceにするには、chart algebra、law ideal、operation restriction、actual overlap、
coboundary非所属を同一finite modelで証明する。

両例は同一ambient siteと共通ambient operation schema上で構成する。law idealの変更でlawful-locus
algebraも変わるため、operation sheafを同一視せず、共通schemaから各lawful locusへのcanonicalな
base changeとして比較する。その上でlaw dataだけを変え、local circuit型とpure descent型が
分かれるwitness pairを作る。これはAAT入力がobstructionの種類を変えることを示す。

---

## 7. 新規性の判定

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

publication-levelの新規性判定前に、hyperplane arrangement、Orlik–Terao、matroid syzygy、
deformation complex、cellular sheaf、matroid bundle / degeneracy locusを監査する。

---

## 8. draft からの昇格条件

G-08をactiveなtarget-theoremへ昇格する前に、次を固定する。

1. `L`、`P`、`t in L \ P`とcompatible labeled conormal mapの型。
2. G-07のsemantic first-order representationの実体と、本構想のoperation liftとのcomparison。
3. semantic operationのzero、加法、scalar、restriction、sheaf conditionと、allowed derivationとの同値statement。
4. chartwise `J_W`と`alpha_(e,W)`のrestriction naturalityを入力fieldにしない構成ルート。
5. `Y_W = Spec(A_W/I_W)`、stalk、residue field、supportとgenerated AAT coverのcomparison。
6. `A_P`のconstant rankとfiber kernel base-changeを支える仮定またはconstruction。
7. fiberwise repair可能性からselected chartwise repairを得るroute、またはexplicit chartwise lift仮定。
8. 同一ambient site / operation schemaから各lawful locusへbase changeしたwitness pairのLean prototype。
9. cover、`P,t`、operation、conormal、responseを含むpresentation transport statementと、
   文献監査後も残る新規性claim。

G-03は一般generated nerveを扱う並行研究、G-04はideal-power higher stages、nonabelian、higher、
stacky、universalityを扱う。G-08は両者を再包装せず、operation-response geometryと
local circuit / global descentの逐次obstructionを担当する。

Lean status: 本構想はdraftであり、対応するtarget theoremは未証明である。
