# Conormal first-order descent — target と証明ルート

SAGA 定理([証明記録](aat_saga_theorem_proof_record.md))の次に証明した
**Law-Generated Conormal First-Order Descent Theorem** の設計ノート。
固定 statement と完了条件の正本は
[research/goals/G-aat-quality-surface-07.md](../../research/goals/G-aat-quality-surface-07.md)の`G-aat-quality-surface-07`であり、
本ノートは数学的根拠と証明順序を記録する。完了証拠は
[research/reports/G-aat-quality-surface-07.md](../../research/reports/G-aat-quality-surface-07.md)に置く。

参照:

- [第X部 Semantic Repair / Descent / SAGA](../aat/algebraic_geometric_theory/part_10_semantic_repair_descent_saga.md)
  (定理3.4 / 3.5 / 4.8 / 7.2 / 7.3 / 8.1–8.5)
- [第IV部 Obstruction / Cohomology](../aat/algebraic_geometric_theory/part_4_obstruction_cohomology.md)
  (`ConDef_U`)
- [G-02設計ノート](aat_semantic_repair_gluing_complex.md)

---

## 1. 固定 target

選択されたAAT site、base `W`、cover `U = {U_i -> W}`と、
law witnessから生成されるshort exact sequence

```text
0 -> ConDef -> Q_1 -> Q_0 -> 0
Q_0 = O/I
Q_1 = O/I^2
ConDef ~= I/I^2
```

を固定する。`s : Q_0(W)`はlawful base sectionであり、各chart上で同じ`s`へのlocal liftを持つとする。
local liftsのoverlap差が定めるconnecting classを

```text
partial_U(s) in CechH1(U, ConDef)
```

と書く。主定理は

```text
partial_U(s) = 0
  <-> exists S_1 : Q_1(W), map(S_1) = s
```

である。加えて次を同じtheorem packageに含める。

1. overlap差はČech 1-cocycleを定める。
2. local lift familyの変更はcoboundaryだけrepresentativeを変え、`partial_U(s)`はwell-defined。
3. global lift fiberは非空なら`ConDef(W) ~= H^0(W, ConDef)`のtorsor。
4. `CechH1(U, ConDef) = 0`なら、このcover上の局所可解な全first-order lifting problemが大域化する。

主対象は群全体の消滅ではなく、sectionごとのclassである。また`I/I^2`が直接分類するのは
`O/I^2 -> O/I`に沿うfirst-order liftであり、full semantic repairは後続のrepresentationと
ideal-power towerを経て扱う。

---

## 2. SAGA後に残った数学

| 段階 | 証明済みの到達点 | G-07に残る仕事 |
| --- | --- | --- |
| G-02 | complete-support finite class上のdescent同値 | class membershipに依存しないgenerated construction |
| G-05 | selected boundary-relation additive package上のtrue-sheaf同値 | law-generated coefficientとlifting problemへの接続 |
| G-06 / SAGA | atom-generated site上のcover-relative Čech `H^1` grounding | law-sensitiveなfirst-order classとactual liftの分類 |

第X部定理8.1 / 8.2は、現行`O/I`係数ではlaw satisfactionがdegree zeroの消滅に現れ、
grounded routeの非自明な`H^1`内容がcover geometryから来ることを固定した。
したがってG-07は既存residualを貼り直すのではなく、law idealのfirst-order thickeningから
新しいlifting problemを生成する。

研究上の差分は一般的なconnecting homomorphismそのものではない。Atom / law witnessから
ideal、係数、lawful reading、local lift torsorを生成し、そのclassがactual global liftを
分類することに置く。

### 必須の4構成

1. **Lawful reading representation**
   law satisfactionから`Q_0 = O/I`上の、零とは限らないsectionを構成する。
   defect reading `interpret = 0`をbase sectionにすると零liftで自明化する。

2. **Law-generated sheaf列**
   witness idealからideal sheaf `I`、`Q_0`、`Q_1`、kernel sheafを生成し、
   restriction compatibility、short exactness、`ker(Q_1 -> Q_0) ~= I/I^2`を証明する。
   objectwise `Ideal.Cotangent`だけではcoefficient sheafにならない。

3. **Connecting classとeffectivity**
   local lift差からchoice-independentなclassを構成し、class zeroからlocal liftsを補正して
   actual global sectionを作る。effectivityをcertificate fieldとして受け取らない。

4. **Semantic representation**
   selected Atom / law / semantic dataから
   ```text
   SemanticFirstOrderRepair(s) ~= Lift_(Q_1 -> Q_0)(s)
   ```
   を証明する。`Hom(I/I^2,M)`やderivation sheafが正しいと判明した場合は、
   `ConDef`直接作用を完了扱いせずtarget改訂を判断する。

---

## 3. 証明ルート

### D0 — generic additive lift descent

AAT固有語彙を外し、additive sheafのshort exact sequence

```text
0 -> N -> E -> Q -> 0
```

に対するengineを先に証明する。候補APIは次の通り。

```text
ShortExactLiftProblem
LocalLiftDifference
CechConnectingCocycle
connectingClass
connectingClass_zero_iff_exists_globalLift
globalLiftFiber_addTorsor
```

証明は六段で閉じる。

1. `ker(E -> Q) ~= N`を構成する。
2. 同じbase sectionのlift fiberに`N(U)`がfree / transitiveに作用する。
3. `omega_ij = s_j|U_ij - s_i|U_ij`をkernel同型で`N(U_ij)`へ戻し、
   triple overlapのtelescopingから`delta^1 omega = 0`を示す。
4. `s_i' = s_i + a_i`なら`omega' - omega = delta^0 a`を示す。
5. global liftがあればlocal liftとの差がprimitiveを与え、classは零。
6. class zeroならlocal liftsを0-cochainで補正し、互換族をsheaf descentへ渡してglobal sectionを作る。

generic engineはadditive exactnessだけを使う。square-zeroという強さは
`O/I^(n+1) -> O/I^n`へのinstantiate側に置く。

### D1 — law-generated ideal geometry

本体の

- site が選ぶ `ArchitecturalEquationSystem` (`S.equationSystem`)
- 同じ site equation system を読む
  `SemanticRepair.LawEquationWitnessIdealGeometryBody`

から次を生成する。

```text
law witness sections
  -> ideal sheaf I
  -> ideal powers I^n
  -> Q_n = O/I^(n+1)
  -> ker(Q_n -> Q_(n-1))
  -> I^n/I^(n+1)
```

証明義務はideal-power restriction、quotient mapのnaturality、kernel comparison、
quotient / kernel sheaf condition、cover-relative Čech coefficient realizationである。
Research側の`SemanticLawEquationWitnessIdealGeometry`は先行成果として参照し、
本体APIへ必要な構成を蒸留する。

### D2 — conormal first-order theorem

D0をD1の`n = 1`へinstantiateし、既存finite-poset generated cover上で

```text
partial_U(s) = 0 in CechH1(U, ConDef)
  <-> GlobalFirstOrderLawLift(s)
```

を証明する。右辺は`Q_1(W)`のactual sectionと、その像が`s`である等式を持つ。
sufficiencyでは補正済みlocal familyを既存`AATDescent`へ渡す。

初回証明はG-03の一般relation-atom nerveを待たない。一方、zero section、singleton site、
identity comparisonだけで発火するinstanceはnonvacuityの証拠にしない。

### D3 — semantic representation

D2と`SemanticFirstOrderRepairEquiv`を合成し、semantic first-order repairの存在判定を得る。

### 後続 — ideal-power filtered descent

G-07完了後、D0を

```text
0 -> I^n/I^(n+1) -> O/I^(n+1) -> O/I^n -> 0
```

へ反復適用し、

```text
partial_(n,U)(s_(n-1)) in CechH1(U, I^n/I^(n+1))
```

を各段で構成する。

`I^(N+1) = 0`の有限nilpotent caseでは、各段のlocal solvability、前段で選んだglobal liftに対する
次段problemの構成、逐次effectivityを証明した上で、全classの逐次消滅とfull liftを対応させる。
一般の場合は`I`-adic completion、inverse limit、limit effectivityを別定理にする。

---

## 4. Law-sensitive finite witness

Lean実装ではBoolean-circle site、selected cover、ambient ring、restrictionを共通に固定し、
law witness idealだけを変えたidempotent-zero / square-zero-nonzero対を構成した。
`LawGeneratedBooleanCircleConormalH1Pair.lean`が同一幾何上の零 / 非零classをまとめ、
`LawGeneratedBooleanCircleSquareZeroH1.lean`が非零period classを、
`LawGeneratedBooleanCirclePrimitiveAtlas.lean`がAtom / law入力から生成した非零lawful readingを与える。
これらはfinal packageのlaw-sensitive nonvacuity witnessとして接続されている。

---

## 5. 停止条件と後続接続

- primary equivalenceのLean反例、または必須semantic representationの反例は
  `target-refuted`。別係数が必要ならGOAL改訂案を返す。
- 同じmaterial premiseが二cycle続けて進まなければ`target-blocked`。
- first-order lift成立後のfull repair失敗は、次のideal-power stageまたはG-04のproof obligation。
- cover-relative Čech cohomologyとfull sheaf cohomology、cover refinementの一般比較には明示的な
  comparison dataを要求する。関連no-go theoremは
  `typedComparisonTarget_not_unconditional_for_emptyTarget`と
  `refinementZeroComparison_not_unconditional_for_coarseZero_fineNonzero`。
  前者はinhabited source / empty target、後者はcoarse-always-zero / fine-never-zeroを量化対象とし、
  全係数target・全refinement pairに対する無条件構成を反証する。

GOALの関係は次の通り。

```text
G-03: relation atomから一般generated nerveを構成
G-07: law-generated conormal first-order descent
G-04: ideal-power higher stages、nonabelian / higher / stacky / universality
```

G-07は`target-theorem-proved`として完了し、tracking Issue
[#3246](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/3246)はclose済みである。

---

## 6. Downstream finite shadow

理論完了後、tooling側ではclassの零 / 非零だけでなく証明witnessを返す。

```text
FIRST_ORDER_GLOBALIZABLE:
  adjustment 0-cochain
  compatible local lifts
  global first-order lift

FIRST_ORDER_OBSTRUCTED:
  obstruction cocycle / period witness

LIFTS_AT_ORDER_n_BUT_BLOCKED_AT_ORDER_(n+1):
  first failing ideal-power stage
```

これはAAT定理の後続clientであり、入力contract、fixture、conclusion code、実証評価は
別のtooling PRDで扱う。

Lean status: G-07 target theoremは`ResearchLean`で証明済みである。完了packageは
`lawGeneratedConormalFirstOrderDescent_package`、完了記録は
[research/reports/G-aat-quality-surface-07.md](../../research/reports/G-aat-quality-surface-07.md)を参照する。
