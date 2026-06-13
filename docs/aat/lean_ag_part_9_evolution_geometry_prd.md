# AAT代数幾何版 Lean形式化 PRD-9: 第IX部 Evolution Geometry

対象本文: [第IX部 Evolution Geometry](algebraic_geometric_theory/part_9_evolution_geometry.md)

先行PRD:
[PRD-1 第I部](lean_ag_part_1_atoms_objects_laws_prd.md) /
[PRD-2 第II部](lean_ag_part_2_sites_sheaves_prd.md) /
[PRD-3 第III部](lean_ag_part_3_law_algebra_lawful_locus_prd.md) /
[PRD-4 第IV部](lean_ag_part_4_obstruction_cohomology_prd.md) /
[PRD-5 第V部](lean_ag_part_5_derived_law_geometry_repair_prd.md) /
[PRD-6 第VI部](lean_ag_part_6_singularity_monodromy_stack_prd.md) /
[PRD-7 第VII部](lean_ag_part_7_representation_periods_analysis_prd.md) /
[PRD-8 第VIII部](lean_ag_part_8_measurement_theory_prd.md)

## 問い

第VIII部までで構成・測定可能になった static AAT geometry は、選ばれた時間方向へ拡張できるか。
すなわち、固定された trace category、state transition presheaf、temporal coefficient、law universe、
measurement profile の中で、次の evolution layer を Lean 上で sorry なしに立ち上げられるか。

```text
static geometry:
  X

measurement profile:
  M

evolution geometry:
  X_0 -> X_1 -> ... -> X_n

trace / temporal layer:
  Tr_E
  St_A
  TempCoeff_A
  TemporalLaw
  TemporalObstruction in H^n(Tr_E x X, TempCoeff_A)
```

特に、次を機械検証できるか。

- trace category `Tr_E` と AAT site `X` から、selected product / incidence site `Tr_E x X` を固定し、
  その上で temporal coefficient と Čech obstruction class を定義できること(定義2.1 / 3.2 / 3.4)。
- local replay data の mismatch class `[m(r)]` が `H^1(Tr_E x X, TempCoeff_A)` で消える場合、
  effective local adjustment と descent の下で global replay transition が得られること(定理4.2)。
- measurement profile `M` 上の evolution functional `Phi_M` と dissipative policy を定義し、
  finite / well-founded regime で selected evolution path が有限停止すること(定理5.3)。
- Lyapunov reading が forecast ではなく、固定された evolution profile 内の非増加 reading であることを型境界で保つこと(定義6.1 / 原則6.2)。
- force による temporal mismatch class が定義され、その非零性が integrability obstruction になるという theorem candidate を、
  coefficient exactness と temporal descent detecting assumption を明示した statement として形式化できること(定理候補7.2)。

採否規律: trace category / state transition presheaf / temporal coefficient / temporal law / temporal obstruction / temporal descent /
dissipative policy / Lyapunov reading / force integrability statement の構成と、CBI 定理4.2・5.3に寄与する定義・命題だけを
形式化対象に採る。寄与しない要素(例、原則、自然言語の警句、未選択の将来 path、外部イベント、実時間の意味論)は対象外とする。
実装中に、temporal descent、finite stopping、force obstruction statement に必要な仮定が本文に不足している、または
第II〜VIII部の形式化と接続できないことが見つかった場合、それは本文または本PRDの欠陥であり、ループを停止して報告する。

## 中心方針

PRD-1〜8 で確立した方針を引き継ぐ(塔を下から積む / 忠実性契約 /
`Formal/AG` 新規実装 / `axiom`・`admit`・`sorry`・`unsafe` 禁止 /
Mathlib 二段橋 / 台帳統合 / 先行PRD依存の blocked 規律 / 部番号付き台帳ラベル)。

本PRDで新たに加わる方針が五つある。

**(1) 時間は実時間ではなく selected trace category として実装する。**

第IX部は、外部世界の任意のイベント、実時計、将来予測を扱わない。Lean では、まず

```text
EvolutionProfile E
TraceCategory Tr_E
```

を record / category として固定し、object を selected time point、operation stage、abstract event state として扱う。
trace category に入っていない transition について、zero、lawful、safe、dissipative を主張しない。

**(2) `Tr_E x X` は finite product / incidence site を一次対象にする。**

本文の `Tr_E x X` は、trace category と AAT site から作る selected product site または incidence model である。
Lean では、一般の site product 理論を無条件に開発せず、まず finite trace category と finite AAT site の product / incidence model を定義する。
一般 site product への橋は、Mathlib 資産が利用できる範囲で bridge theorem とする。

**(3) temporal obstruction は ordinary obstruction cohomology の時間方向版として読む。**

第IV部で構成した cover-relative Čech cohomology を再利用し、temporal obstruction は

```text
H^n(Tr_E x X, TempCoeff_A)
```

の concrete cocycle / class として扱う。`H^n` 非零の群だけから個別の temporal failure を主張せず、
定理は必ず具体的 mismatch cocycle `m(r)` または `ob(F)` を仮定に取る。

**(4) temporal descent は class vanishing だけでなく effective adjustment と descent を仮定に出す。**

定理4.2の本文は「local adjustment の後、global replay transition が存在する」と述べる。
Lean では、これを次の仮定に分解する。

```text
m(r) is a 1-cocycle.
[m(r)] = 0, hence m(r) = d c for some 0-cochain c.
local replay data admits adjustment by c.
adjusted replay data is compatible on overlaps.
St_A satisfies descent for the selected cover.
```

この分解により、abelian coefficient class の消滅と、state transition presheaf 側の実効的な貼り合わせを混同しない。

**(5) dissipative / Lyapunov は forecast ではなく finite profile 内の停止・単調性である。**

`Phi_M` は第VIII部の measurement profile に相対化された reading である。
Lean では、finite state set、well-founded ordered value、strict decrease outside terminal states を仮定し、
「無限に非終端 selected step を続けられない」ことを証明する。
terminal state が lawful であることは、第III部・第IV部の obstruction vanishing / exactness / coverage assumptions を別途要求する。

## 背景

- PRD-8 は、static finite measurement profile の中で AAT geometry を測定する条件を定義した。
  第IX部は、その measurement profile を時間方向に載せ、state transition、temporal law、temporal obstruction を読む最小構造を与える。
- PRD-2 の AAT site / finite poset regime、PRD-4 の Čech obstruction cohomology、PRD-5 の repair path と well-founded repair、
  PRD-6 の operation category / monodromy、PRD-7 の metric / Lyapunov に近い analytic reading、PRD-8 の measurement profile / harmonic mass / distance-to-flatness が、
  本PRDの主要依存先である。
- 第IX部は、AAT本文全体の最終層であり、static geometry から temporal / evolution geometry への橋である。
  ただし、その主張は trace category、state transition presheaf、temporal coefficient の内部に限られる。
- ArchSig 型の将来 ledger では、static measurement packet に temporal replay / migration / compensation の検査結果を追加する必要がある。
  本PRDは、そのための Lean 側の理論アンカーを作るが、外部 runtime trace の収集や実システムの予測は扱わない。

## アウトカム

本PRDの完了時点で、次が成り立つ。

1. `EvolutionProfile`、`TraceCategory`、`EvolutionGeometry`、`TemporalProductSite` が Lean 上に存在する。
2. `StateTransitionPresheaf` と、descent 確認済みの場合の `StateTransitionSheaf` が定義されている。
3. `TemporalCoefficient`、`TemporalLaw`、`TemporalObstruction`、`TemporalCocycle`、`TemporalClass` が、`Tr_E x X` 上の coefficient / Čech class として定義されている。
4. `ReplayDescentData` と mismatch cocycle `m(r)` が定義され、定理4.2 Temporal Descent Criterion が theorem package として証明されている。
5. `EvolutionFunctional`、`DissipativePolicy`、`StrictlyDissipative`、`TerminalState` が定義され、定理5.3 Finite Dissipation Stopping が証明されている。
6. `AATLyapunovReading` が定義され、selected path に沿う非増加 / strict decrease の基本補題が証明されている。
7. `Force`、`IntegrableForce`、`ForceMismatchClass` が定義され、定理候補7.2 Force Integrability Obstruction が statement-only でコンパイルされている。
8. PRD-1〜8 の有限モデルが temporal examples へ拡張され、two-step trace、replay descent、dissipative stopping、force obstruction candidate の toy model が検証されている。
9. 第IX部の本文ラベルと Lean 宣言の対応が両台帳で追跡できる。

## 第IX部ラベルの処遇表

ギャップ分析はこの表を基準に行う。

| 本文ラベル | 処遇 | 備考 |
| --- | --- | --- |
| §1 Part8 から Part9 へ / Evolution geometry schema | 定義 | `EvolutionProfile` と geometry sequence `X_0 -> ... -> X_n` を定義する。static measurement profile から temporal profile へ拡張する入口(R1) |
| 定義2.1 Trace Category | 定義 | `Tr_E` を category として定義。finite trace category instance を優先。selected transition だけを含む(R1) |
| 原則2.2 Trace Relativity | 対象外 | 非主張に記録。未選択 event / path / external state について zero / lawful / safe を主張しない |
| 定義3.1 State Transition Presheaf | 定義 | `St_A(W,t) = State_A(W,t) + Trans_A(W,t)`。AAT context restriction と trace restriction / transition action を持つ(R3) |
| 定義3.2 Temporal Coefficient | 定義 | `TempCoeff_A` を `Tr_E x X` 上の abelian coefficient sheaf として定義(R2) |
| 定義3.3 Temporal Law | 定義 | `St_A` と `Tr_E` 上の equation / commutative diagram / descent condition。closed temporal equation と descent temporal law を分ける(R3) |
| 定義3.4 Temporal Obstruction | 定義 | concrete mismatch cocycle / class `Ob_t in H^n(Tr_E x X, TempCoeff_A)`。積構造がない場合は reading schema に留める(R4) |
| 定義4.1 Replay Descent Data | 定義 | cover と trace arrow に沿う local replay maps、overlap mismatch cocycle `m(r)`(R5) |
| 定理4.2 Temporal Descent Criterion [CBI] | 証明 | `[m(r)] = 0` + effective adjustment + descent -> global replay transition(R5) |
| 定義5.1 Evolution Functional | 定義 | `Phi_M(A)`。第VIII部の measurement profile に相対化された nonnegative / ordered reading(R6) |
| 定義5.2 Dissipative Policy | 定義 | `Phi_M(B) <= Phi_M(A)`、strict decrease outside terminal states(R6) |
| 定理5.3 Finite Dissipation Stopping [CBI] | 証明 | finite selected state set / well-founded value / strict dissipativity から finite stopping(R7) |
| 定義6.1 AAT Lyapunov Reading | 定義+証明 | 非増加 reading、selected obstruction zero 近傍で最小値。path monotonicity 補題を証明(R8) |
| 原則6.2 Lyapunov Is Not Forecast | 対象外 | 非主張に記録。未選択 transition / future path への予測を主張しない |
| 定義7.1 Force | 定義 | selected transition `F : A_t -> A_{t+1}`、integrable force の述語(R9) |
| 定理候補7.2 Force Integrability Obstruction | statement のみ | `ob(F) != 0 -> not IntegrableForce F` の candidate。mismatch construction / exactness / detecting descent を仮定(R9) |
| §8 Part9 の結論 | 対象外 | まとめ。台帳には登録しない |

## 要求

### R0. 前提の確認と Formal/AG/Evolution の立ち上げ

- 本PRDの実装は PRD-2(`Formal/AG/Site`)、PRD-3(`Formal/AG/LawAlgebra`)、
  PRD-4(`Formal/AG/Cohomology`)、PRD-5(`Formal/AG/Derived`)、
  PRD-6(`Formal/AG/SingularityMonodromyStack`)、PRD-7(`Formal/AG/RepresentationAnalysis`)、
  PRD-8(`Formal/AG/Measurement`)の成果物に依存する。
  着手時に依存宣言の存在を確認し、未実装の場合は `blocked` として tracking Issue に記録する。
  先行PRDの実装を本PRDのループで先取りしない。
- 第IX部のモジュールを `Formal/AG/Evolution/` 以下に実装する。
  ファイル分割は本文の節構成に概ね対応させる。例:
  `Profile.lean`, `TraceCategory.lean`, `TemporalProductSite.lean`,
  `StateTransition.lean`, `TemporalCoefficient.lean`, `TemporalLaw.lean`,
  `TemporalObstruction.lean`, `ReplayDescent.lean`, `Dissipation.lean`,
  `Lyapunov.lean`, `Force.lean`, `Examples.lean`。
- ルート import に追加し、CI の `lake build` 対象に含める。
- 本PRDは AAT AG 本文の最終部に対応するため、完了時には `Formal/AG` 全体の no-sorry / no-axiom audit を再実行する。
- 完了条件: 空でない最初のモジュールが CI でビルドされ merge されている。

### R1. EvolutionProfile・TraceCategory・EvolutionGeometry(§1、定義2.1)

- `EvolutionProfile` を record として定義する。

```text
EvolutionProfile:
  baseGeometry      -- static AAT geometry / architecture scheme
  measurementProfile M
  traceObjects
  traceTransitions
  selectedOperations
  selectedStateFamily
  selectedTemporalLaws
  selectedCoefficientProfile
```

- trace category `Tr_E` を定義する。object は selected time point / operation stage / abstract event state、
  arrow は selected transition とする。
- finite trace category regime を instance / structure として定義し、identity と composition が選ばれた transition family の中で閉じることを証明する。
- evolution geometry を、trace category から AAT geometry / architecture state への functor または finite diagram として定義する。

```text
EvolGeom_E : Tr_E -> AATGeometry
```

有限列の場合は次の special case を与える。

```text
X_0 -> X_1 -> ... -> X_n
```

- `TraceRelativity` は theorem ではなく、`EvolutionProfile` の field に入っている selected trace に相対化されることを docstring と非主張に記録する。
- 完了条件: `EvolutionProfile`、`Tr_E`、finite trace category、`EvolGeom_E` が sorry なしで存在する。

### R2. Temporal Product / Incidence Site と Temporal Coefficient(定義3.2、3.4 の ambient)

- AAT site `X` と trace category `Tr_E` から、selected product / incidence site を定義する。

```text
TemporalSite(E,X) := Tr_E x X
```

最小実装では、finite trace category と finite poset AAT site の product poset / incidence category として構成する。
- cover は、trace direction と architecture context direction の両方を持つ family として定義する。

```text
{ (t_a, W_i) -> (t, W) }
```

- PRD-4 の cover-relative Čech complex を `TemporalSite(E,X)` 上へ再利用できる bridge theorem を用意する。
- temporal coefficient `TempCoeff_A` を、`TemporalSite(E,X)` 上の abelian group sheaf または module-valued sheaf として定義する。
- finite coefficient regime では、PRD-8 の `FiniteMeasurementRegime` / `EffCoeff_M` と接続する。
- 完了条件: `TemporalSite`、temporal cover、`TempCoeff_A`、Čech bridge が sorry なしで存在する。

### R3. State Transition Presheaf と Temporal Law(定義3.1、3.3)

- state transition presheaf を定義する。

```text
St_A : TemporalSite(E,X)^op -> Type
St_A(W,t) = State_A(W,t) together with Trans_A(W,t)
```

実装上は、state carrier と transition monoid / category を field として持つ record でよい。
- context restriction と trace transition に沿う map を分けて定義する。

```text
res_context : St_A(W,t) -> St_A(V,t)
transport_trace : e : t -> t' -> State_A(W,t) -> State_A(W,t')
```

- presheaf functoriality(identity / composition)を証明する。
- selected descent 条件がある場合の `StateTransitionSheaf` を定義する。sheaf 条件そのものは PRD-2 / PRD-4 の bridge を使い、一般 sheafification は新規開発しない。
- temporal law を定義する。

```text
TemporalLaw:
  closed temporal equation
  commutative temporal square
  replay idempotence
  encode/decode compatibility
  compensation compatibility
  migration compatibility
  descent temporal law
```

各 law は selected `St_A` と `Tr_E` に相対化された predicate / equation として置く。
- 完了条件: `St_A`、restriction / transport、presheaf functoriality、`TemporalLaw` が sorry なしで存在する。

### R4. Temporal Obstruction と Temporal Class(定義3.4)

- temporal law `L_t` に対する mismatch object を定義する。

```text
TemporalMismatch(L_t) : C^n(TemporalSite(E,X), TempCoeff_A)
```

- temporal cocycle predicate と cohomology class を定義する。

```text
TemporalCocycle(m)
TemporalClass(m) : H^n(Tr_E x X, TempCoeff_A)
```

- `Ob_t in H^n(Tr_E x X, TempCoeff_A)` は、積構造・係数・mismatch cocycle が固定された場合のみ定義されることを型で表す。
- `nonzero group != concrete obstruction` の PRD-4 規律を引き継ぎ、temporal obstruction theorem は concrete class を引数に取る形にする。
- 完了条件: temporal mismatch / cocycle / class が sorry なしで存在する。

### R5. Replay Descent Data と定理4.2 Temporal Descent Criterion

- cover `U = {W_i -> W}` と trace arrow `e : t -> t'` に対する local replay data を定義する。

```text
ReplayDescentData:
  r_i : State_A(W_i,t) -> State_A(W_i,t')
```

- overlap 上の差を temporal coefficient の 1-cochain として定義する。

```text
m(r)_{ij} in TempCoeff_A(W_ij, e)
```

- mismatch が 1-cocycle である条件を定義し、torsor / affine action 型の replay adjustment がある場合に cocycle condition が自然に出る補題を証明する。
- effective temporal adjustment を定義する。

```text
adjust(c, r)_i
m(adjust(c,r)) = m(r) - d c
```

- 定理4.2を証明する。仮定:

```text
Tr_E and X are finite.
TemporalSite(E,X) is fixed.
TempCoeff_A is an abelian coefficient sheaf.
local replay data r has mismatch cocycle m(r).
[m(r)] = 0 in H^1(TemporalSite(E,X), TempCoeff_A).
replay data admits effective adjustment by 0-cochains.
adjusted compatible replay data descends for St_A.
```

結論:

```text
exists global replay transition r : State_A(W,t) -> State_A(W,t')
```

local adjustment 後の global transition として読む。
- 逆向き(`global replay transition -> [m(r)] = 0`)は定理4.2の一部ではない。
  replay mismatch construction の soundness、descent detecting、global transition が selected local replay data を生成することを
  別仮定として持つ場合だけ、nonzero class から global replay transition 不存在を導く補題を置ける。
- 完了条件: 定理4.2 が sorry なしで証明され、`proof_obligations.md` で `proved` に昇格している。

### R6. Evolution Functional と Dissipative Policy(定義5.1、5.2)

- `EvolutionFunctional` を、measurement profile `M` と selected state space 上の ordered value reading として定義する。

```text
Phi_M : State_E -> Value
```

`Value` は少なくとも preorder / well-founded order / zero or minimum predicate を必要に応じて持つ。
- 代表 reading との bridge を optional fields として持たせる。

```text
obstruction mass
harmonic mass ||h(g)||
distance-to-flatness
transfer residue norm
```

- dissipative policy を定義する。

```text
Dissipative(F,Phi_M) := forall selected f : A -> B, Phi_M(B) <= Phi_M(A)
StrictlyDissipativeOutsideTerminal := forall selected f : A -> B, NonTerminal A -> Phi_M(B) < Phi_M(A)
```

- terminal state predicate を定義する。terminal が lawful であることは別 predicate とし、ここでは同一視しない。
- selected evolution path と path-wise non-increase / strict-decrease predicate を定義する。
- 完了条件: `EvolutionFunctional`、`DissipativePolicy`、`TerminalState`、path predicates が sorry なしで存在する。

### R7. 定理5.3 Finite Dissipation Stopping

- finite selected state set、well-founded ordered value、strictly dissipative outside terminal states の下で、非終端 selected step の無限列が存在しないことを証明する。
- theorem package は次を含む。

```text
no_infinite_nonterminal_path:
  no infinite selected evolution path staying outside terminal states.

maximal_path_reaches_terminal:
  if the policy is executable from every nonterminal state and a path is maximal,
  then it reaches a terminal state in finitely many selected steps.
```

- 本文の「任意の selected evolution path は有限時間で terminal state に到達する」は、Lean では上の二つに分解して証明する。
- terminal state が lawful であるためには PRD-3 / PRD-4 の obstruction vanishing、exactness、coverage assumptions が別途必要であることを docstring と非主張に記録する。
- 完了条件: 定理5.3 package が sorry なしで証明され、`proof_obligations.md` で `proved` に昇格している。

### R8. AAT Lyapunov Reading(定義6.1)

- `AATLyapunovReading` を定義する。

```text
AATLyapunovReading(Phi_M):
  NonIncreasingAlongPolicy Phi_M
  MinimalNearSelectedObstructionZero Phi_M
  Scope = selected finite evolution profile
```

- dissipative policy がある場合、`Phi_M` は selected path に沿って非増加であることを補題として証明する。
- strictly dissipative outside terminal states の場合、terminal 到達前の loop が存在しないことを補題として証明する。
- `Phi_M(A) = ||h(g_A)||` のような harmonic mass 例は、PRD-8 の Hodge model がある場合の instance として与える。
- 原則6.2は非主張に記録し、未選択 transition / 未構成 state space / 任意 future path に対する forecast theorem を作らない。
- 完了条件: `AATLyapunovReading` と path monotonicity 補題が sorry なしで存在する。

### R9. Force と Force Integrability Obstruction Statement(定義7.1、定理候補7.2)

- force を selected transition として定義する。

```text
Force_E(A_t,A_{t+1})
```

または、state transition presheaf 上の morphism として読む。
- integrable force を、local law data が global temporal law data へ descent / integration できる predicate として定義する。

```text
IntegrableForce(F)
```

- force mismatch class を定義する。

```text
ob(F) in H^1(TemporalSite(E,X), TempCoeff_A)
```

ただし、mismatch construction、coefficient exactness、trace product site、temporal descent detecting profile を record として明示する。
- 定理候補7.2を statement-only で形式化する。

```text
ForceIntegrabilityObstructionCandidate:
  ob(F) != 0
  -> not IntegrableForce(F)
```

仮定には次を含める。

```text
ob(F) is the concrete temporal mismatch class of F.
TempCoeff_A detects temporal descent failure.
local-to-global integration is controlled by the selected temporal descent criterion.
coefficient exactness and witness coverage hold for the temporal law family.
```

- 証明はしない。future proof obligation として台帳に登録する。
- 完了条件: `Force`、`IntegrableForce`、`ForceMismatchClass`、定理候補7.2 statement がコンパイルされている。

### R10. 有限モデルの拡張

- PRD-1〜8 の有限モデル(`Formal/AG/Examples/`)を第IX部の水準へ拡張する。
  (a) two-step trace category: `t0 -> t1` を持つ finite trace category を構成し、identity / composition を検証する。
  (b) replay descent zero example: two-chart cover 上の local replay mismatch が coboundary であり、定理4.2により global replay transition が得られることを検証する。
  (c) replay descent nonzero example: pseudo-circle temporal cover 上で concrete mismatch class が非零であることを検証する。
      global replay transition が存在しないことまで示す場合は、PRD-4 の gap theorem に加えて、R5 の逆向き soundness / descent detecting 仮定を fixture に含める。
  (d) finite dissipation example: 3状態程度の finite state set と `Phi` を置き、strictly dissipative policy が terminal state に停止することを検証する。
  (e) non-lawful terminal example: terminal に到達しても selected obstruction vanishing がない限り lawful とは言えないことを、separate predicate として検証する。
  (f) Lyapunov harmonic example: PRD-8 の finite Hodge toy model の harmonic mass を `Phi_M` として使い、selected path で非増加である例を作る。
  (g) force obstruction candidate example: toy force に対し `ob(F)` class を構成し、statement-only candidate の仮定を満たす fixture を作る。
- これらは future ArchSig temporal measurement / replay audit の golden fixtures として再利用できる形を保つ。
- 完了条件: (a)–(g) が sorry なしで存在する。ただし (g) は theorem candidate の fixture であり、obstruction theorem の証明は要求しない。

### R11. 台帳整備

- `lean_theorem_index.md` の AG 節に第IX部の宣言を追加する(本文ラベル列は `IX.` 付き)。
- `proof_obligations.md` に第IX部の証明対象ラベル(定理4.2、定理5.3、Lyapunov path monotonicity 補題、example theorem 群)を登録し、進行に応じて status を更新する。
- 定理候補7.2は future proof obligation として登録するが、proved に昇格しない。
- 処遇表で「対象外」とした本文ラベルは台帳に登録しない。
- `GeneralTraceSemantics`, `ExternalRuntimeForecast`, `AllFuturePathSafety`, `UnselectedEventCompleteness`,
  `TerminalStateImpliesLawfulWithoutObstructionAssumptions`, `GeneralForceIntegrabilityTheorem` は、
  本PRDでは未実装の future proof obligation または explicit non-goal として明記する。
- 完了条件: 両台帳が最終実装と一致している。

## 非主張(claim boundary)

- 本PRDは selected trace category の内部だけを扱う。未選択 event、未選択 operation path、外部 runtime event、実時間、任意の future state について zero / lawful / safe / dissipative を主張しない。
- `Tr_E x X` が定義されていない場合、`H^n(Tr_E x X, TempCoeff_A)` は定義ではなく reading schema に留まる。
  一般 site product の完全理論は本PRDの範囲外であり、finite product / incidence site を優先する。
- temporal obstruction は concrete mismatch cocycle / class に相対化される。
  `H^1` group が非零であるだけでは、特定の replay data や force が失敗するとは主張しない。
- 定理4.2は `[m(r)] = 0` だけで global replay transition が得られるとは主張しない。
  effective adjustment action と state transition presheaf の descent を明示的に仮定する。
- temporal coefficient は abelian coefficient sheaf として扱う。non-abelian transition groupoid、gerbe 的 temporal obstruction、stacky temporal descent は扱わない。
- terminal state は lawful state ではない。terminal が lawful であるには、第III部・第IV部の obstruction vanishing、soundness / completeness、axis exactness、witness coverage、descent assumptions が別途必要である。
- dissipative policy と Lyapunov reading は forecast ではない。selected profile 外の transition、未構成の状態空間、外部入力、任意の将来 path に対する予測を与えない。
- `Phi_M` の小ささ、非増加性、停止性は structural lawfulness ではない。lawfulness は lawful locus factorization / obstruction ideal vanishing / cohomological descent の仮定で読む。
- Force Integrability Obstruction は theorem candidate であり、本PRDの完了は一般 force integrability theorem の証明を含まない。
- migration、compensation、replay、encode/decode の代表例は temporal law schema として扱い、実プログラムや外部データの正しさを主張しない。

## 完了条件(Acceptance Criteria)

- [ ] AC1. `Formal/AG/Evolution` が新設され、CI の `lake build` でビルドされる。先行PRD依存の blocked 判定が運用されている(R0)
- [ ] AC2. `EvolutionProfile`、`TraceCategory Tr_E`、finite trace category regime が形式化されている(R1)
- [ ] AC3. `EvolGeom_E : Tr_E -> AATGeometry` または有限列 `X_0 -> ... -> X_n` の special case が形式化されている(R1)
- [ ] AC4. `TemporalSite(E,X) = Tr_E x X` の finite product / incidence site が形式化されている(R2)
- [ ] AC5. temporal cover と PRD-4 Čech complex への bridge が存在する(R2)
- [ ] AC6. `TempCoeff_A` が abelian coefficient sheaf / module-valued sheaf として形式化されている(R2)
- [ ] AC7. `StateTransitionPresheaf St_A`、context restriction、trace transport が形式化されている(R3)
- [ ] AC8. `St_A` の presheaf functoriality(identity / composition)が sorry なしで証明されている(R3)
- [ ] AC9. `StateTransitionSheaf` の selected descent predicate と `TemporalLaw` が形式化されている(R3)
- [ ] AC10. `TemporalMismatch`、`TemporalCocycle`、`TemporalClass` が形式化されている(R4)
- [ ] AC11. `ReplayDescentData` と mismatch cocycle `m(r)` が形式化されている(R5)
- [ ] AC12. effective temporal adjustment の定義と `m(adjust(c,r)) = m(r) - d c` 型の補題が sorry なしで証明されている(R5)
- [ ] AC13. 定理4.2 Temporal Descent Criterion が sorry なしで証明されている(R5)
- [ ] AC14. `EvolutionFunctional Phi_M`、`DissipativePolicy`、`StrictlyDissipativeOutsideTerminal`、`TerminalState` が形式化されている(R6)
- [ ] AC15. selected evolution path と path-wise non-increase / strict-decrease predicates が形式化されている(R6)
- [ ] AC16. 定理5.3 Finite Dissipation Stopping package が sorry なしで証明されている(R7)
- [ ] AC17. `AATLyapunovReading` が形式化され、selected path monotonicity 補題が sorry なしで証明されている(R8)
- [ ] AC18. `Force`、`IntegrableForce`、`ForceMismatchClass` が形式化されている(R9)
- [ ] AC19. 定理候補7.2 Force Integrability Obstruction statement がコンパイルされている(R9)
- [ ] AC20. 有限モデル拡張((a) two-step trace category、(b) replay descent zero、(c) replay descent nonzero、(d) finite dissipation、
      (e) non-lawful terminal、(f) Lyapunov harmonic、(g) force candidate fixture)が検証されている(R10)
- [ ] AC21. `Formal/AG` 全体に `axiom` / `admit` / `sorry` / `unsafe` が存在しない
- [ ] AC22. `lean_theorem_index.md` の AG 節が第IX部の宣言を `IX.` 付き本文ラベルで含み、最終実装と一致している(R11)
- [ ] AC23. `proof_obligations.md` に第IX部の証明対象ラベルが登録され、証明済み分が `proved`、theorem candidate と non-goals が future obligation / explicit non-goal として明記されている(R11)

## 実行順序の指針

prd-loop のギャップ分析で対象を選ぶ際は、次の依存順を推奨する。

```text
R0 -> R1 -> R2
   -> R3 -> R4
   -> R5
   -> R6 -> R7
   -> R8
   -> R9
   -> R10 -> R11
```

R1/R2 は Part9 全体の ambient であり、trace と product / incidence site を先に閉じる。
R3/R4 は temporal law と obstruction class の型境界であり、Temporal Descent Criterion の前提になる。
R5 は第IX部の cohomological core なので、PRD-4 の Čech complex と toy cover を早めに接続する。
R6/R7 は well-founded stopping の独立した有限数学として閉じやすい。
R8 は PRD-8 の Hodge / harmonic examples と接続できる段階で追加する。
R9 は theorem candidate statement に留め、R5 の temporal descent detecting interface を再利用する。
R10 の有限モデルは各ブロックが閉じるたびに増分追加してよい。
