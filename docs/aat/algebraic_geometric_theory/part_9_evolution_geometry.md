# 第IX部 Evolution Geometry

## 1. Part8 から Part9 へ

第VIII部では、固定された finite measurement profile の中で、AAT geometry を測定可能に読む条件を定めた。
しかし、architecture は、selected operation、repair、migration、state transition によって、
選ばれた geometry の列としても現れる。

第IX部の目的は、AAT 本文の純数学的範囲を保ったまま、時間方向を扱う最小の構造を定義することである。
同一の measurement profile が所有する architectural equation system、AAT site、adequate cover と、
そこに載る trace category、state transition presheaf、temporal coefficient の中で、時間方向の law と
obstruction を読む。

```text
static geometry:
  X_ev = Site_AAT(A_ev,E_ev,Sig_ev,R_ev,Ov_ev)

evolution geometry:
  X_0 -> X_1 -> ... -> X_n
```

第IX部の主張は、選ばれた trace category、state transition presheaf、temporal coefficient の内部に限られ、
その外側の事象、遷移、状態空間については沈黙する。

## 2. Architecture Evolution Profile and Trace Category

### 定義 2.1 Architecture Evolution Profile

architecture evolution profile は、次の dependent package である。

```text
P_ev =
  finite measurement profile M_ev
  architecture object A_ev := A_{M_ev}
  equation system E_ev := E_{M_ev}
  architecture signature Sig_ev := Sig_{M_ev}
  coverage requirements R_ev := R_{M_ev}
  context-overlap package Ov_ev := Ov_{M_ev}
  AAT site X_ev := X_{M_ev} = Site_AAT(A_ev,E_ev,Sig_ev,R_ev,Ov_ev)
  adequate cover U_ev := U_{M_ev}
  trace category Tr_{P_ev}
  state transition presheaf St_{P_ev} on X_ev x Tr_{P_ev}
  temporal coefficient TempCoeff_{P_ev} on the selected product/incidence site
  selected transition and operation family F_ev
  selected evolution policy Policy_ev
```

`A_ev`、`E_ev`、`Sig_ev`、`R_ev`、`Ov_ev`、`X_ev`、`U_ev` は `M_ev` の成分から得るため、
profile の中で別々の equation system や site を選び直せない。自然言語の law display は `U_{E_ev}` である。

### 定義 2.2 Trace Category

architecture evolution profile `P_ev` に対して、trace category を次で表す。

```text
Tr_{P_ev}
```

`Tr_{P_ev}` の object は selected time point、operation stage、または abstract event state である。
射は selected transition を表す。

代表的な射は次である。

```text
apply transition
replay transition
project state
compensate action
migrate state
invert selected transition
compose transitions
```

どの transition を object / arrow として採用するかは evolution profile の一部である。

### 原則 2.3 Trace Relativity

時間方向の law は、選ばれた trace category に相対化される。

```text
different trace category
  -> different temporal law reading.
```

未選択の event、path、external state について、AAT 本文は zero / lawful / safe を主張しない。

## 3. State Transition Presheaf

### 定義 3.1 State Transition Presheaf

AAT site `X_ev` と trace category `Tr_{P_ev}` を `P_ev` から取る。
各 context `W` と trace object `t` に、`W` 上で時刻 `t` に見える state space と
transition monoid を割り当てる presheaf を state transition presheaf と呼ぶ。

```text
St_{P_ev}(W,t)
  =
  State_{P_ev}(W,t)
  together with
  Trans_{P_ev}(W,t)
```

ここで `State_{P_ev}` は selected state presheaf であり、`Trans_{P_ev}` は selected transition monoid presheaf である。
restriction は、context restriction に沿って state と transition を制限する。

```text
res_{W,V} : St_{P_ev}(W,t) -> St_{P_ev}(V,t)
```

descent 条件が selected regime で確認されている場合、この presheaf を state transition sheaf と呼ぶ。

### 定義 3.2 Temporal Coefficient

temporal law data の差、mismatch、gluing defect を測る abelian coefficient sheaf を
temporal coefficient と呼び、次で表す。

```text
TempCoeff_{P_ev}
```

`TempCoeff_{P_ev}` は、state や transition の差が abelian coefficient として読める selected regime を
固定したときに、temporal obstruction の係数として使う。

### 定義 3.3 Temporal Law

temporal law は、`St_{P_ev}` と `Tr_{P_ev}` の上の可換図式または関係式として読む。

代表例は次である。

```text
replay(e, replay(e, s)) = replay(e, s)
decode(encode(s)) ~ s
compensate(action(s)) ~ s
migrate(project_old(s)) = project_new(migrateEvents(s))
```

これらは slogan ではなく、選ばれた state transition presheaf 上の equation または descent condition である。

### 定義 3.4 Temporal Obstruction

temporal law `L_t` が selected context family 上で局所的に成立するが、trace composition や restriction と
整合しない場合、その mismatch を temporal obstruction と呼ぶ。

```text
Ob_t in H^n(Tr_{P_ev} x X_ev, TempCoeff_{P_ev})
```

ここで `Tr_{P_ev} x X_ev` は、trace category と AAT site から作る selected product site または incidence model である。
積構造、temporal coefficient、mismatch cocycle が固定されていない場合、上式は定義ではなく
reading schema として扱う。

## 4. Temporal Descent

### 定義 4.1 Replay Descent Data

cover `U = {W_i -> W}` と trace arrow `e : t -> t'` を固定する。
各 `W_i` 上に replay data

```text
r_i : State_{P_ev}(W_i,t) -> State_{P_ev}(W_i,t')
```

があるとする。
overlap 上の差が temporal coefficient の 1-cocycle `m(r)` として読めるとき、これを
replay descent data と呼ぶ。

### 定理 4.2 Temporal Descent Criterion [Certified bounded inference]

次を仮定する。

```text
Tr_{P_ev} and X_ev are finite.
selected product/incidence site Tr_{P_ev} x X_ev is fixed by P_ev.
TempCoeff_{P_ev} is an abelian coefficient sheaf in the selected regime.
local replay data has a temporal mismatch cocycle m(r).
[m(r)] = 0 in H^1(Tr_{P_ev} x X_ev, TempCoeff_{P_ev}).
```

このとき、selected regime では local adjustment の後、replay data は大域 transition として貼り合う。

```text
temporal mismatch class = 0
  +
adjust local replay data by a 0-cochain
  =>
global replay transition exists.
```

固定された trace category と temporal coefficient の中で、
局所 transition data の mismatch が coboundary なら大域 transition へ貼れることを読む。

## 5. Dissipative Policy

### 定義 5.1 Evolution Functional

evolution profile `P_ev` が所有する measurement profile `M_ev` の中で、architecture state `A` に
非負値を与える reading

```text
Phi_{M_ev}(A)
```

を evolution functional と呼ぶ。

代表例は次である。

```text
obstruction mass
harmonic mass ||h(g)||
distance-to-flatness
transfer residue norm
```

### 定義 5.2 Dissipative Policy

operation family `F_ev` が `Phi_{M_ev}` に関して dissipative であるとは、すべての selected operation
`f : A -> B` について次が成り立つことである。

```text
Phi_{M_ev}(B) <= Phi_{M_ev}(A)
```

strictly dissipative であるとは、selected non-terminal state で不等号が strict になることである。

### 定理 5.3 Finite Dissipation Stopping [Certified bounded inference]

次を仮定する。

```text
selected state set is finite.
Phi_{M_ev} takes values in a well-founded ordered set.
selected operation policy is strictly dissipative outside terminal states.
```

このとき、任意の selected evolution path は有限時間で terminal state に到達する。

terminal state が `P_ev` の architectural equation system `E_ev` に対して lawful であるためには、
第III部・第IV部の obstruction vanishing、standard scheme realization の generator-level producer theorem、
`(E_ev,R_ev,Ov_ev)`-adequate cover `U_ev` が別途必要である。

## 6. Lyapunov Reading

### 定義 6.1 AAT Lyapunov Reading

evolution functional `Phi_{M_ev}` が dissipative policy に沿って非増加であり、selected obstruction zero の近くで
最小値を取るとき、`Phi_{M_ev}` を AAT Lyapunov reading と呼ぶ。

```text
Phi_{M_ev}(A) = ||h(g_A)||
```

は、調和的負債分解がある場合の代表例である。

### 原則 6.2 Lyapunov Is Not Forecast

Lyapunov reading は、選ばれた finite evolution profile の中での散逸性を読む。
未選択の transition、未構成の状態空間、将来の任意 path については主張しない。

```text
dissipative in profile
  !=
dissipative outside the selected trace category.
```

## 7. Force Integrability Reading

### 定義 7.1 Force

evolution geometry 上の force は、architecture state を次の state へ送る selected transition である。

```text
F in F_ev : A_t -> A_{t+1}
```

force が local law data を大域 law data へ積分できるとき、integrable force と呼ぶ。

### 定理候補 7.2 Force Integrability Obstruction

force `F` により生じる temporal mismatch class

```text
ob_{P_ev}(F) in H^1(Tr_{P_ev} x X_ev, TempCoeff_{P_ev})
```

が定義されているとする。
このとき、

```text
ob_{P_ev}(F) != 0
```

なら、選ばれた temporal law data は `F` に沿って大域 evolution へ積分できない、と期待する。

`ob_{P_ev}(F)` の構成、coefficient exactness、trace product site、
temporal descent の検出性を固定して初めて定理になる。

## 8. Part9 の結論

第IX部では、AAT geometry の時間方向を trace category、state transition presheaf、temporal coefficient によって
定式化した。

```text
Trace category
  -> State transition presheaf
  -> Temporal coefficient
  -> Temporal law
  -> Temporal obstruction
  -> Dissipative policy
  -> Lyapunov reading
```

これにより、AAT は次を純数学的に扱える。

```text
local transition laws
but
global temporal obstruction remains
```

第IX部は、未選択の trace、未構成の transition、任意の将来 path について主張しない。
第IX部の結論は、固定された temporal / evolution geometry の内部でだけ読む。

次の第X部では、第III部の law equation、第IV部の cover-relative Čech `H^1`、第V部の repair を、
選ばれた有限データの内部で一つの定理連鎖として接続する。
