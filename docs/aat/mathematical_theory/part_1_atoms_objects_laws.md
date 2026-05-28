# 第I部 Atom・対象・法則

## 1. Primitive Architectural Fact

AAT の最小単位は Atom である。

Atom は、ソフトウェアアーキテクチャにおいてそれ以上分解せずに扱う型付き事実である。
Atom は component、relation、capability、state、effect、contract、semantic reading
などの形を取りうる。

Atom の集合を `At` と書く。各 Atom `a : At` には次が付随する。

```text
kind(a)       : AtomKind
axis(a)       : Axis
subject(a)    : Subject
predicate(a)  : Predicate
payload(a)    : Payload
```

`kind(a)` は Atom の種別を表す。`axis(a)` はその Atom がどの構造軸に関係するかを表す。
`subject(a)` は Atom が作用する対象を表し、`predicate(a)` は成立している事実を表す。
`payload(a)` は値、名前、型、証拠、重みなど、Atom の内容を担う。

### 定義 1.1 Atom

Atom とは、次を満たす型付き事実である。

```text
a = (kind, axis, subject, predicate, payload)
```

ただし、`predicate` は `subject` に対して一つの atomic statement を与える。

Atom は命題でも値でもありうる。重要なのは、AAT の内部では Atom が生成元として扱われる
ことである。law は Atom を選別し、operation は Atom を写し、signature は Atom の
振る舞いを読むが、Atom の存在そのものは Atom 公理系から始まる。

### 例 1.2 基本 Atom

```text
component(UserService)
component(UserRepository)
depends(UserService, UserRepository)
provides(UserRepository, UserStore)
state(User, Email)
effect(SendWelcomeMail)
contract(CreateUser, UserCreated)
semantic(UserId identifies User)
```

これらはすべて、AAT の中では primitive architectural fact として扱える。

## 2. Atom 公理系

Atom 公理系は、AAT が立ち上がるための始点である。

### 公理 A0 Primitive Existence

`At` は primitive fact の型である。AAT の architecture object は `At` から生成される。

### 公理 A1 Typing

すべての Atom は `kind` と `axis` を持つ。

```text
forall a : At, kind(a) is defined
forall a : At, axis(a) is defined
```

### 公理 A2 Single Fact

一つの Atom は一つの primitive fact を表す。複合的な主張は Atom の集合または
configuration として表す。

### 公理 A3 Predicate Stability

Atom の同一性は、型、対象、述語、内容によって読む。

```text
a = b
  if kind(a) = kind(b)
  and axis(a) = axis(b)
  and subject(a) = subject(b)
  and predicate(a) = predicate(b)
  and payload(a) = payload(b)
```

### 公理 A4 Composition

Atom の有限族は configuration を生成する。

```text
F subset At
-----------------
Config(F)
```

### 公理 A5 Law Non-Generation

law は Atom の成立を生成しない。law は Atom family 上の制約、保存条件、可換条件、
不在条件として働く。

### 公理 A6 Observation Non-Generation

観測、測定、報告、検査、記録は Atom の成立を生成しない。それらは Atom family に対する
読みを与えるが、Atom 自体の生成元ではない。

### 公理 A7 Operation Preservation of Atom-Origin

architecture operation は Atom family を別の Atom family へ写す。operation の結果として
得られる architecture object も Atom から生成される。

```text
op : Config(F) -> Config(G)
F, G subset At
```

この公理により、AAT の operation は architecture object の代数的変換として閉じる。

## 3. Atom Family

Atom family は、同時に扱う Atom の族である。

### 定義 3.1 Atom Family

Atom family `F` は `At` の部分集合である。

```text
F subset At
```

`F` は component、relation、state、contract、effect、semantic reading を混在して含みうる。
AAT はこの混在を排除しない。むしろ、混在した primitive fact がどの law を満たし、
どの obstruction を生むかを問う。

### 定義 3.2 Support

`support(F)` は、`F` に現れる subject の集合である。

```text
support(F) = { subject(a) | a in F }
```

support は component 集合とは限らない。operation、state、effect、contract も support に
現れうる。

### 定義 3.3 Axis Restriction

軸 `x` に対する restriction を次で定める。

```text
F|x = { a in F | axis(a) = x }
```

例えば、dependency 軸、state 軸、effect 軸、contract 軸、semantic 軸を分けて読むことで、
同じ architecture object の異なる顔が得られる。

### 定義 3.4 Compatibility

Atom family `F` が compatible であるとは、同じ subject と predicate に対して
矛盾する payload を同時に含まないことをいう。

```text
Compatible(F)
  iff not exists a b in F,
      sameSlot(a,b) and inconsistent(payload(a), payload(b))
```

compatibility は完全性ではない。`F` が compatible であっても、必要な Atom が足りないことはある。

### 定義 3.5 Closure

推論規則族 `R` に対する closure を次で定める。

```text
cl_R(F) = least G such that F subset G and R(G) subset G
```

closure は Atom family を拡張するが、closure に含まれる Atom は `R` が正当化する
導出 Atom として扱う。原始 Atom と導出 Atom を区別したい場合は、origin marker を付ける。

## 4. Configuration と Molecule

Atom は単体では architecture object にならない。architecture object は、Atom の配置と
関係づけから得られる。

### 定義 4.1 Atom Configuration

Atom configuration は次の組である。

```text
C = (F, R, E)
```

ここで、

```text
F : AtomFamily
R : relation among atoms
E : equivalence or identification data
```

`R` は Atom 間の依存、整合、生成、参照、置換、実現などを表す。`E` は同一視や
抽象化を表す。

### 定義 4.2 Molecule

molecule は、configuration 内で一つの意味単位として扱える有限 Atom 配置である。

```text
M = (F_M, R_M, E_M)
```

ただし `F_M subset F` であり、`R_M` と `E_M` は `C` から制限される。

### 例 4.3 User Creation Molecule

```text
component(UserService)
component(UserRepository)
depends(UserService, UserRepository)
contract(CreateUser, UserCreated)
state(User, Email)
effect(SendWelcomeMail)
```

この molecule は、user creation という一つの architecture concern を表す。

### 定義 4.4 Subconfiguration

`C' <= C` とは、`C'` の Atom、relation、identification が `C` に含まれることをいう。

```text
C' <= C
  iff F' subset F
  and R' subset R
  and E' subset E
```

Subconfiguration は architecture object の部分構造を表す。

## 5. Architecture Object

Architecture object は Atom configuration から生成される AAT の中心対象である。

### 定義 5.1 Architecture Object

Architecture object `A` は次の組である。

```text
A = (C, S, Q)
```

ここで、

```text
C : AtomConfiguration
S : structure maps
Q : selected quantities
```

`S` は graph、category、algebra、diagram、state transition などへの構造写像を含む。
`Q` は invariant、measure、signature axis、curvature value などを含む。

### 定義 5.2 Generated Object

Atom family `F` が architecture object `A` を生成することを次で書く。

```text
F => A
```

これは、`F` から configuration `C` が構成され、`C` に structure maps と selected
quantities が与えられて `A` が得られることを表す。

### 命題 5.3 Atom-Origin

すべての architecture object は Atom family から生成される。

```text
forall A, exists F, F => A
```

この命題は AAT の生成原理である。AAT の対象は Atom を忘れて現れるのではなく、
Atom によって支えられた architecture object として現れる。

### 定義 5.4 Object Equivalence

二つの architecture object `A` と `B` が同値であるとは、選ばれた structure maps と
selected quantities を保存する configuration equivalence が存在することをいう。

```text
A ~= B
```

同じ Atom family から生成されても、structure maps の選び方が違えば別の object として
読まれることがある。

## 6. Invariant

Invariant は architecture object 上で保存される量または性質である。

### 定義 6.1 Invariant

Architecture object `A` 上の invariant は関数または述語である。

```text
I : Obj -> Value
```

または

```text
P : Obj -> Prop
```

### 定義 6.2 Invariant Family

Invariant family は、同時に保存したい invariant の族である。

```text
Inv(A) = { I_i | i in J }
```

### 定義 6.3 Preservation

operation `op : A -> B` が invariant `I` を保存するとは、

```text
I(A) = I(B)
```

または、順序付き量の場合は

```text
I(B) <= I(A)
```

が成り立つことをいう。

### 例 6.4 保存量

```text
number of forbidden dependency atoms
cycle count
projection violation count
contract mismatch count
effect replay failure count
semantic inconsistency count
```

これらは単独の quality score ではない。各 invariant は異なる law と obstruction に対応する。

## 7. Law

Law は architecture object 上の可換性、保存性、不在性、整合性を表す。

### 定義 7.1 Law

Law `L` は architecture object に対する述語である。

```text
L : Obj -> Prop
```

より構造的には、law は次の形を取る。

```text
L(A) iff diagram(A) commutes
L(A) iff forbidden(A) is empty
L(A) iff projection(A) is sound
L(A) iff substitution(A) preserves contract
L(A) iff operation(A) preserves invariant
```

### 定義 7.2 Law Universe

Law universe は、同時に考える law の族である。

```text
Law(A) = { L_i | i in K }
```

### 定義 7.3 Lawfulness

Architecture object `A` が law universe `U` に対して lawful であるとは、

```text
Lawful_U(A) iff forall L in U, L(A)
```

が成り立つことをいう。

### 例 7.4 代表的 Law

```text
NoCycle
ProjectionSound
SubstitutionCompatible
LayerRespecting
EffectReplayLawful
StateTransitionCommutative
SemanticInterpretationConsistent
```

これらの law は自然言語の設計原則そのものではなく、Atom configuration 上の
数学的条件である。

## 8. Obstruction Circuit

Law が失敗するとき、その失敗は obstruction として読む。

### 定義 8.1 Obstruction

Law `L` に対する obstruction は、`L(A)` が成り立たないことを witness する構造である。

```text
Ob_L(A)
```

### 定義 8.2 Obstruction Circuit

Obstruction circuit は、Atom と relation の有限配置であり、ある law failure を引き起こす。

```text
O = (F_O, R_O, L)
```

ただし、

```text
F_O subset At
R_O relation on F_O
not L(A)
```

が成り立つ。

### 例 8.3 Cycle Obstruction

```text
depends(A, B)
depends(B, C)
depends(C, A)
```

これは `NoCycle` の obstruction circuit である。

### 例 8.4 Substitution Obstruction

```text
contract(Base, returns NonNull)
contract(Impl, returns Nullable)
substitutes(Impl, Base)
```

これは substitution compatibility の obstruction circuit である。

### 定義 8.5 Obstruction Valuation

Obstruction valuation は、law universe に対して obstruction の量を与える。

```text
omega_U(A) : LawUniverse -> Value
```

典型的には count、boolean、weight、rank、energy などを値に取る。

## 9. Lawfulness と Zero Obstruction

Lawfulness と obstruction zero は同じ現象を二つの方向から読む。

### 命題 9.1 Soundness

law `L` に対する obstruction valuation `omega_L` が exact なら、

```text
omega_L(A) = 0 -> L(A)
```

が成り立つ。

### 命題 9.2 Completeness

law `L` に対する obstruction family が complete なら、

```text
not L(A) -> omega_L(A) > 0
```

が成り立つ。

### 定理 9.3 Lawfulness-Zero Obstruction

law universe `U` に対して soundness と completeness が成り立つなら、

```text
Lawful_U(A) iff omega_U(A) = 0
```

が成り立つ。

この定理が AAT の flatness theorem の基本形である。

## 10. Architecture as Algebra

AAT の対象、写像、law、obstruction は代数をなす。

### 定義 10.1 Object Algebra

Object algebra は次のデータからなる。

```text
Obj
Op
Inv
Law
Ob
Sig
```

ここで、`Obj` は architecture object、`Op` は operation、`Inv` は invariant、
`Law` は law universe、`Ob` は obstruction circuit、`Sig` は signature である。

### 定義 10.2 Operation

Operation は architecture object の写像である。

```text
op : A -> B
```

Atom level では、operation は configuration の変換として与えられる。

```text
op_At : Config(F) -> Config(G)
```

### 定義 10.3 Signature

Signature は、architecture object の selected quantities を集めた多軸表現である。

```text
Sig(A) = (q_1(A), q_2(A), ..., q_n(A))
```

Signature は単一値ではない。異なる law failure は異なる axis に現れる。

### 命題 10.4 Operation Reading

operation `op : A -> B` は、次のいずれか、または複数の役割を持つ。

```text
preservation      : selected invariant を保存する
reflection        : obstruction を顕在化する
repair            : obstruction valuation を減らす
extension         : Atom family を増やして機能を拡張する
synthesis         : law を満たす object を構成する
translation       : 表現を変える
```

### 定理 10.5 AAT Core

Atom 公理系を満たす任意の universe において、次の構成が可能である。

```text
Atom
  -> AtomFamily
  -> Configuration
  -> ArchitectureObject
  -> LawUniverse
  -> ObstructionCircuit
  -> ArchitectureSignature
```

したがって、AAT は Atom 公理系の上で architecture object、law、obstruction、
signature、operation を持つ純粋な理論として立ち上がる。
