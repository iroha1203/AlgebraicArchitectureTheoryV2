# AAT Scheme Morphism Geometry

## Canonical geometry 確立後のスキーム論発展構想

このノートは、AAT Lean 基盤の補強が完了し、architecture geometry の公開経路が
`StandardArchitectureScheme`、actual lawful closed subscheme、canonical factorization、
`AATSch` category、Mathlib `Functor` へ統一された後に開く研究世界を整理する。

中心命題は単純である。

\[
\boxed{
\text{architecture event を AAT scheme の射として定義し、
law、合成、交差、変形、特異性を射に沿って研究する}
}
\]

AAT が定義するのは純粋な代数幾何的事象である。現実の development event は、
選択された Atom / Law reading の下でその事象を実現する。

---

## 1. 出発点

基盤補強後には、次の一本の構成経路が成立している。

```text
Atom / Law
  -> selected AAT site
  -> canonical sheafification
  -> StandardArchitectureScheme
  -> lawGeneratedIdealSheaf
  -> lawfulClosedSubscheme
  -> actual factorization
  -> AATSch category
  -> actual Functor
```

その具体的内容は次である。

1. architecture geometry は actual Mathlib `Scheme`、actual affine atlas、actual pullback overlapを持つ。
2. lawful locus は ideal sheaf が切り出す actual closed subscheme である。
3. lawfulness は closed immersion を通る actual factorization として表される。
4. AAT scheme の射は underlying scheme morphism と decoration preservation から構成される。
5. identity、composition、category、forgetful functor は canonical morphism から導出される。
6. nondegenerate reference model は proper principal-open atlas、strict law ideals、actual points、
   law inclusion、coefficient changeを同じprovenanceから発火する。

この基盤の恒久的な参照先は、数学本文 Part II、III、VII と Appendix A.2.1、A.3--A.5、A.7、A.8、
および Lean owner である `Formal/AG/LawAlgebra/StandardScheme.lean`、
`Formal/AG/LawAlgebra/ClosedEquationalGeometry.lean`、
`Formal/AG/ReadingFunctoriality/`、`Formal/AG/RepresentationAnalysis/AATSch.lean` とする。
本ノートが展開するderived intersection、cotangent geometry、moduli / stack、evolution geometryの
数学的参照先は、数学本文 Part V、VI、IX と Appendix A.6、A.9 とする。

ここから先の課題は、schemeを「architectureの対象」として持つ段階から、
scheme morphismを「architectureの事象」として使う段階へ進むことである。

---

## 2. Architecture event as scheme morphism

固定されたlaw universe \(U\) の下で、architecture law geometryを

\[
\mathfrak X=(X,R_X,v_X,c_X)
\]

とする。ここで \(X\) は `StandardArchitectureScheme`、\(R_X\) は
`ClosedEquationalLawReading`、\(v_X\) はreading validity、\(c_X\) は
`RequiredClosed` である。actual obstruction ideal

\[
\mathcal I_{\mathfrak X}
=
\operatorname{lawGeneratedIdealSheaf}(R_X,v_X,c_X)
\]

とlawful closed subscheme \(X^{\mathrm{law}}\) は、このprovenanceから構成される。

architecture eventは、decorated scheme morphism

\[
f:\mathfrak X\longrightarrow\mathfrak Y
\]

として定義する。そのbaseはcanonical `StandardArchitectureScheme.Hom`であり、
Atom labels、Law readings、coordinate sections、signature readings、interpretation maps、
`obstructionIdealReading`のcompatibilityを持つ。law-preserving architecture eventでは、
さらにactual law-generated idealのextension comparisonを射の条件として加える。

この定義により、architecture eventは最初から合成を持つ。

\[
X_2\xrightarrow{f_2}X_1\xrightarrow{f_1}X_0
\]

に対して、

\[
f_1\circ f_2:X_2\longrightarrow X_0
\]

がdevelopment historyの合成された幾何学的事象になる。identity eventは
\(\operatorname{id}_X\)であり、結合則はscheme morphismの結合則から得られる。

したがって、AATにおける進化の最小単位は射である。

---

## 3. Law transportを持つ射

scheme morphismをarchitecture eventとして使う最初の核心は、obstruction idealの移送である。

\(\mathfrak X\)と\(\mathfrak Y\)のactual law-generated ideal sheafを

\[
\mathcal I_X\subseteq\mathcal O_X,
\qquad
\mathcal I_Y\subseteq\mathcal O_Y
\]

とする。射\(f:X\to Y\)に沿って、\(Y\)のidealを\(X\)へ引き戻す。

\[
f^*_{\mathrm{ideal}}\mathcal I_Y
=
f^{-1}\mathcal I_Y\cdot\mathcal O_X.
\]

以下、\(f^*_{\mathrm{ideal}}\) はideal extensionを表す。module、complex、cotangent objectの
pullbackには通常の \(Lf^*\) または文脈に応じたpullback notationを使い、両者を区別する。

### 3.1 Law-preserving morphism

law-preserving morphismは、比較射

\[
f^*_{\mathrm{ideal}}\mathcal I_Y\longrightarrow\mathcal I_X
\]

すなわちideal inclusion

\[
f^*_{\mathrm{ideal}}\mathcal I_Y\subseteq\mathcal I_X
\]

を持つ射として定義する。

このinclusionから、lawful closed subscheme間の射

\[
f^{\mathrm{law}}:
X^{\mathrm{law}}\longrightarrow Y^{\mathrm{law}}
\]

が構成され、次の正方形が可換になる。

\[
\begin{CD}
X^{\mathrm{law}} @>{f^{\mathrm{law}}}>> Y^{\mathrm{law}}\\
@V{\iota_X}VV @VV{\iota_Y}V\\
X @>{f}>> Y.
\end{CD}
\]

これはlaw preservationをclosed-subscheme factorizationとして表す。

### 3.2 Exact law transport

さらに、

\[
f^*_{\mathrm{ideal}}\mathcal I_Y=\mathcal I_X
\]

が成り立つとき、\(f\)はexact law transportを持つ。

このとき\(X\)側のlaw geometryは、\(Y\)側のlaw geometryのbase changeとして得られる。

\[
X^{\mathrm{law}}
\cong
X\times_Y Y^{\mathrm{law}}.
\]

### 3.3 Law strengtheningとlaw relaxation

二つのidealの順序により、architecture eventを分類できる。

```text
f*ideal I_Y ⊆ I_X:
  transported lawを保持し、X側に追加方程式を許す。

f*ideal I_Y = I_X:
  obstruction geometryをexactに移送する。

I_X ⊆ f*ideal I_Y:
  X側のlaw equationがtransported equationの部分系になる。
```

この分類は違反数の増減ではなく、ideal sheafとclosed subschemeの順序による分類である。

---

## 4. Lawful locus functor

law geometry \(\mathfrak X=(X,R_X,v_X,c_X)\) を対象、law-preserving architecture eventを射とする
categoryを

\[
\mathbf{AATSch}^{\mathrm{law}}_U
\]

とする。

identityとcompositionについてideal inclusionが保存されることを証明すれば、lawful locusはfunctorになる。

\[
\operatorname{Lawful}_U:
\mathbf{AATSch}^{\mathrm{law}}_U
\longrightarrow
\mathbf{Scheme}.
\]

各対象では

\[
X\longmapsto X^{\mathrm{law}},
\]

各射では

\[
f\longmapsto f^{\mathrm{law}}
\]

と送る。

closed immersionはnatural transformationをなす。

\[
\iota_U:
\operatorname{Lawful}_U
\Longrightarrow
\operatorname{Underlying}.
\]

この構造によって、次が同じfunctorial law geometryの定理になる。

- identity eventはlawful locus上でもidentityになる。
- event compositionはlawful morphismのcompositionになる。
- law inclusionはclosed immersionを誘導する。
- coefficient changeはlawful locusのbase-change mapを誘導する。
- representation functorはlawful eventをtarget categoryへ送る。

---

## 5. Fiber productとlawの同時充足

scheme theoryをarchitecture eventへ展開する第二の中核はfiber productである。

### 5.1 二つのlaw universeの合成

同じambient scheme \(X\) 上の二つのlaw idealを

\[
\mathcal I_U,
\qquad
\mathcal I_V
\]

とする。それぞれのlawful locusは

\[
X_U=V(\mathcal I_U),
\qquad
X_V=V(\mathcal I_V)
\]

である。

同時充足locusはscheme-theoretic intersection

\[
X_U\times_X X_V
\]

であり、affine chart上ではideal sumに対応する。

\[
V(\mathcal I_U)\times_XV(\mathcal I_V)
\cong
V(\mathcal I_U+\mathcal I_V).
\]

この同型は、複数lawの同時充足を集合の共通部分からschemeの普遍性へ引き上げる。

### 5.2 Decorated pullback

二つのarchitecture event

\[
X\xrightarrow{f}S,
\qquad
Y\xrightarrow{g}S
\]

に対して、underlying scheme pullback

\[
X\times_SY
\]

へAtom、Law、coordinate、obstruction idealのpullback decorationを載せる。

目標は、`AATSch`がpullbackを持つためのcanonical constructionを与えることである。

共通base law geometry \(\mathfrak S\) への二つの射がexact law transportを持ち、
pullback上のlaw reading、validity、required closedness、decorationを両脚からcanonicalに構成できるとする。
このときpullback idealは両脚の共通idealのextensionとして定まり、lawful locusとの交換則を得る。

\[
\operatorname{Lawful}_U(X\times_SY)
\cong
\operatorname{Lawful}_U(X)
\times_{\operatorname{Lawful}_U(S)}
\operatorname{Lawful}_U(Y).
\]

この定理は、複数のarchitecture eventが同じbase上で両立する条件を表す。

---

## 6. Derived fiber productと潜在law conflict

理論説明では、classical fiber productからderived fiber productへの移行を一続きに示すため、
infinitesimal geometryより先にderived intersectionを置く。Lean実装はconormal constructionを
derived comparisonの入力に使うため、Stage 4のconormal / cotangentを先に構成する。

classical fiber productがlawの同時零点を保持する一方、derived fiber productは交差の仕方を保持する。

\[
X_U\times_X^{\mathbf R}X_V.
\]

affine chart \(X=\operatorname{Spec}A\) 上では、

\[
\mathcal O_{X_U}
\otimes_A^{\mathbf L}
\mathcal O_{X_V}
\]

を用い、そのhomologyは

\[
\operatorname{Tor}_i^A(A/I_U,A/I_V)
\]

を与える。

この構造から、次の研究課題が生まれる。

1. law-compatible morphismに沿うTor conflictのfunctoriality。
2. flat coefficient changeに沿うderived intersectionのbase change。
3. event compositionに沿うconflict transport。
4. classical lawful intersectionとderived lawful intersectionの比較射。
5. Stage 4で構成するconormal geometryとTorによるexcess intersectionのcomparison。

二つのlawful eventが同じambient geometry上で交わるとき、derived residueはその非横断性を記録する。

---

## 7. Lawful closed immersionからinfinitesimal geometryへ

lawful closed immersion

\[
\iota:X^{\mathrm{law}}\hookrightarrow X
\]

とobstruction ideal \(\mathcal I\) から、conormal sheafを構成する。

\[
\mathcal N^*_{X^{\mathrm{law}}/X}
=
\mathcal I/\mathcal I^2.
\]

これはlawful locusの周囲にあるfirst-order architecture directionを保持する。

### 7.1 Cotangent triangle

base scheme \(B\) 上のactual lawful closed immersion \(\iota:X^{\mathrm{law}}\hookrightarrow X\) に、
まず一般のtransitivity triangleを接続する。

\[
L_{X^{\mathrm{law}}/X}[-1]
\longrightarrow
L\iota^*L_{X/B}
\longrightarrow
L_{X^{\mathrm{law}}/B}
\longrightarrow
L_{X^{\mathrm{law}}/X}.
\]

lawful immersionがregular / lciであるとき、relative termはconormal sheafのshift

\[
L_{X^{\mathrm{law}}/X}
\simeq
(\mathcal I/\mathcal I^2)[1]
\]

に同定される。これにより、selected cotangent readingをlaw-generated ideal sheafのcanonical constructionと
regular / lci lawful geometryへ結び付ける。

### 7.2 Differential of an architecture event

architecture event \(f:X\to Y\) はcotangent map

\[
Lf^*L_Y\longrightarrow L_X
\]

を誘導する。cotangent complexesがperfectでpullbackとderived dualが交換するとき、このmapを双対化して
tangent map

\[
df:T_X\longrightarrow f^*T_Y
\]

を得る。一般の場合は

\[
R\mathcal Hom(L_X,\mathcal O_X)
\longrightarrow
R\mathcal Hom(Lf^*L_Y,\mathcal O_X)
\]

を基本のderived dual morphismとして保持する。

このmapにより、eventがfirst-order directionをどのように移送するかを研究できる。

- tangent directionの保存
- infinitesimal freedomの生成
- conormal directionの消去
- tangent rankのjump
- higher lifting obstructionの移送

### 7.3 Smooth、unramified、étale

law baseに相対化されたscheme morphismとして、architecture eventの標準的なsmoothness、
unramifiedness、étalenessを定義し、decorationとlaw transportのcompatibilityを重ねる。

```text
smooth:
  locally of finite presentationで、infinitesimal lifting propertyを持つ。

unramified:
  locally of finite typeで、infinitesimal liftingの一意性を持つ。

étale:
  locally of finite presentationで、infinitesimal liftingが一意に存在する。
```

selected deformation-test regimeだけに相対化したlifting predicateは `U-smooth`、
`U-unramified`、`U-étale` として標準的なscheme predicateから区別する。
これらはeventの性質である。

---

## 8. Nilpotent structureとarchitecture fragility

同じunderlying point setを持つlawful locusでも、scheme structureは異なりうる。

\[
V(I)
\qquad\text{and}\qquad
V(I^2)
\]

は同じ点を持ちながら、異なるnilpotent structureとconormal dataを持つ。

AATでは、この差をarchitecture fragilityの幾何として読む。

- 現在のlawful pointの周囲に残るfirst-order obstruction
- 特定方向の変形に対する高い感度
- 同じlawful point集合を持つarchitecture間のrepair可能性の差
- tangent dimensionとembedded componentの差
- multiplicityとして残るlaw equationの重なり

この発展により、lawful / unlawfulの二値から、lawful locusの厚みと変形可能性へ分析対象が広がる。

---

## 9. Scheme invariantsによるarchitecture geometry

canonical scheme constructionが確立した後は、標準的なscheme invariantsをarchitecture geometryへ適用できる。

候補は次である。

- Krull dimension
- irreducible components
- connected components
- minimal primes / associated primes
- nilradical
- singular locus
- embedding dimension
- depth
- multiplicity
- Hilbert function / Hilbert polynomial
- tangent dimension
- Tor amplitude

最初に証明すべきなのはpresentation invarianceである。同じAtom / Law geometryを異なるgeneratorや
affine presentationで表した場合、得られるinvariantがscheme isomorphismに沿って一致することを示す。

これにより、measurementは座標表示ではなくarchitecture geometryに属する量になる。

---

## 10. Stratification

lawful locusを一様な空間として扱う代わりに、scheme invariantsが一定になるstrataへ分解する。

\[
X^{\mathrm{law}}
=
\bigsqcup_{\alpha}S_\alpha.
\]

stratificationの候補は次である。

- tangent dimension
- rank of conormal sheaf
- obstruction support
- singularity type
- law support pattern
- associated prime
- Tor amplitude

architecture event \(f:X\to Y\) がstrataをどのように送るかを調べることで、
obstructionの移動、集中、分裂、合流を幾何学的に追跡できる。

---

## 11. Repair transformations

repairを、law geometryを変換するscheme morphismまたはcorrespondenceとして定義する。

### 11.1 Open immersionとclosed immersion

```text
open immersion:
  architecture geometryの選択されたopen regimeへの制限。

closed immersion:
  新しいlaw equationによるclosed conditionの追加。
```

### 11.2 Blow-up

obstructionが集中するclosed center

\[
Z=V(\mathcal J)\subseteq X
\]

に沿うblow-up

\[
\operatorname{Bl}_ZX\longrightarrow X
\]

を構成する。

AAT repairとしてのblow-upは、次のデータを持つ。

1. law-generated center \(Z\)
2. exceptional divisor
3. obstruction idealのtotal transform
4. lawful locusのstrict transform
5. transform前後のconormal / singularity comparison

最初の定理目標は、具体的なreference family上で、strict transform後のobstruction support、
conormal rank、singular locusを計算し、exceptional geometryがlaw directionを分離するための
判定条件を与えることである。

### 11.3 Normalization

reduced finite-type architecture schemeをnormalization-finiteなbase上で扱い、normalization

\[
X^\nu\longrightarrow X
\]

は、同じcoordinate algebra内で交差していたirreducible branchをcomponentwiseに分離する。
branch separation、monodromy、decomposition stackとの接続が研究対象になる。

### 11.4 Repair adoption criterion

各repair constructionは、center、induced morphism、lawful locus transform、obstruction transport、
composition theoremを一組として持つ。これによりrepairは標準代数幾何の操作としてAATへ入る。

---

## 12. Moduliとstack

固定されたAtom vocabularyとlaw universe \(U\) に対し、test scheme \(T\) 上のlawful architecture familyと
そのbase-preserving morphismからcategory

\[
\mathcal F_U(T)
=
\mathbf{LawfulArchitectureFamily}_U(T)
\]

を作る。一般のarchitecture eventはこのcategoryのmorphismとして保持する。

### 12.1 Functor of points

base changeによりfibred categoryを得る。その各fiberからisomorphismだけを取ったcoreは、
category fibred in groupoids

\[
p:\mathcal M_U\longrightarrow\mathbf{Scheme}
\]

を与える。cleavageを選ぶと、これはpseudofunctor

\[
\mathbf{Scheme}^{op}\longrightarrow\mathbf{Groupoid}
\]

として表示される。split structureまたはstrictificationを構成した段階でstrict functorを得る。

descentを証明した後、automorphismが自明でset-valued functorへ降りる部分についてはschemeによる
representabilityを問う。automorphismを保持する部分については、representable diagonalとsmooth atlasを
構成してalgebraic architecture stackへ進む。

### 12.2 Moduli上のevent

一般のarchitecture eventはfibred category \(\mathcal F_U\) のmorphismとして現れる。
moduli stack \(\mathcal M_U\) のarrowはlawful family間のisomorphismである。

これにより、次を同じ形式で扱える。

- lawful architecture family
- family間の自然変換
- local decompositionのautomorphism
- path-dependent refactor
- monodromy
- canonical decompositionの存在

---

## 13. Evolution geometryとの統合

trace category \(\mathcal T\) に対し、architecture evolutionをdiagram

\[
X:\mathcal T\longrightarrow\mathbf{AATSch}^{\mathrm{law}}_U
\]

として表す。

各trace arrow \(t\to t'\) はarchitecture event

\[
X_t\longrightarrow X_{t'}
\]

へ送られる。

このdiagram上で、次を研究する。

- event composition
- lawful locusのfunctorial transport
- obstruction idealの時間発展
- singular strataの移動
- derived conflictの生成と消滅
- repair pathのhomotopy / monodromy
- dissipative morphism family
- base changeされたdevelopment trace

同じbaseから出る二つのeventと、そのsimultaneous realizationはpullback / pushout comparisonで表される。
これによりmerge geometryは普遍性の問題として現れる。

---

## 14. 現実のdevelopment eventとの対応

AAT内部ではarchitecture event \(f:X\to Y\) を純粋に定義する。

現実側では、development event \(e\) とAAT event \(f\) の実現関係を

\[
\operatorname{Realizes}_\rho(e,f)
\]

として読む。\(\rho\)は選択されたAtom / Law / evidence readingである。

現実のdevelopment eventには、次の形態がある。

- pull request
- commit sequence
- refactoring
- migration
- deployment transition
- policy change
- architecture decisionの適用

この対応では、AATのscheme morphismが先にあり、PRはその事象が現実に現れる一形態である。

```text
AAT:
  architecture event f : X -> Y

SFT / development reading:
  event e realizes f

ArchSig:
  selected evidence contractからbounded diagnostic / analysis packetを計算する
```

LeanとArchSigはAATへそれぞれ接続する疎結合な兄弟クライアントである。

```text
             AAT
            /   \
         Lean   ArchSig
```

Leanはscheme morphism、law transport、factorization、compositionの数学的statementを形式化する。
ArchSigはArchMap、LawPolicy、law-equation surface、MeasurementProfileからbounded diagnostic / analysis packetを計算する。

scheme-morphism theorem packageの成立後には、別のtooling計画として、event correspondence、
coordinate translation、ideal transport certificateを入力artifactへ加え、architecture eventの
measurement packetを生成するArchSig client extensionを設計できる。

---

## 15. 既存研究との接続

AAT scheme morphism geometryは、複数の先行研究と接続できる。

### 15.1 Categorical patch theory

[Mimram and Di Giusto, *A Categorical Theory of Patches*](https://arxiv.org/abs/1311.3903)は、
fileをobject、patchをmorphismとするcategoryを構成し、coinitial patchのmergeをpushoutとして扱う。

[Mori and Hashimoto, *On the Correctness of Software Merge*](https://arxiv.org/abs/2607.07987)は、
three-way mergeのuniversalityをpushoutで定式化し、構造的mergeへ接続している。

AATはarchitecture eventをdecorated scheme morphismとして扱い、lawful closed subscheme、
obstruction ideal、derived intersection、deformationを同じ射に沿って読む。

### 15.2 Sheaf consistency

[Gibson, *Sheaves as a Means of Maintaining Consistency in Model-based Systems Engineering*](https://arxiv.org/abs/2605.08609)は、
engineering viewの局所整合性とglobal gluingをsheaf conditionで表し、Lean 4で形式化している。

AATでは、そのlocal-to-global geometryをringed AAT site、law algebra、obstruction ideal、
architecture schemeへ進め、scheme morphismに沿うtransportまで研究する。

### 15.3 Polynomial ideal program analysis

[Cyphert and Kincaid, *Solvable Polynomial Ideals: The Ideal Reflection for Program Analysis*](https://arxiv.org/abs/2311.04092)は、
polynomial idealをprogram summaryとnonlinear reasoningへ用いる。

AATではAtomとLawがarchitecture coordinateとequationを生成し、ideal sheaf、closed subscheme、
base change、derived intersectionへ接続する。

### 15.4 Functorial data migration

[Spivak, *Functorial Data Migration*](https://arxiv.org/abs/1009.1166)は、schemaをcategory、instanceをfunctorとして扱い、
schema morphismからcanonical data migration functorを導く。

AATではAtom vocabulary、law universe、coefficient、coverageのchangeをfunctorialに扱い、
architecture schemeとlawful locusのbase changeへ接続する。

### 15.5 AATの統合点

これらの接続は、AAT内で次の一本の幾何へ統合される。

\[
\boxed{
\text{Atom}
\to
\text{Law algebra}
\to
\text{Architecture scheme}
\to
\text{Scheme morphism}
\to
\text{Law transport}
\to
\text{Derived / deformation geometry}
}
\]

---

## 16. Lean研究プログラム

### Stage 1: Law-compatible morphism

最初に、canonical `StandardArchitectureScheme.Hom`へactual law-generated idealのtransportを追加する。
owner関係は次で固定する。

```text
LawGeometry_U(X)
  := (R : ClosedEquationalLawReading raw X,
      v : IsClosedEquationalLawReading raw X R,
      c : RequiredClosed raw X R)

I(X,R,v,c)
  := lawGeneratedIdealSheaf raw X R v c

LawCompatibleHom((X,R_X,v_X,c_X), (Y,R_Y,v_Y,c_Y))
  := (f : StandardArchitectureScheme.Hom X Y,
      obstructionIdealReading compatibility for f,
      f*ideal I(Y,R_Y,v_Y,c_Y) <= I(X,R_X,v_X,c_X))
```

ideal inclusionはlaw-compatible morphismの定義条件であり、中心定理はそこからMathlibのcanonical
closed-subscheme mapとambient squareを構成する。identityとcompositionでは、生成idealのprovenance、
ideal extensionのidentity / composition、base morphismのidentity / compositionをproof termで使用する。
strict inclusionを持つ射と、inclusionが成立しない射を同じreference modelに置き、定義の発火も固定する。

候補宣言は次である。

```lean
lawfulMap
lawfulMap_immersion
lawfulMap_id
lawfulMap_comp
exactLawTransport_pullbackIso
```

| target | 入力 | 構成・証明する内容 |
| --- | --- | --- |
| `lawfulMap` | source / target `LawGeometry`、`LawCompatibleHom` | Mathlibのclosed subscheme map |
| `lawfulMap_id` | 一つの`LawGeometry` | ideal extensionのidentityからmap equality |
| `lawfulMap_comp` | composableな二つの`LawCompatibleHom` | ideal extensionのcompositionからmap equality |
| `exactLawTransport_pullbackIso` | `LawCompatibleHom`と生成idealのextension equality | canonical comparison mapからpullback isomorphismを構成 |

### Stage 2: Lawful locus functor

```lean
LawfulFunctor : AATSchLaw raw ⥤ AlgebraicGeometry.Scheme
lawfulImmersionNatTrans : LawfulFunctor ⟶ UnderlyingFunctor
```

reference modelでは、non-identity ring hom、strict law inclusion、coefficient changeを使って
identity / composition / exact transportを発火させる。

### Stage 3: Decorated pullbacks

```lean
aatPullback
aatPullback_fst
aatPullback_snd
lawful_pullback_iso
lawful_inf_iso_pullback
```

underlying Mathlib pullbackからdecoration、law ideal、lawful locusを構成し、普遍性を証明する。

### Stage 4: Conormal and cotangent geometry

```lean
lawfulConormal
lawfulCotangentTransitivityTriangle
lciLawfulRelativeCotangentIso
architectureDifferential
architectureDifferential_id
architectureDifferential_comp
squareZeroLawfulLift
```

`I/I²`をactual lawful closed immersionから構成し、cotangent / tangent mapへ接続する。

### Stage 5: Derived event geometry

```lean
derivedLawfulIntersection
lawConflictTor
lawConflictTor_baseChange
lawConflictTor_map
lawConflictTor_comp
```

`lawConflictTor_map`はlaw-compatibleな可換正方形とinduced quotient mapsを引数とし、
`lawConflictTor_baseChange`はflat base changeを仮定する。`lawConflictTor_comp`は前者が構成したmapの
合成則を述べる。classical intersection、Tor、derived intersectionを同じmorphism APIへ接続する。

### Stage 6: Moduli and repair transformations

```lean
LawfulArchitectureFamilyFibredCategory
LawfulArchitectureModuliCore
LawfulArchitectureStack
blowupObstructionCenter
lawfulStrictTransform
normalizationLawTransport
```

moduli functor、automorphism、blow-up、normalizationをarchitecture eventのcategoryへ統合する。

---

## 17. 最初のnondegenerate theorem package

最初の実装単位は、既存のprincipal-open reference geometryを使う。ringとlocalization mapを

\[
A_0=\mathbb Z[x],
\qquad
A_1=A_0[x^{-1}],
\qquad
A_2=A_1[(1-x)^{-1}],
\]

\[
\varphi_1:A_0\longrightarrow A_1,
\qquad
\varphi_2:A_1\longrightarrow A_2
\]

で固定する。反変なscheme morphismはcanonical principal-open immersion

\[
\operatorname{Spec}A_2
\xrightarrow{f_2}
\operatorname{Spec}A_1
\xrightarrow{f_1}
\operatorname{Spec}A_0
\]

である。各 \(X_i\) はこのaffine scheme、actual atlas、reference decorationから構成し、
\(f_i\) について `AATReadingDecoration.Preserves` とatlas compatibilityを証明して、actual
`StandardArchitectureScheme.Hom` \(F_i:X_i\to X_{i-1}\) へ持ち上げる。

law dataは各object上の

\[
R_i:\operatorname{ClosedEquationalLawReading}(raw,X_i),
\quad
v_i:\operatorname{IsClosedEquationalLawReading}(raw,X_i,R_i),
\quad
c_i:\operatorname{RequiredClosed}(raw,X_i,R_i)
\]

から構成する。IdealSheafDataを

\[
\mathcal I_i
:=
\operatorname{lawGeneratedIdealSheaf}(raw,X_i,R_i,v_i,c_i)
\]

と置く。\(R_0\) にはweak law witnessを使い、canonical affine global-section isoの下で対応するring idealを

\[
J_0=(x(x-1))\subseteq A_0
\]

と同定する。\(R_1,R_2\) はこのreadingのlocalizationとして構成し、対応するglobal-section idealについて

\[
J_1=\varphi_1(J_0)A_1=(x-1),
\qquad
J_2=\varphi_2(J_1)A_2=(1)
\]

を得る。さらにlocalization / restriction theoremからIdealSheafDataの等式

\[
F_1^*{}_{\mathrm{ideal}}\mathcal I_0=\mathcal I_1,
\qquad
F_2^*{}_{\mathrm{ideal}}\mathcal I_1=\mathcal I_2
\]

を証明する。これが二つのnon-identity exact law-compatible eventと、そのcompositionを同じprovenanceから
発火させる。object-levelのlaw comparisonにはreference readingが生成するglobal-section ideal chain

\[
(x(x-1))\subsetneq(x)\subsetneq(x,2)
\]

を使う。identity base上でsourceをstrong、targetをweakとするeventは
\(\mathcal I_{\mathrm{weak}}\subsetneq\mathcal I_{\mathrm{strong}}\) によりlaw-compatibleとなる。
sourceをweak、targetをstrongとするreverse eventは \((x)\nsubseteq(x(x-1))\) により不成立となる。

flat coefficient changeには

\[
\beta:\mathbb Z[x]\longrightarrow\mathbb Z[t][x]
\]

を用い、localization diagram、decoration、readings、生成idealのscalar extensionからmixed naturality squareを作る。
この固定データに対し、次を一つのpackageで証明する。

1. non-identity ring homからactual architecture scheme morphismを構成する。
2. obstruction ideal pullback inclusionを具体計算する。
3. induced lawful closed-subscheme mapを構成する。
4. ambient squareを可換にする。
5. identity law transportを証明する。
6. 二つのnon-identity eventのcomposition lawを証明する。
7. exact transport caseでlawful squareがpullbackになることを証明する。
8. flat coefficient changeとlaw inclusionのmixed naturality squareを証明する。

このpackageにより、scheme morphismはabstract interfaceではなく、actual ring map、ideal map、
closed immersion、pullbackを結ぶ具体的なAAT theoremになる。

---

## 18. 到達点と優先順

この研究によって、architecture eventの列はscheme morphismのdiagramとなり、law preservationは
ideal extensionとclosed-subscheme square、simultaneous realizationはfiber productの普遍性、
latent conflictはderived intersection、refactoringはdeformationとして扱われる。nilpotent thickening、
embedded component、multiplicity、singular locus、higher Torはlawful geometryの内部構造を与える。
AtomとLawをprimitiveとするため、これらの定理は同じ形のまま複数のtechnology readingへ展開される。

実装順は次で固定する。

```text
law-compatible morphism
  -> lawful locus functor
  -> exact pullback theorem
  -> decorated fiber product
  -> conormal / cotangent geometry
  -> derived event geometry
  -> moduli / stack
  -> repair transformations
```

最初の三段階で、AAT scheme morphismはlawful geometryを運ぶcanonicalな射になる。
decorated fiber productまで進むとlaw conjunctionとsimultaneous realizationが得られる。
actual lawful closed immersionのconormal / cotangent geometryを構成した後、derived intersection、
moduli、blow-upへ進む。

最終的に、AATはarchitecture objectの代数幾何から、architecture eventとその合成、交差、変形、
repairを扱う代数幾何へ進む。現実のPR、migration、deployment、refactoringは、この純粋な
AAT geometry上の事象がdevelopment processに現れる具体的な形態として読まれる。

---

## 19. Expansion atlas: scheme morphismから開く十本の研究軸

ここまでの構想を核として、AAT scheme theoryはさらに複数の方向へ発展できる。
各方向は独立した比喩ではなく、law geometry、architecture event、base change、fiber product、
cotangent complexという共通の構成から生じる。

| 研究軸 | 新しいAAT object | 最初の中心定理 |
| --- | --- | --- |
| categorical law geometry | law geometryのGrothendieck fibration | vertical strengtheningとexact transportへのcanonical factorization |
| morphism calculus | image、graph、proper / finite / flat event | morphism propertyのlawful locusへのbase change |
| correspondence geometry | span、partial / rational event、kernel | graph embeddingとfiber-product composition |
| arithmetic / formal geometry | generic・special fiber、formal completion、jet | specialization defectとsaturation / Torの対応 |
| birational / log / tropical geometry | Rees algebra、normal cone、log scheme、fan | blow-upの普遍性とlaw transform |
| derived / spectral geometry | derived lawful locus、derived event stack | truncationとclassical lawful locusのcomparison |
| cohomological / motivic geometry | six operations、K-class、cycle、motive | base change・projection formula・localization triangle |
| singularity / dynamical geometry | singularity category、vanishing cycle、fixed scheme | degeneration residueとderived periodic locus |
| moduli / higher geometry | mapping stack、higher descent、gerbe、Hall algebra | event compositionのmapping-stack realization |
| logical / Galois / higher-algebra frontier | classifying topos、étale Galois、operad、Poisson structure | alternative realization間のcomparison |

### 19.1 Law geometryのGrothendieck fibration

scheme \(X\) 上のquasi-coherent law idealのfiberを \(\operatorname{Law}(X)\) とし、

\[
\pi:\mathbf{LawGeom}_U\longrightarrow\mathbf{Scheme}
\]

を考える。objectは \((X,\mathcal I_X)\)、射は

\[
f:(X,\mathcal I_X)\longrightarrow(Y,\mathcal I_Y),
\qquad
f^*_{\mathrm{ideal}}\mathcal I_Y\subseteq\mathcal I_X
\]

である。ideal extensionがcartesian liftを与え、exact law transportを持つeventがcartesian arrowになる。

任意のlaw-compatible eventにはcanonical factorization

\[
(X,\mathcal I_X)
\longrightarrow
(X,f^*_{\mathrm{ideal}}\mathcal I_Y)
\longrightarrow
(Y,\mathcal I_Y)
\]

がある。第一射は同じambient scheme上のvertical law strengthening、第二射はexact transportである。
この分解について、存在、一意性、identity、compositionとのcompatibilityを証明する。

affine event \(\varphi:B\to A\) ではideal extensionとcontractionがadjunction

\[
JA\subseteq I
\quad\Longleftrightarrow\quad
J\subseteq\varphi^{-1}(I)
\]

をなす。このunitとcounitからlaw saturationとlaw interiorを構成できる。localization
\(A\to A_x\) ではcontraction of extensionが \(I:x^\infty\) となり、eventが保持するlaw componentを
scheme-theoretically抽出する。

最初のreference theoremは、strict law inclusion

\[
(x(x-1))\subsetneq(x)
\]

によるvertical eventと、principal-open localizationによるcartesian eventを合成し、一般の
law-compatible eventのnormal formを発火させることである。

### 19.2 Scheme morphism propertyとfactorization calculus

exact law transportにより

\[
X^{\mathrm{law}}
\cong
X\times_Y Y^{\mathrm{law}}
\]

が得られるため、base changeで安定なmorphism propertyはlawful eventへ移る。

\[
P\in
\{\text{proper, smooth, finite, flat, étale, separated, finite locally free}\}
\]

に対し、\(f\) が \(P\) を持つexact eventなら \(f^{\mathrm{law}}\) も \(P\) を持つ。
identity、composition、base changeまでを一つのproperty calculusとして構成する。

quasi-compact event \(f:X\to Y\) にはscheme-theoretic image

\[
Z_f
=
V\!\left(\ker(\mathcal O_Y\to f_*\mathcal O_X)\right)
\]

を割り当て、law idealを

\[
\mathcal I_{Z_f}
=
(\mathcal I_Y+\mathcal K_f)/\mathcal K_f
\]

とする。これにより

\[
X\longrightarrow Z_f\hookrightarrow Y
\]

がschematically dominant eventとexact closed eventへ分解される。

さらに次の標準分解をAAT law geometryへ持ち上げる。

- graph factorization：\(X\to X\times_SY\to Y\)
- Zariski Main factorization：quasi-finite eventをopen eventとfinite eventへ分解
- Stein factorization：proper eventをconnected-fiber eventとfinite eventへ分解
- compactification：finite-type separated eventをopen eventとproper eventへ分解

finite locally free exact eventにはtrace、norm、discriminantを付与する。例

\[
k[t]\longrightarrow k[x],
\qquad t\longmapsto x^2
\]

ではdegree、ramification locus、discriminant \(4t\) が一つのevent invariantになる。

valuative criterionもlawful locusへ移る。valuation ring \(V\) とfraction field \(K\) によるdiagramの
liftの存在をproper event、一意性をseparated eventの性質として扱う。これによりgeneric pointから
special pointへのlawful specializationがeventの幾何学的性質として分類される。

最後にfpqc descentを構成する。scheme、decoration、law reading、generated ideal、event mapが
Čech cocycleを満たすとき、local law-compatible eventはglobal eventへ貼り合わさる。ideal inclusionと
exact equalityもfaithfully flat base change後に検査できる。

### 19.3 Architecture correspondence、partial event、event completion

一般のrelational architecture eventをlaw-compatible span

\[
\mathfrak X
\xleftarrow{p}
\mathfrak C
\xrightarrow{q}
\mathfrak Y,
\qquad
q^*_{\mathrm{ideal}}\mathcal I_Y
\subseteq
p^*_{\mathrm{ideal}}\mathcal I_X
\]

として定義する。通常のscheme morphism \(f:X\to Y\) はgraph span

\[
X\xleftarrow{\operatorname{id}}X\xrightarrow{f}Y
\]

として埋め込まれる。

二つのspanの合成はfiber product

\[
(X\leftarrow C\to Y)
\circ
(Y\leftarrow D\to Z)
=
(X\leftarrow C\times_YD\to Z)
\]

で定める。apex間の可換射を2-morphismとすれば、law correspondenceのbicategoryが得られる。
exact correspondenceでは

\[
C\times_X X^{\mathrm{law}}
\cong
C\times_Y Y^{\mathrm{law}}
\]

となる。

open immersion \(U\hookrightarrow X\) を左脚に持つspanをpartial eventとし、dense open上の同値類から
rational event \(X\dashrightarrow Y\) を作る。partial eventのgraph closure

\[
\overline{\Gamma_f}\subseteq X\times Y
\]

をevent completionとする。rational map

\[
\mathbb A^2\dashrightarrow\mathbb P^1,
\qquad
(x,y)\longmapsto[x:y]
\]

のgraph closureは

\[
V(xv-yu)
\cong
\operatorname{Bl}_{(x,y)}\mathbb A^2
\]

である。これによりblow-upはrational eventのcanonical completionとしても現れる。

derived段階では合成を \(C\times_Y^{\mathbf R}D\) に置き換える。さらに

\[
K\in\operatorname{Perf}(X\times Y)
\]

をkernel eventとし、Fourier--Mukai型convolutionによって合成する。graph、closed correspondence、
derived supportを同じoperator calculusへ統合できる。

### 19.4 Arithmetic family、specialization、formal completion

算術base \(S\) 上のlaw geometry family

\[
p:\mathfrak X\longrightarrow S
\]

を考える。DVR \(R\)、一様化元 \(\pi\)、fraction field \(K\)、residue field \(k\) に対し、
generic fiberとspecial fiberを

\[
X_\eta=X\times_RK,
\qquad
X_s=X\times_Rk
\]

とする。generic lawful locusのclosureはideal saturation

\[
I^{\mathrm{sat}}
=
I:\pi^\infty
\]

によって切り出される。最小例

\[
A=R[x],
\qquad
I=(\pi x)
\]

ではgeneric fiberのlaw idealは \((x)\)、naive special fiberのidealは \((0)\)、generic closureの
special fiberは再び \((x)\) となる。この差は \(\pi\)-torsionと

\[
\operatorname{Tor}_1^R(A/I,k)
\]

によって測られる。

中心定理系列は次である。

- generic lawful closureと\(\pi\)-saturationの一致
- flat quotientに対するsaturationの安定性
- specialization defectとTorのcomparison
- exact law transportとgeneric / special fiber形成の交換
- Fitting idealによるdegeneration locusの構成

lawful closed immersion \(Z=V(I)\hookrightarrow X\) に沿うformal completion

\[
\widehat X_Z
=
\varprojlim_nV(I^{n+1})
\]

は全infinitesimal neighborhoodを保持する。associated graded

\[
\operatorname{gr}_I\mathcal O_X
=
\bigoplus_{n\ge0}I^n/I^{n+1}
\]

をnormal coneへ接続し、completion、Rees algebra、blow-upを一系列にする。

Henselian liftingでは、compatibleなfinite-order lawful section towerをformal sectionへ持ち上げる。
formal smooth eventはliftの存在、formal étale eventはunique liftを与える。jet scheme

\[
J_n(X)(T)
=
\operatorname{Hom}
\left(T\times\operatorname{Spec}k[t]/(t^{n+1}),X\right)
\]

とarc spaceはeventの高次germとlaw idealへのcontact orderを表現する。

### 19.5 Rees、normal cone、log、toric、tropical geometry

law-generated center \(Z=V(\mathcal J)\subseteq X\) に対しRees algebra

\[
\mathcal R(\mathcal J)
=
\bigoplus_{n\ge0}\mathcal J^n
\]

を作り、blow-upをrelative Projとして構成する。

\[
\operatorname{Bl}_ZX
=
\operatorname{Proj}_X\mathcal R(\mathcal J).
\]

中心idealがinvertibleになるeventが一意にblow-upを経由するという普遍性を、AAT repairの中心定理にする。
centerはobstruction support、singular locus、conormalのFitting ideal、non-transverse law intersectionから生成する。

deformation to the normal cone

\[
\operatorname{DNC}_Z(X)\longrightarrow\mathbb A^1
\]

はgeneric fiberに \(X\)、special fiberに

\[
C_ZX
=
\operatorname{Spec}_Z
\bigoplus_{n\ge0}\mathcal J^n/\mathcal J^{n+1}
\]

を持つ。law idealもfamilyへ持ち上げ、special fiberでinitial law geometryを得る。

divisorial valuation \(\nu_E\) によりlaw idealの各birational directionにおけるvanishing orderを測る。
これからexact ideal equality、integral law equivalence、reduced support equalityを分離する。

degeneration divisorとexceptional divisorをlog structureとして保持し、log architecture scheme

\[
(X,M_X,\mathcal I_U)
\]

を作る。family \(xy=t\) はspecial fiberにnodeを持ちつつ、標準chart

\[
\mathbb N\longrightarrow\mathbb N^2,
\qquad1\longmapsto(1,1)
\]

の下でlog smooth eventになる。

monomial / binomial law geometryはtoric scheme \(X_P=\operatorname{Spec}k[P]\) とfanに持ち上げる。
fan subdivisionがtoric blow-upを、tropicalizationがvalued law equationのpiecewise-linear skeletonを与える。
stability parameterに依存するmoduliでは、wall crossingを

\[
\mathcal M_U^{\theta_-}
\longleftarrow
\mathcal Z
\longrightarrow
\mathcal M_U^{\theta_+}
\]

というcorrespondenceとして表す。

### 19.6 Derived lawful locus、event stack、spectral enhancement

Atomから得たlaw algebraを \(A_X\)、Law presentationをperfect moduleとmap

\[
\lambda_U:P_U\longrightarrow A_X
\]

で表す。derived lawful algebraを

\[
A_X/\!/\lambda_U
:=
A_X
\otimes^{\mathbf L}_{\operatorname{Sym}_{A_X}(P_U)}
A_X
\]

と定義する。二つのalgebra mapは \(\lambda_U\) とzero sectionから得る。

derived lawful scheme

\[
\mathfrak X_U^{\mathrm{law,der}}
=
\operatorname{RSpec}(A_X/\!/\lambda_U)
\]

にはclassical truncation theorem

\[
t_0\mathfrak X_U^{\mathrm{law,der}}
\simeq
\operatorname{Spec}(A_X/I_U)
\]

とKoszul homology comparisonを与える。

post-foundation reference modelには

\[
A=\mathbb Z[x],
\qquad
(f_s,f_w)=(x,x(x-1))
\]

を使う。classical quotientは \(\mathbb Z\) だが、Koszul complexは

\[
H_1(K(A;x,x(x-1)))\cong\mathbb Z
\]

を持つ。strong lawがweak lawを含意する依存関係がderived lawful geometryに残る。

architecture eventをring map \(\varphi:A_Y\to A_X\) とpresentation map

\[
\alpha:P_Y\otimes_{A_Y}A_X\longrightarrow P_X,
\qquad
\lambda_X\alpha=\varphi^*\lambda_Y
\]

として定義すると、derived lawful eventのidentity、composition、base changeが得られる。

event全体はcompatibility defectのderived zero locus

\[
\mathbb R\operatorname{Event}_U(X,Y)
=
Z^{\mathbf R}(\lambda_X\alpha-f^*\lambda_Y)
\]

としてmapping stackを形成する。そのtangent complexはlinearized defect mapのhomotopy fiberである。

quasi-smooth derived lawful moduliからcanonical perfect obstruction theory、virtual structure sheaf、
virtual fundamental classを生成する。obstruction theoryはAtom、Law、derived zero locusのprovenanceから得る。

長期的にはbaseをconnective \(E_\infty\)-ringへ持ち上げ、spectral Atom algebraとspectral lawful schemeを
構成する。\(\pi_0\) はclassical law algebra、higher \(\pi_i\) はLaw syzygyとhigher coherenceを保持する。

### 19.7 Six operations、bivariant intersection、K-theory、motive

各law geometry \(X\) にstable coefficient category

\[
\mathscr D_{\mathrm{AAT}}(X)
\]

を割り当て、architecture eventに

\[
Lf^*,\quad Rf_*,\quad Rf_!,\quad f^!,\quad
-\otimes^{\mathbf L}-,\quad R\mathcal Hom
\]

を対応させる。quasi-coherent realizationとconstructible étale realizationを分けて構成し、
base change、projection formula、localization triangleをlawful squareへ接続する。

lawful immersion \(i:L\hookrightarrow X\) と補集合 \(j:U\hookrightarrow X\) に対するtriangle

\[
Rj_!j^*E
\longrightarrow
E
\longrightarrow
Ri_*i^*E
\longrightarrow
\]

はambient、lawful、law-deviation geometryを一つのexact calculusに置く。

proper event、flat event、lci eventへpushforward、pullback、refined Gysin mapを割り当て、bivariant AAT theoryを作る。
二つのlawful lociのintersection multiplicity、excess bundle、cycle classをChow groupで保持する。
例

\[
V(y)\cap V(y-x^2)
\subseteq
\mathbb A^2_k
\]

は原点にlength \(2\) を持つ。

lawful locusのcoherent classを

\[
\kappa_L(X)
=
[\mathcal O_L]\in G_0(X)
\]

とし、derived intersectionにはvirtual law class

\[
\sum_i(-1)^i
[\operatorname{Tor}^{\mathcal O_X}_i(\mathcal O_{L_U},\mathcal O_{L_V})]
\]

を割り当てる。K-theoryとChow theoryをChern characterとRiemann--Rochで接続する。

さらにlawful locusのmotive \(M(X^{\mathrm{law}})\) とcompact-support motiveを構成する。
localization、Künneth、blow-up formula、各cohomological realizationとのcompatibilityにより、
motiveをarchitecture geometryのuniversal cohomological signatureとして使う。

### 19.8 Singularity category、degeneration residue、event dynamics

singular lawful scheme \(L\) にsingularity category

\[
D_{\mathrm{sg}}(L)
=
D^b_{\mathrm{coh}}(L)/\operatorname{Perf}(L)
\]

を割り当てる。law potential \(W\in\Gamma(S,\mathcal O_S)\) を持つregimeではmatrix factorization category
\(\operatorname{MF}(S,W)\) を構成し、hypersurface singularity categoryとのcomparisonを与える。

reference example

\[
S=\operatorname{Spec}k[x,y],
\qquad
W=xy
\]

にはrank-one matrix factorization

\[
k[x,y]
\mathrel{\mathop{\rightleftarrows}^{x}_{y}}
k[x,y]
\]

があり、nodeに集中するstable singularity modeを保持する。

trait上のfamily \(\pi:X\to S\) にはnearby / vanishing cycle triangle

\[
i^*K
\longrightarrow
R\Psi_\pi(j^*K)
\longrightarrow
R\Phi_\pi(K)
\longrightarrow
\]

を割り当てる。\(xy=t\) familyではvanishing cycleがspecial fiberのnodeに集中する。
critical schemeのimageからdiscriminant \(\Delta_\pi\subseteq S\) を構成し、complement上のmonodromyを
lawful fiber invariantへ作用させる。

architecture endomorphism \(f:X\to X\) のfixed schemeを

\[
\operatorname{Fix}(f^n)
=
\Gamma_{f^n}
\times_{X\times X}
\Delta_X
\]

とし、derived fixed schemeではfiber productをderived化する。periodic point multiplicity、
family中のbifurcation discriminant、dynamical zeta functionをevent iterationのinvariantとして研究する。
endocorrespondenceにも同じ構成を拡張し、repeated eventが生成するderived residueを保持する。

### 19.9 Event moduli、higher descent、gerbe、Hall algebra

test scheme \(T\) に対してevent familyを

\[
\operatorname{Map}_U(X,Y)(T)
=
\operatorname{Hom}_{\mathbf{LawGeom}_U/T}
(X\times T,Y\times T)
\]

とする。evaluationとcomposition

\[
X\times\operatorname{Map}_U(X,Y)\longrightarrow Y,
\]

\[
\operatorname{Map}_U(Y,Z)
\times
\operatorname{Map}_U(X,Y)
\longrightarrow
\operatorname{Map}_U(X,Z)
\]

を構成し、law-compatible event locusをmapping stack内のclosed substackとして切り出す。

有限表示、representable diagonal、cotangent complex、effectivity、smooth atlasを構成し、
architecture stackのArtin representabilityへ進む。automorphismを持つfamilyはquotient stack

\[
[L^m/S_m]
\]

を最初のnondegenerate modelとする。

space-valued architecture stack

\[
\mathcal A_U:\operatorname{AATSite}^{op}\longrightarrow\mathbf{Spaces}
\]

ではhypercover descentとPostnikov towerを構成する。各\(k\)-invariantはhigher gluing obstructionになる。
banded gerbeでは、global decomposition objectの存在、選択肢、automorphismをcohomologyの異なる次数へ分離する。

lawful architecture objectのextension category \(\mathcal C_U\) が得られた後は、object moduli \(\mathcal M_U\) と
extension moduli \(\mathcal E_U\) のcorrespondence

\[
\mathcal M_U\times\mathcal M_U
\xleftarrow{(s,q)}
\mathcal E_U
\xrightarrow{m}
\mathcal M_U
\]

からHall convolutionを定義する。二段filtration stackによる結合性、\(K_0\)-grading、Ext群とderived law
conflictのcomparisonがarchitecture assemblyの代数を与える。

### 19.10 Logical、Galois、homotopical、higher-algebra frontier

Atom sort、relation、operation、Law equationをgeometric theory \(T_U\) として提示し、classifying topos

\[
\mathscr B_U
=
\mathbf{Set}[T_U]
\]

を作る。任意のGrothendieck topos \(\mathscr E\) に対するinternal architecture modelは

\[
\operatorname{Geom}(\mathscr E,\mathscr B_U)
\simeq
\operatorname{Mod}_{T_U}(\mathscr E)
\]

で分類される。architecture schemeをringed realizationとして回収し、geometric formulaのsubobjectと
lawful closed subschemeのcomparison theoremを狙う。

connected lawful scheme \(L\) にはfinite étale categoryとfundamental group

\[
\operatorname{FinEt}(L),
\qquad
\pi_1^{\acute et}(L,\bar x)
\]

を割り当てる。finite étale cover、torsor、non-abelian \(H^1\)、monodromyをlawful geometry上の
local choice systemとして統合する。

motivic homotopyでは

\[
\mathcal H_U(X)
=
L_{\mathbb A^1,\mathrm{Nis}}h_{X^{\mathrm{law}}}
\]

を構成し、affine-bundle event、blow-up square、motivic cohomology、K-theoryをhomotopy-stable invariantへ送る。

Atom speciesをcolor、lawful multi-input assemblyをoperationとするcolored operad \(\mathcal O_U\) を作れば、
scheme morphismによる一入力eventに加えて、多入力architecture assemblyを扱える。factorization algebraは
disjoint open上のoperationをglobal operationへ貼り合わせる。

さらにPoisson law geometry

\[
(X,\{-,-\},\mathcal I_U),
\qquad
\{\mathcal I_U,\mathcal O_X\}\subseteq\mathcal I_U
\]

を導入すると、lawful locusがPoisson structureを継承する。potentialから生成されるLaw、Hamiltonian event、
deformation quantizationを通じてarchitecture dynamicsとlaw invarianceを同じ代数構造へ接続できる。

---

## 20. Cross-axis nondegenerate theorem packages

拡張を個別概念の列挙で終えず、複数軸を同時に発火するreference packageを作る。

### 20.1 Vertical / cartesian factorization package

\[
A=\mathbb Z[x],
\qquad
(x(x-1))\subsetneq(x),
\qquad
A\longrightarrow A_x
\]

を使い、law strengthening、exact localization、ideal extension / contraction adjunction、saturation、
canonical factorization、lawful locus functorを同じdiagram上で証明する。

### 20.2 Arithmetic specialization package

\[
A=R[x],
\qquad
I=(\pi x)
\]

を使い、generic lawful locus、naive special fiber、saturated closure、\(\pi\)-torsion、Tor、formal completion、
jet towerを接続する。

### 20.3 Rational event completion package

\[
\mathbb A^2\dashrightarrow\mathbb P^1,
\qquad
(x,y)\longmapsto[x:y]
\]

を使い、partial event、graph closure、Rees algebra、blow-up、exceptional divisor、correspondence compositionを
一つのevent completion theoremにする。

### 20.4 Derived Law dependency package

\[
A=\mathbb Z[x],
\qquad
(f_s,f_w)=(x,x(x-1))
\]

を使い、classical lawful quotient、Koszul homology、derived zero locus、conormal complex、canonical obstruction theory、
virtual K-classを接続する。

### 20.5 Semistable degeneration package

\[
xy=t
\]

を使い、generic / special fiber、log smoothness、discriminant、normal crossing、nearby / vanishing cycle、
monodromy、tropical skeletonを同じfamilyから構成する。

### 20.6 Finite branching and dynamics package

\[
t=x^2
\]

を使い、finite flat event、trace、norm、discriminant、étale open、ramification、Galois monodromy、
fixed-point collisionを接続する。

---

## 21. Expanded dependency map

拡張全体の依存関係は次のようになる。

```text
law-compatible morphism
  -> Grothendieck fibration of law geometry
  -> vertical / cartesian factorization
  -> morphism property calculus and fpqc descent
  -> scheme image / graph / compactification factorizations

decorated fiber product
  -> correspondence bicategory
  -> partial and rational events
  -> graph closure and blow-up completion
  -> derived correspondence and kernel convolution

lawful closed immersion
  -> conormal and cotangent geometry
  -> formal completion / jets / normal cone
  -> Rees / blow-up / log geometry
  -> toric / tropical / wall-crossing geometry

Law presentation
  -> derived lawful zero locus
  -> derived event mapping stack
  -> perfect obstruction theory and virtual classes
  -> derived moduli / higher descent / Hall algebra
  -> spectral enhancement

exact lawful squares
  -> six operations
  -> bivariant intersection / K-theory / Chow groups
  -> nearby and vanishing cycles
  -> motives and motivic homotopy

family and endomorphism geometry
  -> discriminant / monodromy
  -> singularity category / matrix factorization
  -> fixed and periodic schemes
  -> correspondence dynamics
```

近い研究段階では、law geometryのfibration、morphism property calculus、graph correspondence、
DVR specialization、Rees / normal cone、derived Law dependencyを優先する。これらはpost-foundationの
canonical scheme、generated ideal、lawful closed subscheme、principal-open reference modelから直接始められる。

次の段階では、formal geometry、log / tropical geometry、six operations、K-theory、event mapping stack、
singularity familyへ進む。長期的にはmotives、higher gerbes、Hall algebra、spectral AAT、classifying topos、
Poisson / factorization geometryが、AATをhigher algebraic geometry全体へ接続する。

この拡張atlasの中心命題は次である。

\[
\boxed{
\begin{aligned}
\text{law-compatible event}
&=
\text{vertical law change}
+
\text{exact geometric transport},\\
\text{partial event}
&\longrightarrow
\text{correspondence completion},\\
\text{law family}
&\longrightarrow
\text{specialization / formal / log geometry},\\
\text{Law presentation}
&\longrightarrow
\text{derived zero locus / virtual geometry},\\
\text{event action}
&\longrightarrow
\text{six operations / convolution / dynamics},\\
\text{event family}
&\longrightarrow
\text{mapping stack / higher descent}.
\end{aligned}
}
\]
