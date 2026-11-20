# 原始意味、native族、図式

## N1. 原始意味圏

### 定義 N1.1 — 宣言とmodel

小さいsort集合 `S` を固定する。宣言は次の族からなる。

- 有限列 `s₁,…,sₙ` と出力 `t` を持つoperation記号。
- 有限列上のrelation記号。
- 指定domainを持つpartial operation記号。
- 各sortの選択値記号。これはarity 0のoperationでもある。

model `A` は集合 `A_s`、実際の関数 `ω_A:∏ A_sᵢ→A_t`、実際の部分集合 `P_A⊆∏ A_sᵢ` を持つ。partial operation は部分集合 `D_A⊆∏ A_sᵢ` と関数 `D_A→A_t` の組として持つ。domainの元を別sortに置く表示では、包含 `D_A↪∏ A_sᵢ` とその単射性を保つ。空sort、空domain、非有限担体を許す。

model間の射 `h:A→B` は全sortの関数 `h_s:A_s→B_s` であり、各operationについて

```math
h_t\omega_A=\omega_B\prod_i h_{s_i}
```

を満たす。relationは `a∈P_A ⇒ h(a)∈P_B`、partial operationは `h(D_A)⊆D_B` とその上の同じ可換式、選択値は `h(c_A)=c_B` を要求する。relationの反映は要求しない。必要なときには別のreadingとして明示する。

Lawはこのデータに対する指定された式・述語であり、Lawを満たすmodelの**充満部分圏**を取る。Lawが否定・存在・全称を含む有限論理式であるときも、その充足を新しい射の制約と取り違えない。例えば `∃w.P(a,w)` を満たすmodelと、関数 `w(a)` を追加して `P(a,w(a))` を課したmodelは異なる。後者の射は選択witnessも保つ。前者から後者への標準的なsectionは主張しない。model全体について外在的に指定した条件もnative部分圏として保持するが、その係数的意味は原始解釈を指定した場合に限る。

### 定理 N1.2 — 恒等・合成とterm評価

これらのmodelと射は圏をなす。型付きterm `τ` について `h(τ_A(a))=τ_B(h(a))` が成り立つ。

**証明。** 恒等関数は各可換式と包含を保つ。二つの可換式を合成すればoperationの式が得られ、relation・domainの包含は推移的である。合成則と単位則は関数についての等式である。termは変数、選択値、operation適用の順に帰納する。partial termは、その時点で定義domainに属する入力について帰納し、domain保存が次の適用を正当化する。これは関手や幾何の存在を使わない。□

### 構成 N1.3 — Atomとgeneric ArchitectureObject

固定 `AtomCarrier U` のconfigurationは、sort `U.Atom` と `family`、`relation`、`identification` の三つのrelationで宣言する。既存 `ConfigurationHom` と同じく、射は実際の `atomMap` と三relationの順方向保存である。五座標の保存は既存の `ConfigurationHom` にないので追加しない。五座標そのものは固定carrierの読取り関数として保持する。座標も保存するreadingを選ぶ場合にだけ、それらの可換式を別に追加する。

`family` の外にある原始relationを消さない。`FamilySupported` は独立のLawであり、必要なfamilyにだけ課す。この宣言のmodelを既存configurationに組み直す写像と、各fieldを読む写像は互いに逆であり、射についても同じ三つの保存証明を読み戻す。したがって対象と全Homを回復する。

generic `ArchitectureObject` ではこれに二sort `StructureMaps`、`SelectedQuantities` とそれぞれの選択点を加える。新しい射はconfigurationの射と、二sortの選択点を保つ実際の関数の組とする。合成は N1.2 で得られる。忘却は元の二つの**型と選択値**をそのまま返す。既存 `ObjectEquivalence` の任意relationを、この新しい圏の射と同一視しない。`ObjectAlgebra.Op` のoperation添字だけから恒等・合成を推測することもしない。

opaque payload `P` はsort `P` と指定された点 `p` のまま表す。`P` に有限性、文字列としての解釈、加法を導入しない。実際の残差 `r:D→O` は関数記号、またはrelation `{(d,o) | r(d)=o}` とtotality・一意性で表す。これで任意関数が保持される。係数への拡張は[量と拡張](quantity-and-extension.md)で別に構成する。

## N4. Lensとprotocol

### 定理 N4.1 — Lensの積分解

total lensは `get:C→V`、`put:C×V→C` と

```math
\mathrm{get}(\mathrm{put}(c,v))=v,\quad
\mathrm{put}(c,\mathrm{get}(c))=c,\quad
\mathrm{put}(\mathrm{put}(c,v),w)=\mathrm{put}(c,w)
```

を持つ。`v₀∈V` があるとき `K={c | get(c)=v₀}` と置くと

```math
\phi(c)=(\mathrm{put}(c,v_0),\mathrm{get}(c)),\qquad
\psi(k,v)=\mathrm{put}(k,v)
```

は互いに逆である。積上では `get(k,v)=v`、`put((k,v),w)=(k,w)` となる。

**証明。** `φ` の第一成分が `K` に属するのは第一Law。`ψφ(c)=c` は第三Lawと第二Law、`φψ(k,v)=(k,v)` は第三Law、`get(k)=v₀`、第二Lawから従う。積上の式も同じ三式の代入である。□

相対射を `(h:C→C',u:V→V')` とし、`get' h=u get` と `h put=put'(h×u)` を要求する。両viewに基準値があるとき、積上の射はちょうど

```math
(k,v)\longmapsto(a(k),u(v)),\qquad a:K\to K',\quad u:V\to V'
```

である。実際、`get` 保存で第二成分が決まり、`put` 保存で第一成分は `v` に依存しない。逆にこの式は両保存則を満たす。合成は `(a',u')∘(a,u)=(a'a,u'u)`。同じ `V` 上で `u=id` を固定した全Homは `K→K'` に対応する。`K` は空でも任意濃度でもよい。この計算は既存 `GeneralLens.productEquiv`、`GeneralLens.normalForm`、`GeneralLens.productMap` の順序 `V×K` を入れ替えたものである。

`V=∅` なら `get` の存在から `C=∅`。空viewのlensから任意のlensへの相対射は一意である。非空viewから空viewへの相対射は存在しない。両viewが空なら一意である。`V≠∅, C=∅` は許され、基準値を選べば `K=∅` という上の分類に含まれる。viewに点がない場合を非空fiberの仮定で捨てない。

### 定理 N4.2 — Protocol

小さいexecution category `P`、N1の意味圏 `E`、観測functor `O:P→E` を固定する。modelは実際の `F:P→E` と自然変換 `α:F⇒O`、射は `β:F⇒F'` で `α'β=α` を満たすものとする。これは `[P,E]/O` である。

各対象に N1 の宣言、各射にsort map、各composable pairに合成式、恒等に単位式を置く。これらの解からfunctorが構成され、成分mapに自然性式を課した解から自然変換が構成される。全pathの作用は有限回の合成であり、圏の等しいpathには同じ作用が得られる。逆にfunctor・自然変換のfieldを読むと全ての原始式を満たす。二方向は各fieldで互いに逆で、全Homを保つ。

`P` が一点圏、`E=Set`、`O=1` なら二元集合から一点への定数写像が非単射な射を与える。二元集合の交換は非恒等自己同型である。ゆえにこの構成は射を単射や同型だけに縮めていない。

### 系 N4.3 — Copyingとdescentでの同じ比較

Lensの `φ,ψ` と相対射のnormal formは、`get,put`、射影、基準値、対角、有限合成だけで記述される。N2.1のcartesian関手でその同じ式を運ぶと、任意環上で `C_R(C)≅C_R(K)⊗C_R(V)` と係数化したnormal formが得られる。native基準値を保持したこの比較はscalar extensionと可換である。このnativeな比較dataの降下形では、overlapの基準sectionを保つlens同型が `K` を運ぶので、B1.2により比較が降下する。

より一般のcoalgebra lensでは、`p(c)=put(c,v₀)` で定まる冪等coalgebra射の像をQC coalgebra `K` とする。冪等射の像はmoduleの直和因子であり、`Δp=(p⊗p)Δ` によりその像にもcoalgebra構造が入る。`φ,ψ` の同じ式は `C≅K⊗V` を与え、QC moduleとmapのdescentで降下する。この一般の `K` 自体の局所split性は結論しない。大域基準sectionがない場合には、局所比較とその遷移を保持し、大域的に一個の積分解を選んだとはしない。

Protocolの係数化は各頂点・辺・観測mapにN2.1を適用する。path Lawと自然変換の正方形は有限合成の等式なので運ばれる。connectedな非零環ではN2.3を各頂点mapに適用し全native自然変換を回復する。局所splitなprotocol dataとその自然変換は各頂点・辺についてB1.2を適用し、path式を忠実平坦に検査して降下する。従ってこれらのnative族について、新しい係数・descent比較も同じ実際のstate/view/path mapから生成される。

## N1・N4. G-124のgeometryとの比較

geometryでは、既存の独立原始宣言を同じ入力として使う。次の順に、型付きの実際の値と関数を N1 のsort・operation・relationへ置く。

1. extraction・composition・formation、invariant・signature・operation、および係数環のcarrierと演算。
2. それらから生成される対象上のcontext、equation、circuit、coverage、overlap、raw data。
3. 射のpackage map、係数環射、各contextでのactual action、raw map、realization成分とその可換式。

依存sortは、添字sortへの射とそのfiberで表示する。たとえばcontextごとのobservableは直和 `⨿_W O_W→W` と、同じfiberで定義された環演算で表す。定義domainは N1.1 のpartial operationを使う。既存の存在命題は存在命題として保持し、選択済みpresentationは選択値として保持する。

読み戻しは宣言順の再帰で行う。第一段の出力から第二段の添字を決め、各fiberを取り、各operationのgraphから元の関数を取り出す。graphに対するtotalityと一意性が関数の存在と一意性を与える。非activeな行は既存宣言の規則どおり正規化する。これはrepresenting equivalenceを入力にせず、各fieldを構成する操作である。

具体的には `IndependentGeometryPrimitiveAssembly.assemble` がこの順序で対象を構成する。対象同定と全Homの逆写像は `IndependentGeometryCategoryReconstruction`、`IndependentGeometryHomNativeFullRecovery` の原始data上の組立て・読み戻しを使う。representative modeでは `GeomReadCategory`、explicit modeでは `ExplicitExactGeomCategory` を返す。特に後者のraw mapと全context actionを落とさない。既存の `ULiftHom` はuniverseだけを揃え、Hom集合を変えない。

この宣言を copying 化すると、全sort mapは [N2](copying-and-totality.md) のcoalgebra射となる。connectedな非零環ではgraphの全行が元の関数に戻るので、上の逆写像がそのまま全native Homを回復する。任意環での追加のidempotent分割は元の写像に潰さず保持する。既存の対象・射の再構成だけを、相対Specや係数にわたる表現性の証明として用いない。

## N5. 図式、全補完候補、評価

### 定義 N5.1 — 図式の原始表示

小さい圏 `J` の各対象に宣言を置き、各射に型付きsort mapと N1.1 の保存式を置く。異なる宣言間では指定されたreadingに沿って型を解釈する。各恒等・合成に対応する式を課す。生成射と関係による表示を使う場合は、全pathを有限語として作り、与えた関係の合同閉包で同一視する。すでに与えた圏 `J` の表示として使うには、その合同商が `J` であることを入力の表示条件とする。

対象間の比較には各頂点の全sort mapを新しい変数として加え、各辺について自然性正方形を課す。termとして表せるmapだけに制限しない。ここまでの解を `Diag_prim(J)` とする。読取りと組立てにより、独立に定義された意味図式の圏 `Diag_sem(J)` と同型になる。証明は N4.2 と同じfieldごとの逆写像であり、辺の式からpathの式への帰納が関係による商を正当化する。

### 定義 N5.2 — 許容規則と固定部分

`K↪J`、固定図式 `F`、許容規則の集合 `H` を与える。`H` の要素は変更後の宣言、型対応、有限term代入、補助sortの宣言を持ち、その構文的適用条件を指定する。候補は次の**データ全部**である。

```math
(h\in H,\ A\in\mathrm{Diag}_{\mathrm{prim}}(J;h),\ c:A|_K\to F)
```

比較の向きや同型性が規則に指定されていればその指定を使う。共有規則係数、語翻訳、補助選択も `h,A,c` のfieldとして保持する。候補間の射は実際の頂点mapで、図式関係・固定比較・指定された共有dataを保つものとする。許容規則に複数の語翻訳があれば、それらを評価値が等しいだけで同一視しない。

意味側でも、同じ宣言編集を実際の担体・演算に施し、全図式と固定比較を独立に定義する。N5.1 の同型は固定比較の各fieldも保つため、候補の圏に同型を誘導する。これは全候補を列挙できるというアルゴリズム上の主張ではない。任意の小さい候補familyはこの集合論的構成に含まれる。

### 定理 N5.3 — 自然性と評価一致

図式形 `J'→J` に沿う制限は頂点・辺の添字を引き戻す。固定部分の制限は `c` を制限する。`H⊆H'` は候補dataをそのまま含める。係数変更は各係数構造をtensorまたはcopyingのscalar extensionで運ぶ。それぞれ原始表示の組立てと可換である。

**証明。** 前三者では各fieldへの作用が両経路で同じである。係数変更ではoperation評価の可換性を N1.2 のterm帰納法と N2 または係数的実現のtensor同型で示す。単位・合成のcoherenceはpure tensorまたはbasis上で一致し、それらが加群を生成するので全体で一致する。□

評価は、同じ候補のquantity、操作語、状態比較から有限式を評価して得る。語の長さと式に関する帰納法により、原始候補の評価と組み立てた意味modelの評価は一致する。候補を回復する同型と、評価値への忘却map `ev` は別のmapである。例えば異なる補助sortを持つ二候補が同じscalarを返しても、候補同型は自動的には生じない。このデータが G-140 の条件付きfiberと全補完の2-fiberへの入力となる。
