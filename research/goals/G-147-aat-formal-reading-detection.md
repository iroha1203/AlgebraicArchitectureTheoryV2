# G-147-aat-formal-reading-detection — 原始Lawからの変形比較と最初の不成立次数

- `id`: `G-147-aat-formal-reading-detection`
- `status`: `draft`
- `research mode`: `target-theorem`
- `tracking issue`: [#6359（設計）](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/6359)。個別のResearch Loop Issueはactive化時に定める。
- 設計: [多項式特殊化ノートの変形比較](../../docs/note/n1020_shigure_polynomial_specializations.md#formal-reading)
- 依存: [G-140](G-140-aat-independent-realization-descent.md)、[G-141](G-141-aat-semantic-scheme-representability.md)、[G-142](G-142-aat-shigure-reading-naturality.md)、[G-146](G-146-aat-semantic-lift-and-repair-comparison.md)

主経路は[n1019](../../docs/note/n1019_shigure_representability_design.md)のG-149〜G-152にある。
本カードは多項式特殊化を構成する。主経路と同じ対象・射・Law評価への比較を要し、
本カードの達成だけでSHIGURE全体の達成とはしない。

## 研究目的

補助演算を追加する変更と、その演算へLawを追加する変更を区別し、観測する実現の
どの変形まで保存されるかを原始式から決定する。追加Lawの消去ideal、そのidealの
極大idealに関する次数、実際の係数環拡大に対する持ち上げ、合法な局所修復の障害を
同じ実現と比較写像で結ぶ。自由な観測係数では、検査すべき次数の上界を原始構文から
生成し、その上界を達成する例を構成する。

G-141・G-142の表現可能性とreadingの自然性から進み、G-146が扱う一つの平方零拡大を、
全局所Artin係数上の変形の比較に接続する。固定次数の判定対象は、指定したreadingと
実現点における、指定冪零次数以下の全係数変形である。全係数代数上の意味同値との
相違は、Bの全次数判定とWの有限・無限の指定例によって決定する。

## 固定target

### A. 三角的な補助演算の消去とreadingの像

量化順は、可換環k、ノートの原始表示O、以下の原始追加から得る表示P、k代数Rとする。
OとPは同じ型・階数・名前付き生成元を持つ。Pには有限個の補助tensor演算Y₁,…,Y_sと、
同じ入出力型の有限式によるrequired Law

```math
Y_j=F_j(O,Y_1,\ldots,Y_{j-1})\qquad(1\le j\le s)
```

を置く。さらに有限個のrequired Law G_α=0を追加する。Oの演算をそのまま読む代入
u:O→Pを作り、補助演算の順序に沿ってG_αを代入し、Oの演算だけの残差Ḡ_αを生成する。
式・型・Lawの出現と導出は保持し、Sem間の写像、closed immersion、消去の同型を入力にしない。

全Rについて、原始演算の復元と消去から自然な同値

```math
\operatorname{Sem}_P(R)\simeq
\{a\in\operatorname{Sem}_O(R)\mid\overline G_\alpha(a)=0\text{ for all }\alpha\}
```

を構成する。Realではu*がfull faithfulであり、同じ残差の零点がessential imageに
なることを、全ての演算保存同型について証明する。特に自己同型群の比較は同型になる。
残る追加Lawが空の場合は、同じ消去が全R上の同値を与える。

G-141の各chartでḠ_αの全成分が生成するidealを作る。基底変更でtensor残差が変換する
ことからideal sheaf 𝒥_uを生成し、M_P→M_Oがその閉部分schemeになることを証明する。
任意のk代数射との自然性、原始表示の改名、相互にLaw導出を持つ冗長Lawの追加・削除、
定義だけの補助演算の追加・消去との整合を含める。

### B. 全局所Artin試験による最初の不成立次数

B–Dではkを体とし、O・Pの演算とLawを有限とする。x∈Sem_P(k)、a=u*xを選ぶ。
A=𝒪_{M_O,a}、mをその極大ideal、J=(𝒥_u)_aとし、有限表示からAのNoetherian性を得る。
xが存在するのでJ⊆mである。

Art_k^{≤r}は、剰余体をkと同定した局所Artin k代数Rで、極大ideal n_Rが
n_R^{r+1}=0を満たすものの圏とする。Def_{O,a}(R)はaへ還元されるSem_O(R)の実現、
Def_{P,x}(R)はxへ還元されるSem_P(R)の実現とする。全てのr≥0について次を証明する。

```math
\begin{aligned}
&\operatorname{Def}_{P,x}|_{\operatorname{Art}_k^{\le r}}
 \longrightarrow\operatorname{Def}_{O,a}|_{\operatorname{Art}_k^{\le r}}
 \text{ が自然同値}\\
&\quad\Longleftrightarrow J\subseteq\mathfrak m^{r+1}\\
&\quad\Longleftrightarrow
 A\longrightarrow A/\mathfrak m^{r+1}
 \text{ が与える普遍観測変形が }P\text{ の実現へ持ち上がる}.
\end{aligned}
```

A/m^{r+1}がArt_k^{≤r}に属すること、局所環の写像からG-141の同じ実現を得ることも
構成義務に含む。kのdual numbers、曲線に沿う変形、有限個のサンプルを全試験環の代わりにしない。

J≠0のときν_a(u)=max{n∈ℕ | J⊆m^n}、J=0のときν_a(u)=∞と定める。
Krull交叉から最大値の存在を証明し、r<ν_a(u)では比較が同値、r=ν_a(u)<∞で初めて
同値でなくなることを示す。全rでの一致、J=0、およびaのあるopen近傍上でM_P→M_Oが
同型になることの同値を証明する。全R上の同値は、Aで構成したideal sheaf 𝒥_uの
零性で判定し、点aでのJ=0と区別する。

判定対象は全Artin代数であり、k[t]/(t^{r+1})型の曲線jetの試験とは別に定義する。
[de Fernex–Ein–Ishii](https://arxiv.org/abs/1704.07494)、
[Mallory](https://arxiv.org/abs/1811.12577)、
[Chen–Zuo](https://arxiv.org/abs/2507.05796)のjet closure・jet indexとの比較では、
各々の試験対象と量化を対応させる。全Artin試験のBを曲線jetの判定へ置き換えない。
jet schemeは任意のk代数Tに対するT[t]/(t^{r+1})値点を表すため、先行研究をk値の
曲線サンプルだけの判定と読まない。本条項の局所Artin R全体、augmentation、普遍商との
比較を、この係数Tを含む量化と照合する。

### C. 初回の平方零障害と合法な局所修復

ν=ν_a(u)<∞について、

```math
R=A/\mathfrak m^\nu,\qquad
R'=A/\mathfrak m^{\nu+1},\qquad
I=\mathfrak m^\nu/\mathfrak m^{\nu+1}
```

を構成する。R′→Rが平方零拡大であること、R上の普遍観測変形がPへ持ち上がることを
示す。指定された普遍観測lift A→R′の残差から非零写像

```math
\kappa_u:J/J^2\longrightarrow I,\qquad
f\longmapsto f\bmod\mathfrak m^{\nu+1}
```

を構成し、G-146 Cの同じ指定観測liftに対する障害へ送る比較を証明する。
ν≥2の場合は、観測lift間の差となるderivation A→IがJを零に送ることを導き、
R上のこのP実現がR′へ持ち上がらないことも示す。ν=1の場合の結論は、指定観測liftの
不成立である。基点自身の定値liftと、指定観測方向のliftを区別する。

消去した各tensor残差Ḡ_αと同じ入出力型の補助tensor演算Z_αを追加し、OとZ_αを共有する
二文脈を作る。左にZ_α=Ḡ_α、右にZ_α=0を置く。交差はOとZ_αを持つ。
原始宣言の合併から、この表示の実現が追加Law Ḡ_α=0の実現に一致することを証明する。
その後、同じ基底chartで残差とZ_αの成分をf₁,…,f_qおよび対応する共有座標にする。
成分多項式を元のtensor式と対応させ、座標関数を原始演算として受け取らない。

Art_k内の平方零拡大R′→R、x_R∈Def_{P,x}(R)、u*x_Rの指定観測lift ãについて、
左右の局所liftを実際に構成する。残差写像κ_u(ã):J/J²→Iをf↦ã(f)で生成し、
初回の普遍liftでは上のκ_uになることを示す。
観測を固定し局所Lawを保つderivationを修復係数とし、共有部の差
δ=(f_i(ã))∈I^qをČech cocycleとして得る。全syzygyから自然な単射

```math
\operatorname{Hom}_{A/J}(J/J^2,I)\longrightarrow I^q
```

を構成し、κ_u(ã)をδへ送ること、像をsyzygyの消滅で特徴づけること、零性を反映することを
証明する。Iには実現を介したA/J加群構造を使う。自由なLaw座標I^q全体と、この像を
区別し、G-146の同じ被覆・合法修復係数・障害類へ接続する。
ここで扱う係数環への実現liftと、conormalのsection liftとの型の区別はG-146 Eに従う。

### D. 表示・生成元・合成との整合

J、ν、κ_uとCの比較が、chartの変更、生成元の改名、相互の導出を伴うLaw表示の変更、
定義だけの補助演算の追加・消去で整合することを証明する。生成idealとconormalの写像を
構成し、Lawの個数や選んだsyzygy生成族にνと実際の障害の零性が依存しないことを示す。

二つのAの型のreading u:O→P、v:P→Qは、定義順序を連結して同じ型のreadingに合成する。
Qのk値実現を選び、各観測点の局所環をA、A/J_u、A/J_{vu}と同定する。
P上の追加ideal J_vを生成し、J_{vu}がそのAへの逆像であることから

```math
\nu(vu)=\min\{\nu(u),\nu(v)\}
```

を証明する。各νは対応する実現点と局所環で計算し、∞を含む。普遍変形、
idealの写像、相対liftと残差の比較についても恒等・合成との可換性を示す。

Realのpointed deformationは、剰余体上の実現への還元同型を保持したgroupoidとして
独立に構成する。Aのfull faithfulnessと、局所Artin環上で生成元qを持ち上げられることを
原始加群から証明し、Bの同値判定が同じunmarked実現のpointed deformationにも一致する
ことを示す。生成元数m_v≥n_vとqの選択を変えても、この判定とνが一致することを導く。
この比較対象はνとpointed Realであり、各marked schemeは選んだ生成元のデータを保持する。
自己同型とその還元kernelを保持し、指定観測liftに対する相対fiberが空またはcontractible
になることをAから証明する。相対修復の自由度を絶対自己同型群と同一視しない。

### E. 構文からの有限上界と係数変更

観測chartが自由な係数B=k[z₁,…,z_d]である場合、k値の基点を原点へ移す。
原始式の成分多項式に対して、変数に1、定数に0、積に次数上界の和、和に最大を割り当てる。
補助定義の依存順序に沿って代入し、消去後の残差の次数上界Dを生成する。
式の評価との一致とdeg f_i≤Dを証明し、

```math
J\ne0\Longrightarrow\nu_a(u)\le D
```

を示す。したがってD次までのBの全Artin比較から、この自由chart上の追加idealが零か
どうかを判定できることを証明する。既存Lawを持つ観測環には、その関係を含む別の次数
計算が必要であることをW5の同じ原始入力で検査する。

係数変更については、可換環k₀上のaugmentation B₀→k₀、m₀をそのkernel、
消去ideal J₀⊆m₀を持つ同じ構成を使う。B₀/m₀^{r+1}と
B₀/(J₀+m₀^{r+1})が任意のk₀→k₁によるbase changeと交換することを証明する。
両者の写像のkernelをD_rとすると、変更後のkernelは
D_r⊗_{k₀}k₁→(B₀/m₀^{r+1})⊗_{k₀}k₁の像であることを示す。
flatな変更でのkernel比較同型、faithfully flatな変更での零性反映を証明する。
このaugmentationに沿う冪零商の主張と、Bの剰余体kを持つ局所Artin試験を区別する。

### W. 同じ原始構成を通す指定例

W1–W6は一型、rank 1、生成元数1の単項演算から構成する。W7はノートの主例の
一型の係数表示からrank 1型D,B,Cのコピーを作る。W1–3・W5・W6ではkを体とする。
W1–W5・W7は該当するA–Eの構成へ通す。
W4の整数環はEのaugmentationの系、その各体への特殊化はB–Dで扱う。

1. **局所liftは存在するが組み立たない例。** 観測演算T、左文脈Y=T²、右文脈Y=0、
   交差T,Y、基点T=Y=0を取る。全ての体kについてR=k[ε]/(ε²)上の
   T=ε,Y=0は大域実現になる。R′=k[ε]/(ε³)への任意の観測lift
   T=ε+aε²では、左Y=ε²、右Y=0となる。合法な相対修復係数が
   C⁰=0、C¹=(ε²)であること、κ_uと[ε²]の一致、ν=2を証明する。
2. **二次Lawの鎖。** 任意のN≥1について、Y₁=T²、Y_{j+1}=Y_j²、Y_N=0を置く。
   消去idealが(t^{2^N})、ν=2^Nであり、Eの再帰的上界を達成することを示す。
   2^N−1次までの全Artin比較と、k[ε]/(ε^{2^N+1})への初回の持ち上げ不能を
   同じ実現から証明する。
3. **冗長Lawとsyzygy。** 残差(t²)と(t²,t³)を比較する。syzygy(t,−1)から、
   原点でのcanonicalなconormalの双対がI⊕Iの第一成分へ入ることを示す。
   νと実際の障害が一致し、二本の零Jacobianだけから得るI⊕I全体とは異なることを証明する。
4. **非flatな係数変更。** k₀=ℤ、B₀=ℤ[t]、J₀=(2t²+t³)、augmentation t↦0を取る。
   (t)-adic orderがℤ上とℚ上で2、F₂上で3になることを証明する。
   r=2ではD₂=2ℤt²なのでD₂⊗F₂≠0だが、変更後のkernelは零であることを示し、
   Eの像による比較と一致させる。
5. **観測環の既存Law。** 任意のN≥1について、観測にY=T^N、追加LawにY=0を置く。
   原点の局所環でYの次数がNであることを示す。追加Lawの表示上の次数1だけでは
   Bの判定次数が決まらず、既存Lawの消去を含めると同じν=Nを得ることを証明する。
6. **無限入力で全有限変形が一致する例。** 可算な演算T_iとLaw T_i=T_{i+1}²を置く。
   A_∞=colim k[t_i]、移行写像t_i↦t_{i+1}²を、同じ原始表示の座標環として構成する。
   全T_i=0の点の局所環でm=m²、t₀≠0を証明する。Law T₀=0を追加しても
   全局所Artin原点変形が定値であり、その比較が全次数で同値になることを示す。
   一方、A_∞が整域、A_∞/(t₀)でt₁が非零かつ平方零であることから、両schemeが
   同型でないことを証明する。この例はG-141の小さい無限入力を使い、Bの有限表示の
   入力とは区別して、同じ消去と実現の生成経路で検査する。
7. **台帳移行で生じる初回障害。** [同じ台帳の主例](../../docs/note/n1020_shigure_polynomial_specializations.md#ledger-example)の
   p=(1,1)、i=(λ,1−λ)、j=μ(1,−1)を用い、δ=1−λとする。公開before状態はx、
   apply_u(x)=x+uである。afterには有限phase graph Idle / Busyを置き、
   Idleのambient状態を(B,C)∈R²、Busyのambient状態を(B,C,h)∈R³とする。
   以下の写像を同じ原始演算の有限式から生成する。

   ```math
   \begin{aligned}
   \operatorname{begin}(B,C)&=(B,C,C),\\
   \operatorname{apply}^{\rm Idle}_u(B,C)&=(B+\lambda u,C+\delta u),\\
   \operatorname{apply}^{\rm Busy}_u(B,C,h)&=(B+\lambda u,C+\delta u,h),\\
   \operatorname{finish}(B,C,h)&=(B+\mu h,(1-\mu)C).
   \end{aligned}
   ```

   beginはIdleからBusy、finishはBusyからIdle、applyは各phase内の操作とする。
   同時に開始できるcompactorは一つで、Busy内のbeginは許さない。applyとfinishは
   この操作言語の原子操作であり、readは両phaseでB+Cを返す。begin・finishはbeforeの
   空語、apply_uはbeforeのapply_uへ送る。初期状態は任意のIdle状態でx=B+Cとする。

   任意の可換環R、λ,μ∈Rについて、phaseが許す全有限操作列の全readでbeforeとafterが
   一致することとμδ=0が同値であることを証明する。beginからfinishまでのbusy applyの
   入力の総和をUとすると、finishの観測差が−μδUになる式を生成する。
   十分性はIdleでx=B+C、Busyでx=B+Cかつμ(h−C)=0という関係から、各操作と全有限語へ
   帰納する。必要性はIdle(0,0)からbegin; apply_1; finishを実行し、read=1−μδを得る。

   有限局所自由のcarrierはambient R²・R³とする。Busyの合法状態は、G-140・G-142で
   定める追加の0引数state宣言とLaw μ(h−C)=0の実現fiberから生成し、原始式による
   closureを証明する。任意のR³上でfinishの観測保存を要求すると、(B,C,h)=(0,0,1)
   からμ=0が必要になることも示す。これに対してλ=1,μ=1は上の到達不変量を保ち、
   全有限操作列で意味を保存する。同じ例で、全ambient状態の保存への過剰な変更を検査する。

   係数表示Oはrank 1・生成元数1の一型Dと単項λ,μ、required Lawなしから作る。
   このmarked実現からDの三つのコピーを作り、p=(id,id)、i=(λ,id−λ)、j=(μ,−μ)を生成する。
   G-140 Fの自然同型によりM_O≃A²と元の台帳の固定pのmarked fiberを対応させる。
   固定pを元の三型のtensor Lawだけで定義したとは扱わず、この同型をunmarkedへ自動移送しない。
   このOへ補助演算E=μ∘(id−λ)とLaw E=0を追加してPをAの経路で生成する。
   消去ideal J=(μδ)、M_P≃Spec k[δ,μ]/(μδ)と、protocol係数の意味保存fiberへの同型を構成する。
   体k上では二つの座標軸の合併で
   原点が特異点であること、基点δ=μ=0でν=2であることを証明する。
   δだけ、μだけを変える二方向は全次数へ延長できる一方、R=k[ε]/(ε²)上の
   δ=μ=εはR′=k[ε]/(ε³)へ延長できない。任意の候補δ=ε+aε²、μ=ε+bε²で
   E=ε²となり、上のambient操作列のreadが1−ε²となることを同じ式から示す。

   Cの二文脈をこの台帳に適用し、左をE=μδ、右をE=0、共有観測をδ,μとする。
   R上では整合する大域実現があり、R′上では左右の局所liftが各々存在するが、
   合法な相対修復係数C⁰=0、C¹=(ε²)の中に非零障害[ε²]が残ることを示す。
   同じκ_u、ν、具体的なread差の符号を含めて対応させる。

   修正したfinish_snap(B,C,h)=(B+μh,C−μh)も同じ原始式から構成する。
   修正後はBusyの状態Law μ(h−C)=0を除き、Busyを全ambient R³、比較関係をx=B+Cとする。
   R=ℚで旧状態Lawを残すとδ=μ=1でbegin; apply_1が閉じないことも検査する。
   固定pのコピー同定を使い、compact_all(B,C)=compact_{C}(B,C)=(B+μC,(1−μ)C)を
   状態から引数を選ぶ派生原子操作として定義する。applyを挟まないbegin; finishと
   begin; finish_snapはこのcompact_allを実現するが、固定引数compact_tとは同一視しない。
   k=ℚ、μ=1でcompact_allは非単射、固定引数compact_tとその固定有限語はtranslationとなる
   ことを反例として示す。finish_snapを使うprotocolは全λ,μでphaseが許す全有限語のreadを
   保存することを証明する。
   μδ=0を満たす旧係数上では、旧合法Busyの包含が各遷移と可換であることを証明する。
   特にμ(h−C)=0上では両finish自体が一致する。係数の閉埋め込みV(μδ)→A²と、この状態包含を
   同じ原始式から生成する。
   これにより、元の原子操作の係数族SL₂×A¹とその固定pの族を保ったまま、
   snapshot後の更新を消す実装と、同じsnapshot量だけを差し引く実装を比較する。

## 前提・構成台帳

| 対象 | 役割 | 出所・構成義務 | 使用先 |
| --- | --- | --- | --- |
| 原始表示O、補助演算の定義順序、有限式と追加Law | 入力として保持 | A。演算・式・Law導出からreadingを作る | A、E、W |
| 独立Sem・Real、表現scheme、reading自然性 | 先行構成 | G-140・G-141・G-142の同じ実現 | A–D |
| 消去、残差ideal、閉埋め込み、full faithfulness | 構成・証明義務 | Aの原始代入とtensor残差 | B–E |
| 有限表示、体、k値実現 | 一般定理の仮定 | B。Noetherian性とArtin商の有限性を証明 | B–D |
| 全Artin比較、ν、普遍試験環、初回障害 | 構成・証明義務 | B・C。Krull交叉と同じ残差を使う | D、W |
| 全syzygy、合法な相対修復係数、比較写像 | 構成・証明義務 | CとG-146。rawな自由Law座標への単射を構成 | 局所組立てと障害の同定 |
| 表示・生成元変更、合成、pointed Real比較 | 構成・証明義務 | D。Artin環上のqのliftとAのfull faithfulness | νと相対liftの自然性 |
| 自由観測係数、augmentation、flatness | 各系の仮定 | E。使用する系ごとに区別する | 有限上界、係数変更 |
| W1–W7の原始入力 | 構成・証明義務 | 同じ消去・実現・局所修復を使用。W7のphaseとstate fiberはG-140・G-142へ接続 | 固定targetの検査 |

## 完了条件

A–E・WをLeanで証明し、`research/reports/G-147-aat-formal-reading-detection.md`に
原始消去、全Artin判定、初回障害と局所修復の同定、構文上界、係数変更と指定例の
証拠を対応させる。Lean証拠は`research/lean/ResearchLean/AG/`に置き、
[共通完了基準](../../.codex/skills/target-theorem-loop/references/target-goal-contract.md#共通基準の参照適用)を適用する。

W6の反例はBの有限表示定理の反証ではなく、同じ表現可能性に含まれる無限入力についての
独立した固定成果として判定する。固定された一般主張が偽の場合は、その量化に属する
原始表示・実現・reading・試験環を構成し、破れる同値、次数、障害比較を特定して
`target-refuted`と記録する。

Krull交叉、局所環のArtin商、平方零liftの標準理論は既知の数学として用いる。
本GOALの比較は、それらの成立を原始Lawの消去、文脈支持、実際の残差から導き、
同じ生成経路の鋭い上界と不成立例へ接続することによって判定する。
