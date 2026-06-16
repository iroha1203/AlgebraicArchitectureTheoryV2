# AAT 代数幾何版本文 フルレビュー

- 対象: `docs/aat/algebraic_geometric_theory/` 全9ファイル(第I〜VII部+付録A+README、約9,600行)
- 実施日: 2026-06-11
- 方法: 多段レビュー。(1) 全8ファイルの定義・定理インベントリ抽出、(2) 各ファイル×2レンズ(本物のAG度監査/証明ギャップ監査)の精読レビュー16本、(3) critical/major 指摘への敵対的検証(数学的正しさ+原文忠実性の2観点、17評決)、(4) 主執筆者による中核ファイル(付録A、第I〜III部全文、第IV〜VI部主要定理)の独立精読と指摘の追検証。検証エージェントの評決は17件中15件が「指摘成立」、2件が反証され棄却された。棄却された指摘は本レポートに含めない。

---

## 0. 総評

**「比喩ではなく本物の代数幾何か」への答えは、階層によって異なる。**

```text
付録A の decoration principle        : 健全 (設計として正しい)
site / sheaf / ringed topos 層       : 本物 (B: 標準理論の正当な decoration)
affine chart / 単項式イデアル層       : 本物 (A: 検証済みの可換代数を含む)
architecture scheme (大域化) 層      : 未完成 (D 級の誤りを1件含む)
derived / Tor 層                     : 道具は本物、repair への接続機構は未確立
singularity / monodromy / stack 層   : 骨格は本物、固有概念の数カ所が ill-defined
representation / period / analysis 層: period の核のみ本物、残りは枠組み宣言
```

- 用語だけ借りた空虚な比喩で書かれた文書では**ない**。座標環・イデアル・零点集合・Čech複体・Tor・cotangent complex は実体を持って使われており、検算可能な計算例(擬円周の H¹≅ℤ、共有 witness の Tor₁)は**すべて正しい**(独立検算済み)。
- 一方、**定理の証明規律に系統的な弱点**がある。ラベル付き定理級主張44件のうち、本文中に実質的な証明を持つのは1件(第IV部 定理7.1)のみ。30件は主張のみ、13件は概略のみである。
- **critical 級の数学的誤りが6件**確認された(§2)。いずれも理論を殺すものではなく修復可能だが、うち2件(scheme gluing、smooth/singular 二分法)は部の中心概念に関わる。
- 実コード計測としては、**「有限 poset site + square-free witness + Stanley–Reisner + 単項式 Tor」の経路に限れば数学は計測可能性までほぼ通っている**。これが最短の実用化経路である。一般経路(任意 site、derived、monodromy、period)は計測まで2段階以上の未完成が残る(§4)。

総括すると、これは「代数幾何の言葉で書かれたポエム」ではなく、**真面目に作られた研究プログラムの設計書**である。ただし現状の完成度は「定義の塔は高く正確、定理の床板は薄い」。以下、6つの観点で詳述する。

---

## 1. 軸①: 本物の代数幾何になっているか

### 1.1 判定の枠組み

各構成を次の4分類で監査した。

```text
(A) 標準的な代数幾何としてそのまま正しい
(B) 標準理論の decoration / 非標準だが well-defined
(C) 用語だけの比喩(数学的内容が伴わない)
(D) 数学的に壊れている(ill-defined / 偽)
```

### 1.2 部ごとの判定

| 部 | 総合判定 | 根拠の要点 |
| --- | --- | --- |
| 第I部 | AG前段の公理層。(B)主体、中心概念に(C)/(D) | site/sheaf/環は未登場。ExtractionDoctrine への相対化は健全な規律だが、obstruction circuit(定義8.2)に自由変数、valuation(定義8.5)に型エラー、「algebra」(§10)は演算・等式が未提示 |
| 第II部 | (B): SGA4 流の正当な decoration | admissible cover から**生成される**最小 Grothendieck 位相として J_U を定義する設計は標準的かつ正しい。厳密に well-defined なのは最小 poset モデル(ArchCtx_min、finite poset regime)に限られ、一般の ArchCtx(A) は圏として未形式化 |
| 第III部 | 局所・affine・単項式レベルは(A)、大域化に(D) | no-cancellation discipline(原則5.6)、冪等座標崩壊 no-go(補題5.6A)、Stanley–Reisner 同定(定理5.6C)、Nullstellensatz certificate(7.2A〜C)は本物の可換代数。scheme gluing(定義10.3)は偽の含意を含む(§2.3) |
| 第IV部 | (B)主体、計算例は(A) | Čech複体、torsor 記述、Mayer–Vietoris、擬円周の H¹≅ℤ 計算と cycle pairing は正確。Ob_U の一般定義(定義2.1)は restriction も層条件も与えない placeholder で、実内容は定義2.4 の標準 package が担う |
| 第V部 | 道具は(A)/(B)、中心機構は(C) | derived intersection、LawConflict_i = Tor_i、Tor-independence としての transversality は Stacks Project 水準で標準的。Tor₁ 計算2例は検算済みで正しい。しかし「transfer は derived non-transversality の現れ」という部の中心主張は証明されておらず、提示された例自身が定理の仮定を満たさない(§2.5) |
| 第VI部 | 骨格(A)/(B)、関節に(C)/(D) | 定理6.2 は Illusie/Stacks 流 square-zero lifting obstruction の正確な再現(Ext⁰-torsor 性、Ext⁻¹ の automorphism 制御まで正しい)。quotient stack [X/Ref_U] も well-defined。一方 U-smooth/U-singular の二分法が崩壊(§2.6)、π₁^AAT は群として未保証、gerbe class は gerbe の公理なしに宣言されている |
| 第VII部 | 節5の核のみ(A)、残りは(C)寄り | strict period の有限 poset homology model と擬円周 pairing(⟨ω,γ⟩ = r_sync − r_async)は正しく第IV部と厳密に整合。representation functor 族・curvature・mass・metric enrichment は target 圏も構成も欠く枠組み宣言 |
| 付録A | (B)、核は(A) | Spec_AAT = 通常の Spec + decoration、点 = prime ideal という規定は正しく、新奇な spectrum を捏造していない。ただし大域埋め込み(ringed topos と glued scheme の比較射、decoration の貼り合わせ)は方針表明であり検証済み定理ではない |

### 1.3 特筆すべき「本物」の部分

レビュー全16本が独立に高く評価した点:

1. **no-cancellation discipline(III 原則5.6)** — witness の和 δ=Σx_c が標数・符号で打ち消される罠を正確に認識し、lawfulness の primary encoding を ideal の vanishing(`s*I_L = 0` / `I_L ⊆ p`)に置く。比喩的テキストが必ず落ちる罠を回避している。
2. **冪等座標崩壊 no-go(III 補題5.6A)** — `k[x]/(x²−x)` 型代数では Tor・I/I²・Ω が全消滅し derived 理論が自明化することを正しく認識し、square-free witness regime(定義5.6B)を動機づける。第V部の Tor 計算が空転しないための本質的な配慮であり、本物の数学的洞察。
3. **生成位相による site 公理の担保(II 定義7.1)** — 意味論的 coverage 条件から base change / transitivity が自動で従うと誤魔化さず、生成される最小位相を取り、witness 喪失は後続定理の仮定(U-adequate)に送る。
4. **claim boundary の規律** — 「群の非零 ≠ 具体的 class の非零」(IV 原則4.4)、「未計算 ≠ 非零」(IV 原則11.3)、「Čech が sheaf cohomology を計算するには Leray 条件が別途必要」(II 7.2C)、abelian/torsor/gerbe の三層分離(IV 原則2.3)。標準的な障害理論の作法に忠実。
5. **検算可能な計算例の正しさ** — 擬円周の二弧被覆 Čech 計算(IV 例9.3/9.4)、`Tor₁(R/⟨xy⟩, R/⟨xz⟩) ≅ ⟨xyz⟩/⟨x²yz⟩ ≅ R/(x)`(V 例5.6/9.2)、period pairing(VII 例5.2B)。すべて独立検算で正しい。
6. **law を無理に ideal 化しない分類(付録A.6、III 原則5.8)** — closed equational / open / constructible / descent / temporal / stacky の階層分けは数学的に良識ある設計。

### 1.4 結論(軸①)

**比喩ではない。** ただし「本物の代数幾何である」と無条件に言えるのは ringed topos 階+affine chart 階+単項式 regime までで、「architecture scheme」「monodromy」「period」を名乗る上層は、本物になるための数学的負債(well-definedness 証明、比較射の構成、二分法の修正)を残している。README が宣言する階層(site → ringed topos → affine chart → scheme → derived/stacky)のうち、**下3段は実体があり、上2段は設計図段階**と読むのが正確である。

---

## 2. 軸②: 数学的GAP

### 2.1 全体統計

| 種別 | 件数 |
| --- | --- |
| critical(定理が偽 / 証明が根本的に壊れている) | 6 |
| major(実質的ギャップ・隠れ仮定・well-definedness 未証明) | 78 |
| minor(軽微) | 74 |

定理インベントリ(ラベル付き定理級主張、部ごと):

| 部 | 総数 | 本文中に証明 | 概略のみ | 主張のみ |
| --- | --- | --- | --- | --- |
| I | 8 | 0 | 1 | 7 |
| II | 3 | 0 | 2 | 1 |
| III | 7 | 0 | 3 | 4 |
| IV | 5 | 1 | 1 | 3 |
| V | 7 | 0 | 2 | 5 |
| VI | 6 | 0 | 3 | 3 |
| VII | 3 | 0 | 1 | 2 |
| 付録A | 5(prose内) | 0 | 0 | 5 |
| **計** | **44** | **1** | **13** | **30** |

### 2.2 critical #1: 定理9.3(第I部)— soundness+completeness から iff は導けない【検証2票で確認】

命題9.1(soundness)は `ω_L(A)=0 → L(A)`、命題9.2(completeness)は `¬L(A) → ω_L(A)>0` を与えるが、9.2 の対偶は(ω≥0 を仮定すれば)`ω_L(A)=0 → L(A)` であり、**両者は同じ方向の含意**である。定理9.3 が主張する `Lawful_U(A) iff ω_U(A)=0` のうち `Lawful → ω=0` 方向はどちらの前提からも従わない。

反例: L が恒真、ω_L ≡ 1(定数)。soundness・completeness とも空虚に成立するが、Lawful かつ ω=1≠0。

さらに per-law の ω_L から集約値 ω_U への接続も無仮定で使われており、Value に符号付き weight を許す定義8.5 の下では加法的打ち消しの反例も作れる。**これは本文が「AAT の flatness theorem の基本形」と呼ぶ命題であるだけに重大。**

修正は容易: soundness を「false positive なし」すなわち `ω_L(A)>0 → ¬L(A)`(同値に `L(A) → ω_L(A)=0`)として定式化し直し、ω の値域に順序付き可換モノイドを固定し、集約を `ω_U=0 iff ∀L. ω_L=0` が成り立つ形(例: 和ではなく sup、または非負値環)で定義すればよい。

### 2.3 critical #2: 定義10.3(第III部)— scheme gluing の含意が標準AGの反例で偽【主執筆者追検証で確認】

「`Spec_AAT(O(W_i))` たちが overlap `Spec_AAT(O(W_i ×_W W_j))` 上で agree すれば `Spec_AAT(O(W), D_W^U)` へ貼り合う」という表示推論(`part_3:1542-1568`)は、**affine chart を貼った結果が大域切断環の Spec になる**と主張しており、通常のスキーム論で偽である。

反例: ℙ¹ は `Spec k[x]` と `Spec k[1/x]` を `Spec k[x,1/x]` 上で貼るが、`O(ℙ¹)=k` であり `Spec k` は一点。sheaf 条件(equalizer)は比較射が open immersion であることも joint surjectivity も含意しない。定義9.2 の chart compatibility にも joint surjectivity は含まれないため、本文の hedge では修復されない。**「sheaf descent → gluing of affine AAT charts」という Part3 の topos→scheme 橋渡しの中心標語が、この偽の含意に乗っている。**

修正: 貼り合わせの結果は「W 上の chart」ではなく一般には新しい locally ringed space であることを認め、(i) 結果が再び affine になる十分条件(例: 有限 poset 上で principal context が final な場合)を別途定理化するか、(ii) 標語を「sheaf descent → architecture scheme の存在(必ずしも affine でない)」へ弱める。

### 2.4 critical #3: 定理11.1(第IV部)— Cohomological Flatness Criterion の正方向が自然な読みで偽【主執筆者追検証で確認】

第IV部の中心定理に証明が一切なく、`[g]=0 ⇒ 大域 lawful section 存在` の方向は「effective torsor after abelianization」という仮定の自然な読みの下で偽になりうる。非可換群層 G(例: PGL_n 型、abelianization が自明)の非自明 torsor(Severi–Brauer 型)では、abelianized class は常に 0 だが大域 section は存在しない。非可換 H¹ の情報は abelianization で保存されない — 原則4.4 自身が effectivity の必要性を正しく注意しているのに、11.1 の仮定リストにその注意が反映されていない。

修正: 調整 torsor が **abelian 層 Ob_U そのものの torsor** であることを仮定に明示し(abelianization 経由を許さない)、その下で標準的な torsor 論法(H¹ class が消える iff torsor が自明 iff section 存在)として証明を書く。

### 2.5 critical #4: 定理9.1/例9.2(第V部)— 中心機構「transfer = derived non-transversality」が確立されていない【主執筆者追検証で確認】

- 例9.2 の section family は `x ↦ 1` で固定されるため、repair path は conflict sheaf の support `V(x)` と**交わらない**(`Tor₁ ≅ R/(x)` の support は V(x))。x=1 上では `I_U, I_V` は `⟨y⟩, ⟨z⟩` となり完全に横断的。つまり**定理の仮定「repair locus において LawConflict₁ ≠ 0」を例自身が満たさない**。
- 逆に、横断的な組 `I_U=⟨y⟩, I_V=⟨z⟩` でも path `y↦1−t, z↦t` は同じ transfer を起こす。すなわち Tor₁≠0 は transfer の必要条件でも十分条件でもなく、**仮定が論証で何の働きもしていない**。
- 同じ ideal の組で path `x↦1−t`(y=1, z=0 固定)を取れば、non-transverse でも単調 repair が存在する。

非含意命題としての定理9.1 自体は真だが、第V部の物語の核(「副作用は Tor が読む構造的残差である」)は現状、数学として裏づけられていない。修正の方向: transfer を conflict sheaf の **support 上で**定義し直し、「support を通る repair path に沿った transfer の下界を Tor が与える」型の定理として再構築する(§5 の提案T5)。

### 2.6 critical #5: 定義4.1/5.1(第VI部)— U-smooth と U-singular の二分法が崩壊【主執筆者追検証で確認】

U-smooth が3条件の選言、U-singular が6条件の選言で定義され、選言肢が互いに非同値なため**両述語が同時に成立する stratum が存在する**。具体的に: `Ext¹(L, O_S)=0`(H¹(T)=0、第1選言で smooth)かつ `Ext¹(Lξ*L, M)≠0` なる M が存在(第2選言で singular)する例として、rigid singularity(変形を持たない特異点、例: 3次元商特異点)が標準理論にある。さらに singular 側の選言肢3つ(「tangent rank jumps」「normal cone is nontrivial」「derived law conflict concentrates」)は判定基準が未定義。God object 再解釈(§7)や「Size Is Not Singularity」(原則4.2)はこの二分法を前提に語られているため、章の中心概念が ill-defined。

修正: smooth を「すべての M に対する Ext¹(Lξ*L_{S/U}, M)=0」の単一条件で定義し、singular をその否定とする。他の選言肢は「同値になる regime」(例: lci + 有限表示)を明示した上で同値定理として回収する。

### 2.7 critical #6: 補題7.2A(第II部)— witness-closure cover の補題が記載仮定から証明不能【検証1票で確認、major へ降格修正可】

補題の仮定(局所有限性・support 表現可能性・overlap 存在)は、結論の U-adequacy 5条件のうち「restriction maps preserve the selected witness ideals」「required signature axes are readable」に一切触れない。Reading の選択の自由度(付録A.2)を使えば枠組み内で反例が構成できる。修正は仮定2件の追加で済むため実質 major だが、第IV部以降のすべての cover 構成がこの補題に依存するため波及が大きい。

### 2.8 major 所見の構造的パターン

78件の major は個別列挙より**5つの病型**に整理する方が有用である(個別一覧は付録参照):

**型1: 未定義述語への困難の吸収(定理のスキーマ化)。**
`exact` / `complete`(I §9)、`NoHigherBoundaryObstruction`・`C is U-flat`(IV §9)、`witness exactness`(VII 定理15.4 — corpus 全体で未定義)、`tangent rank jumps`(VI 定義5.1)。仮定リストに未定義の名前付き述語を置くことで、定理が「その述語をうまく定義すれば成立するだろう」という証明義務スキーマになっている。README の3区分でいう Formal theorem の体裁を保てていない。

**型2: トートロジー定理(定義の言い換え)。**
V 定理6.1/7.3/10.5前半、VI 定理6.1/11.1、I 命題5.3。仮定の述語が結論を定義として内蔵しており、「証明の読み」が定義の展開にすぎない。これらは「定理」ではなく「原則」「定義の帰結」へ降格すべきもの。なお IV 定理7.1・VI 定理16.2 のような対偶型定理は、構造は単純でも **obstruction class の well-definedness が証明されていれば**正当な定理である — 問題は型3がその前提を崩していること。

**型3: class / 不変量の well-definedness 未証明。**
hidden coupling class [hc_U(X)](IV: 正規化 mismatch の公理不足、torsor iff に sheaf 条件欠落 — 反例構成可能)、Hol_U(IV 定義9.1: section 選択非依存性未証明)、π₁^AAT(VI 定義9.2: 一部の射のみ可逆化した圏は groupoid にならない)、Mon_γ(VI: refactor equivalence witness の選択依存)、gerbe class(VI 定義16.1: local transitivity と band の同定なし — それなしでは定理16.2 に反例が構成できる)、strict period pairing(VII: cohomology-homology 比較同型・trace の存在・代表元非依存性が体系的に未証明)、I_Ob^U の sheaf 性(III 定義6.1/6.2: witness selection の restriction 整合性が hedge 処理)。**型2の定理群はすべて型3の class に乗っているため、本文の実質的な数学的負債はここに集中している。**

**型4: 大域化の飛躍。**
critical #2 のほか: 大域 lawful locus V(I_Ob^U) が点集合未構成の topos 段階で点ごとに定義され ill-defined(III 定義7.1)、|X| が未構成のまま措定され ringed AAT topos と glued scheme の比較射が欠如(III 定義9.3、付録A.5)、局所 decoration D_i から大域 D_X への貼り上げ未定式化(付録A.5)。

**型5: 標準理論との次数・向きのずれ。**
DerOb_U := Ext¹(L_{Flat/X}, M) の「obstruction space」ラベルは標準変形理論と次数が1ずれ(IV 定義2.4 — 標準では Ext¹ は first-order deformation、Ext² が obstruction)、normal cone が closed immersion なしに書かれ向きも逆(VI 定義5.2)、Kuranishi map の κ⁻¹(0) と Defhat の関係が標準理論と食い違い循環的(VI 定理候補6.4)、命題7.2C の「C^n=0 (n>d)」は alternating 規約を暗黙仮定(II)。

### 2.9 救いの所見

- **偽と確定した主張は上記6件+型3の一部反例可能件のみ**で、Stanley–Reisner・Nullstellensatz・Tor 計算・擬円周など「計算で支えられた背骨」は全件正しい。
- 検証エージェントはレビュー指摘自体も2件反証した(「architecture algebra は site の台を供給できない」「命題6.5 に形式的主張がない」— いずれも原文誤読)。レビューの過剰指摘は除去済みである。
- 付録Aの hedge(「自動成立ではない」)、「定理候補」ラベル、Lean 台帳との分離宣言(README)は、主張の誠実性として高水準。問題は誠実な hedge と Formal theorem ラベルの混在が**読者に区別不能**なことにある(§6)。

---

## 3. 軸③: 実コード適用 — 意味のある計測まで完成しているか

### 3.1 答え

**一般形では未完成、しかし特定の regime では「あと実装だけ」の水準まで来ている。**

理論が自ら用意している計算可能経路は次である:

```text
有限 poset AAT site regime (II 定義7.2B)
  + square-free witness regime (III 定義5.6B)
  + Stanley–Reisner obstruction ideal (III 定理5.6C)
  + 有限 Čech 複体 (II 命題7.2C)
  + monomial Tor 計算 (V 命題5.5: Taylor resolution / Scarf complex)
  + Nullstellensatz certificate / NSdepth (III 7.2A-D)
  + 有限 poset homology model の strict period (VII 定義5.2A)
```

この経路上では、すべての不変量が**有限の組合せ論と線形代数**に落ちる。これは本理論の最大の実用的資産であり、意図的に設計されたものと読める。

### 3.2 パイプライン段階別評価

| 段階 | 数学的完成度 | 計算可能性 | 残る障害 |
| --- | --- | --- | --- |
| Atom 抽出(ExtractionDoctrine) | 公理的定義あり | **未保証** | E・N・use-rule R の決定可能性が未規定。semantic Atom の抽出一意性(公理A8)は実装仕様ではなく公理。抽出器の健全性を語る理論層がない(§5 提案B4) |
| site 構成 | finite poset regime は厳密 | ○(有限なら自明) | U-adequate cover の構成補題(7.2A)が壊れており、修正仮定の追加が必要 |
| I_Ob^U 構成 | square-free regime は厳密 | **◎ 完全に組合せ的** | forbidden support 族の同定は law 設計の問題(数学側は完成) |
| H^n 計算 | Čech は有限線形代数 | ○ | alternating 規約の明示が必要(II 7.2C)。Čech→sheaf cohomology の Leray 条件を検証する手段が**ない**(acyclic cover の構成定理が必要、§5 提案T6) |
| LawConflict (Tor) | monomial regime は標準理論 | ◎(Macaulay2 等の既存実装可) | 共通 ambient O_X の構成が U 依存で曖昧(V rigor 指摘)— 同一 site 上の二つの witness 選択として再定式化が必要 |
| monodromy / Mon_γ | π₁^AAT が ill-defined | × | 群構造の保証から作り直し(§5 提案T9) |
| period | 有限モデルは計算可能 | △ | pairing の well-definedness(比較同型)が未証明。係数評価 tr の存在条件も未固定 |
| 計測値の品質保証 | **存在しない** | — | 安定性・単調性・識別力に関する定理が皆無(§3.3) |

### 3.3 計測理論として欠けている最重要要素: 安定性

現場のコードベース計測に使うには「小さなリファクタで値が暴れない」「コードが悪化すれば値が悪化する」が**定理として**必要だが、本文には摂動に対する不変量の挙動を述べる定理が一つもない。

- Atom 1個の追加・削除で H¹ や Tor の次元はいくら動きうるか(Lipschitz 型の bound)
- refactor groupoid の射に沿って不変量はどう変換されるか(VI §12 は groupoid を定義するだけで、不変量との関手性を述べない)
- law universe の単調拡大 U ⊂ U' で各不変量は単調か(付録A.2.1 の閉埋め込み塔はこの方向の唯一の萌芽だが、証明なし+隠れ仮定3件)

安定性定理がない計測は、実コードに当てたとき「ノイズと信号を区別できない」。**これが「意味のある計測ができるところまで完成しているか」への最終的な No の理由**であり、同時に次に証明すべき定理の筆頭である(§5 提案T1)。

### 3.4 リポジトリ実装との突き合わせ

- `tools/archsig`(Rust, v1 稼働): ArchMap + LawPolicy → typed evaluator 出力。witness counting 中心の**古典AAT読み**であり、本文の幾何的不変量(H¹、Tor、NSdepth、period)は未実装。
- `tools/fieldsig`: forecast/governance 側。同上。
- `Formal/`(Lean, 139ファイル): graph/walk/monodromy 等、**先行体系(有限・構成的AAT)の形式化**。AG版の定理ラベル(Stanley–Reisner、Nullstellensatz、LawConflict、gerbe 等)は `lean_theorem_index.md`(3,081行)・`proof_obligations.md` に**1件も登載されていない**。README 自身が「台帳にない theorem label は Lean proved claim と読まない」と明言しており、この分離は誠実。
- 含意: AG版本文は現状、実装とも形式化とも接続されていない純設計書である。§3.1 の計算可能経路は archsig の評価器に載せられる粒度まで数学が降りているので、**接続の第一候補はここ**。

---

## 4. 軸④: 追加・強化できる定理

優先度順。各項目: 内容 → 価値。

**T1. 安定性定理(最優先)。**
`d_I(H*(X_F), H*(X_F')) ≤ C · |F △ F'|` 型の主張。atom family の対称差(または witness ideal の生成元の追加・削除)に対する Čech cohomology / Tor 次元の interleaving 距離の bound。square-free regime なら、forbidden support 1個の追加が Δ_U(W) の simplicial collapse / anticollapse に対応するため、persistent homology の安定性定理(Cohen-Steiner–Edelsbrunner–Harer / Chazal et al.)がほぼそのまま輸入できる。**計測のノイズ耐性が初めて定理になる。**

**T2. Refactoring functoriality(不変量の変換則)。**
refactor groupoid Ref_U の射 φ: A → A' に対し、誘導射 φ*: H^n(X_{A'}, Ob_U) → H^n(X_A, Ob_U) の存在と、同型になる十分条件。「リファクタは obstruction class を保つ/移送する」が定理になれば、計測値のリファクタ不変性が保証され、Monodromy Debt(VI 11.1)も well-defined な土台に乗る。

**T3. soundness/completeness の正規化と定理9.3 の修正版。**
§2.2 の通り。ω の値域を順序付き可換モノイドに固定し、no-false-positive / no-false-negative の正しい対で iff を証明する。Lean 形式化の最初の1本にも適している(有限なら decidable)。

**T4. Mayer–Vietoris と多 feature スペクトル系列の完全証明。**
IV 定理候補10.4 を candidate から theorem へ。有限 poset site + abelian 係数なら標準的な二重複体論法で書ける。multi-feature 干渉の「どの組が衝突するか」を E₂ 項で読む実務価値が大きい。

**T5. Support-localized transfer theorem(第V部の作り直し)。**
§2.5 を受けて: 「repair path γ が supp(LawConflict₁(U,V)) を通るとき、V-residue の変化量は γ に沿った Tor₁ の長さ(または pairing 値)で下から評価される」型の定理。これが立てば「副作用は Tor が読む」が初めて数学になる。立たなければ、transfer の正しい不変量は Tor ではない(例えば I_U∩I_V / I_U·I_V の生成元の共有構造)ことが分かる — どちらでも理論は前進する。

**T6. Leray/acyclicity の組合せ的十分条件。**
有限 poset site 上で「principal context による cover は selected 係数に対し acyclic」のような検証可能条件。これがないと H^n(𝒰,F) を計算しても H^n(X,F) を計測したことにならない(本文自身が正しく注意している穴を、自分で塞ぐ)。

**T7. NSdepth と repair cost の橋渡し定理。**
unlawfulness certificate の次数 NSdepth_U(W) が、repair route の最小長(VII §12)の下界を与える条件。証明複雑性(Polynomial Calculus の degree 下界、§5 B6)から既製の下界技術が輸入できる。「直せなさの証明書」という実務で最も欲しい量に直結。

**T8. Semicontinuity(法族・コード進化に対する上半連続性)。**
コミット列 {F_t} をパラメータ族と見て、dim H¹(X_{F_t}, Ob_U) の上半連続性が成り立つ regime を特定。劣化検知(値の跳ね上がり)の理論保証になる。

**T9. π₁^AAT の正しい構成と有限計算定理。**
operation category の localization(zig-zag / hammock localization)として π₁ を定義し直し、有限 poset regime で nerve の edge-path group として計算可能であることを示す。これで Monodromy Debt 定理が型1・型3病から脱出する。

**T10. gerbe の banding 可能条件。**
Aut(Dec_U) が abelian center を持つ(または decomposition が中心的に同値)場合に gerbe class が H²(X, Z(Aut)) に落ちることの証明。No Canonical Decomposition 定理が検証可能な主張になる。

**T11. 二つの law universe の共通 ambient 定理。**
同一 site・同一 O_X 上の witness 選択の対 (U,V) として LawConflict を再定義し、J_U と J_V の生成位相の比較射の存在条件を明示(付録A.2.1 の3主張の証明を含む)。第V部全体の前提を固める。

**T12. Square-free 化可能性の特徴づけ。**
どの law family が(係数拡大や座標追加なしに)square-free witness encoding を持つかの特徴づけ。NoCycle・layering は持つ(witness = 経路の単項式)。contract refinement・temporal law はどうか。Stanley–Reisner 経路(§3.1)の適用範囲を確定する。

---

## 5. 軸⑤: 他分野への橋

評価軸は「コードベース解析に何が新しく測れるようになるか」。実現可能性の近い順。

**B1. 組合せ可換代数(半分架かっている橋を渡り切る)— すぐできる・効果大。**
定理5.6C で Stanley–Reisner に到達済みなので、その先の定理群が無料で付いてくる: **Hochster の公式**(I_Δ の graded Betti 数 β_{i,j} = Δ の制限部分複体の被約 homology)、Taylor/Scarf 複体、lcm-lattice、Alexander 双対(minimal non-face ↔ minimal vertex cover の双対で「障害パターン」と「修復セット」が双対になる)。
測れるもの: β_{i,j}(I_Ob) は「障害の絡まり方の高次構造」— 障害数が同じでも絡まり方が違うコードベースを区別する。Alexander 双対は **minimal repair set の列挙**をそのまま与える。CoCoA/Macaulay2 で即計算可能。

**B2. TDA / persistent homology — すぐできる・効果大。**
law universe の filtration `U_1 ⊂ U_2 ⊂ …`(law を厳しくしていく)や時系列(コミット列)に沿った H*(X, Ob_U) の persistence barcode。輸入できる定理: bottleneck/interleaving 安定性(T1 の証明エンジン)、代表サイクル抽出。
測れるもの: 「どの law 強度で障害が生まれ、どの強度まで生き残るか」のバーコード。一時的ノイズと構造的負債の分離。ツール(Ripser、GUDHI)も既製。

**B3. Cellular sheaves / sheaf Laplacian(Hansen–Ghrist)— すぐできる・効果大。**
有限 poset 上の sheaf は cellular sheaf そのもの。sheaf Laplacian L = δ*δ + δδ* を組めば、H^n = ker L_n が**数値線形代数**になり、さらに固有値スペクトルが「ほぼ整合(near-consistency)」の度合いを与える。
測れるもの: 第VII部が枠組み宣言で終わっている **distance to flatness・obstruction mass の数学的実体**(最小固有値・スペクトルギャップ)。「障害が消えるまでの距離」が連続量で出る。heat flow による「最も整合に近い修復」の勾配も得られる。第VII部の (C) 判定部分を一気に実体化する最有力ルート。

**B4. Abstract interpretation(Galois 接続)— 中期・抽出層の理論化。**
coarse projection / resolution(I §1.4、A8)は Galois 接続 α ⊣ γ そのもの。輸入できるもの: 健全性定理の標準形(「coarse reading 上の lawful 判定が canonical family 上の判定を過大評価しない条件」)、widening/narrowing。
価値: §3.2 の最弱段(Atom 抽出の健全性)に既製の理論を当てられる。抽出器の「観測は Atom を生成しない」公理(A6)が、abstraction の健全性条件として検証可能になる。

**B5. Institution theory / Goguen の sheaf semantics — 中期・相対化の体系化。**
(V,U,J,k) への徹底した相対化は、Goguen–Burstall の institution(署名圏上の文・モデル・充足の関手系)と同型の問題意識。先行研究として Goguen "Sheaf semantics for concurrent interacting objects" (1992) は「振る舞いの sheaf」でシステム合成を扱っており、**本理論の最も近い先行者**。引用・差分明示(Goguen は behavior の gluing、AAT は law failure の cohomology — H¹ 以上を実際に使う点が新規)に使うべき。

**B6. 証明複雑性 / SAT・CSP — 中期・修復困難性の下界。**
Nullstellensatz certificate は証明複雑性の **Nullstellensatz/Polynomial Calculus 証明系**そのもの。NSdepth = NS degree。輸入: degree 下界の技術(design による下界、Tseitin 型障害)、Gröbner 計算との関係。
測れるもの: 「この障害クラスタは浅い証明書で unlawful と確定できる/できない」— 修復優先度付けに直結。実装も既存の Gröbner/SAT ソルバが使える。

**B7. Sheaf neural networks — 遠いが視野に。**
B3 の sheaf Laplacian の上に学習(sheaf diffusion)を載せる系譜(Bodnar et al.)。law 違反の予測や repair 提案のランキングに、構造を保った GNN を使える。理論強化ではなく応用拡張。

**B8. 数論的類似(period・Galois 表現・L関数)— 遠い橋と明示すべき。**
第VII部の period、第VI部の monodromy は数論的類似を意識した命名だが、Galois 群に相当する対象(π₁^AAT)が未構成である以上、現状は語彙の類似に留まる。架けるなら T9 の後、有限 Galois 圏(SGA1)として operation category の有限被覆論を作る経路だが、コード解析への実利は現時点で見えない。**「architecture の zeta 関数」のような方向に進む前に B1–B3 を渡り切るべき**、というのが本レビューの助言である。

---

## 6. 軸⑥: その他の気づき・改善点

**E1. worked example の不在(最大の編集的欠落)。**
9,600行のどこにも「実コード断片 → Atom family → site → I_Ob → H¹ → Tor → period」を**一気通貫**で計算する例がない。擬円周(IV 例9.3/9.4、VII 例5.2B)と共有 witness(V 例5.6/9.2)は部分例として優秀だが、コード起点でない。30行程度のミニ・コードベース(モジュール3つ、cycle 1つ、contract mismatch 1つ)で全構成を回す「付録B Worked Example」を強く推奨する。これは (i) 構成の非空性の証明、(ii) 読者の導線、(iii) 実装仕様、の3役を兼ねる。

**E2. 主張3区分のタグ化。**
README は Formal theorem / Certified bounded inference / Analytic reading の3区分を宣言するが、本文の「定理」「命題」ラベルからどれに属すか判別できない。型1・型2病(§2.8)の多くは、`[F]`/`[C]`/`[A]` タグを定理ラベルに付ければ「誤り」から「区分明示済みの設計宣言」に変わる。低コストで文書の誠実性を大きく上げる修正。

**E3. ラベルの降格・昇格の整理。**
- 「定理」→「原則」へ降格すべき: V 6.1/7.3/10.5前半、VI 6.1/11.1、VII 16.1(synthesis は定理の体裁がない)
- 「定理候補」のままで正しい: IV 10.4、VI 6.4(誠実なラベリング)
- 証明を書けば「定理」に昇格できる(数学は正しい): III 5.6A/5.6C/7.2A-C、II 7.2C(規約修正後)、V 5.5

**E4. 未定義語の台帳化。**
`exact` / `complete` / `witness exactness` / `U-flat` / `NoHigherBoundaryObstruction` / `trace topos` / `operation homotopy` / `tangent rank` 等、定理の仮定に現れる未定義語を `proof_obligations.md` 方式の台帳に集め、各語に「定義予定 / 意図的プリミティブ / 廃止」のステータスを付ける。型1病の系統的解消法。

**E5. 前方依存の解消。**
II 命題7.2C の Čech 複体が第IV部の微分定義に依存、I §9 の witness completeness 等が後続部で初めて意味を持つ、など。各部冒頭に「この部が後続部から借りる記号」を明示するか、定義を前倒しする。

**E6. 記号表・用語集。**
X^{V,U,J,k}、O_X^U、I_Ob^U、Flat_U、Ob_U、LawConflict_i、NSdepth、Δ_U(W) 等の主要記号に一覧がない。9,600行の文書には必須。

**E7. 第VII部の二分。**
節5(period の核、(A)水準)と、それ以外(representation/curvature/mass、(C)水準)の完成度差が激しい。節5を第IV部の続きとして昇格させ、残りを「Analytic Reading 設計書」として別文書化する構成変更を検討する価値がある。

---

## 7. 修正ロードマップ(優先順)

| # | 作業 | 規模 | 効果 |
| --- | --- | --- | --- |
| 1 | I §9: soundness を `ω>0 → ¬L` に再定式化、ω の値域構造を固定、9.3 を証明付きで書き直す | 小 | 理論の「基本形」の修復。Lean 化候補 |
| 2 | III 定義10.3: gluing 含意の修正(joint surjectivity を条件に追加 or 主張を弱める) | 小 | (D)級誤りの除去 |
| 3 | VI 定義4.1/5.1: smooth/singular を単一条件+同値 regime 定理に再編 | 中 | 第VI部の中心概念の修復 |
| 4 | IV 定理11.1: abelian torsor 仮定に固定して証明を執筆 | 中 | 中心定理の確立 |
| 5 | II 補題7.2A: 仮定2件(ideal保存・axis可読性)を追加 | 小 | cover 構成の信頼回復 |
| 6 | 型3の well-definedness 証明群(hc class → Hol → Mon → gerbe → period pairing の順) | 大 | 対偶型定理群が本物の定理になる |
| 7 | E4 未定義語台帳 + E2 タグ化 | 小 | 文書全体の主張規律 |
| 8 | E1 worked example 付録 | 中 | 非空性・導線・実装仕様 |
| 9 | T1 安定性定理(B2 の輸入で) | 大 | 計測理論としての成立 |
| 10 | V transfer 理論の再構築(T5) | 大 | 「副作用の幾何学」の確立 |

---

## 8. 結論

ユーザーの6つの問いへの一行回答:

1. **本物の代数幾何か** — ringed topos・affine chart・単項式 regime までは本物(計算例は全件検算済みで正しい)。scheme 大域化と解析層は設計図段階。比喩で空転している箇所はごく少ない。
2. **数学的GAPはないか** — ある。critical 6件(うち5件は中心定理・中心概念)、major 78件。ただし系統的な5病型に整理でき、大半は修復可能。偽と確定した計算は1件もない。
3. **意味のある計測まで完成しているか** — 一般形では No。安定性定理の不在が決定的。ただし「有限 poset + square-free + Stanley–Reisner + monomial Tor」の経路は実装着手可能な水準まで数学が降りている。
4. **追加・強化定理** — 12件提案(§5)。筆頭は安定性定理 T1 と refactoring functoriality T2。
5. **他分野への橋** — 8本評価(§6)。即効性は組合せ可換代数(Hochster・Alexander双対)、TDA(barcode・安定性)、cellular sheaf Laplacian(距離・mass の実体化)の3本。
6. **その他** — worked example の執筆と主張3区分のタグ化が、コスト対効果の最も高い改善。

この理論の独自の強みは、「障害の幾何学」を**有限の組合せ可換代数に落とす経路を自分で用意していること**(square-free regime)と、**語れないことを語らない規律**(相対化・claim boundary)である。弱みは、その規律が定理の証明にまで及んでいないこと。上のロードマップ1〜5(いずれも小〜中規模)を済ませるだけで、本文の数学的信頼性は大きく変わる。

---

## 付録: レビュー実施記録

- レビューエージェント16本(8ファイル × rigor/gaps)+ インベントリ8本: 全件完了
- 敵対的検証: 17評決完了(15成立 / 2反証棄却)。残る critical 4件は主執筆者が数学的に追検証して確認済み(ℙ¹ 反例、Severi–Brauer 型反例、conflict support 解析、rigid singularity)
- major 78件のうち未検証は約60件: 本レポートでは個別主張ではなく病型(§2.8)として要約した。個別の検証が必要になった場合は、該当箇所を指定されたい
- 検証で棄却された指摘(本レポート不採用): 「第I部 §10 の algebra が site の台を供給できない」(第II部の site の台は ArchCtx(A) であり誤読)、「命題6.5 に形式的主張がない」(非含意主張が明示されており誤読)
