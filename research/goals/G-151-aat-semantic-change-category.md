# G-151-aat-semantic-change-category — 意味を保つ全変更とその局所性

- `id`: G-151-aat-semantic-change-category
- `status`: `draft`
- `research mode`: `target-theorem`
- 関連メモ: [#6359](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/6359)。実行用tracking Issueはactive化時に定める。
- 設計: [n1019 §5–6・8](../../docs/note/n1019_shigure_representability_design.md)
- 依存: G-150の意味再構成・Law幾何。

## 研究目的

元の意味を保つ非可逆な変更、その合成、整合する局所変更の組立てを同じ幾何で回復する。
局所変更を整合させる補正とその障害はG-152、指定障害と診断の比較はG-144が扱う。

## 固定target

### A. 非可逆射と観測

原始signatureのmodel圏において、実際のsort mapsからoperation/relation保存射を作る。
観測oと各operationを保つh:A→Bの全体をChg_o(A,B)と定義する。
元の状態mapからこの条件を検査し、全有限操作語の観測保存を帰納的に証明する。
非単射・非全射を許し、全射を同型に置換しない。

固定語彙の構造保存と、traceだけのbehavioral equivalenceを区別する。
操作語翻訳を持つ変更は、原始term substitutionと状態mapで定義して合成を構成する。
phase・stutteringを使うときはその翻訳と許可経路を明示する。
観測を強くするとChgがどう変わるかを同じ写像で比較する。

### B. 射の幾何と合成

G-150 Nの全Homのprofile表示と同A–Dのquantity引戻し・対応空間から、
各係数的実現σの独立な変更modelと幾何的表示の全Rでの自然な同値を構成する。
さらにnative基点で元のChgの全Homを回復し、指定native点の係数移送と比較する。
copying familyとlinear familyを全Rで同一視しない。
各射を、その源・標的・quantity保存等式とともに表現する。
単にM_before×_{M_obs}M_afterの点を取って、状態比較hを落とすことはしない。

N_nをn個の合成可能な実際の変更とその可逆な比較のgroupoidとして作る。
Segal同値、恒等、合成、coherenceとnativeの合成との一致を証明する。
同型比較のgroupoid化と変更そのものの可逆化を混同しない。
同型な原始表示、definitionalな補助演算の追加・消去について、この全構造を比較する。

### C. 文脈と係数のdescent

原始宣言・witness・Law supportからAAT文脈coverを生成する。
別に係数schemeの被覆を固定する。二つの制限の可換性を構成し、
対象・全Hom・観測保存・合成のdescentを同じprimitive mapsから証明する。
Lawを含まない断片だけの被覆でLawfulのdescentを主張しない。
totalityや有限supportの条件もそのまま残す。

平方零lift、文脈に沿う組立て、fragmentの延長を、それぞれどのfiberの問題か定義する。
matching familyから対象・状態比較・観測保存を持つ実際の変更を組み立て、その一意性を証明する。
原始宣言から被覆・全制限・matching条件を作り、sheaf条件をcallerに要求するだけで済ませない。
整合していない局所変更をmatchingへ補正する存在問題とは区別する。

### D. 同じ意味を保持していることの試験

全lens Hom、全protocol自然変換、G-124の同じHom query、
G-126のquotient repairを比較対象にする。
非可逆な必須例として、V=Bool、hidden担体Kを持つlensの射K×V→Vを、
get/put保存・全Hom分類・合成とともに幾何へ運ぶ。|K|>1なら同型ではないことを示す。
G-126の共通behavior上端を保つ商修復と、指定adapter間の変更が別fiberであることを示す。
前者の組立て原理の仮定と後者のfiberの入力を照合し、同一の問題として扱わない。

### P. 階数変更と操作言語を持つ多項式特殊化

[n1020 §12・16](../../docs/note/n1020_shigure_polynomial_specializations.md#development-change)
のbefore/after・状態比較h・観測・操作語翻訳τからcomparison presentationを作り、
G-150 Pのschemeと独立なmodelの同値へ通す。両端の状態階数が違う場合も量化する。
原始式から両端へのspanとそのfiber、合成可能な比較のfiber productから合成比較への射を
生成し、Bのnerveへ同定する。unmarked版では同型を保持した2-fiber productを使う。

加法・単項演算から状態作用を作り、G-126のOperationSystem / behaviorへ同じ評価で接続する。
ArchSigの純粋affine Termの型付き解釈では、元式と加群上の式評価の一致を証明する。
二引数加法をtensor上の双線形写像とはしない。有限phase graphでは各phaseの状態を
0引数演算と不変量の実現fiberとして作り、遷移後の不変量と観測差が元のidealに属することを
原始式から証明する。この比較から全許可有限経路の観測保存を導く。

台帳の同じAtom・apply・compact・read・比較p・初期状態対応を使い、次を必須例とする。

1. pi=id、pj=0から全原子操作語の保存を証明し、係数実現をSL₂×A¹に同定する。
   p=(1,1)のmarked fiberはA²_(λ,μ)、固定状態のfiberはp⁻¹(x)として区別する。
   rank1・一生成元・unary λ,μの表示から各型のコピーとp,i,jを回復し、marked fiberとの
   自然同型を構成する。異なる型の射をidへ等置せず、unmarkedの同値も推論しない。
2. writeB/writeCの途中にもreadを許す場合、R=ℚ、λ=1/2、u=2で保存が失われることを示す。
   原子操作語の保存と、観測言語を広げた場合の保存を同じ状態・評価で比較する。
3. snapshotではBusyの不変量μ(h−C)=0を保持し、全許可経路の保存とμ(1−λ)=0の同値を
   begin; apply_1; finishの必要性を含めて証明する。意味保存の像をV(μδ)、δ=1−λへ同定する。
   Busyの全ambient R³上で同じ保存を要求した場合の条件μ=0を、(B,C,h)=(0,0,1)から導く。
   λ=μ=1では合法状態上の全語保存が成立することも、同じR=ℚで示す。
4. compact_allを固定引数compact_tへのt=Cの代入として生成し、applyなしのbegin; finishと
   一致することを示す。修正版finish_snapではBusyの状態Lawを除いて全R³を状態とし、
   x=B+Cで全係数の操作列を保存すること、μδ=0上で旧合法状態の包含が遷移と可換になることを証明する。
   R=ℚで旧状態Lawを残したδ=μ=1ではbegin; apply_1が閉じないことを示す。
   μ=1のcompact_allは非単射で、固定引数compact_tとその有限語はtranslationであることも検査する。

同時変形のliftと、合成可能な意味保存射の合成は別のfiber問題として定義する。
Pの同じsnapshotを使った高次liftの存在・失敗はG-152の固定targetとする。

## 前提・構成台帳

| 対象 | 役割 | 構成・証拠 | 使用先 |
| --- | --- | --- | --- |
| 指定観測・操作・語の翻訳 | 入力 | Aの状態mapと可換式 | 全語の意味保存 |
| 係数的実現・そのnative比較 | 先行構成 | G-150 | Bの射と合成の幾何 |
| 文脈support・witness・係数被覆 | 入力と構成義務 | Cの二種類のdescentを区別 | 組立て比較 |
| matchingな変更・全制限・組立て | 構成義務 | Cの同じ原始maps | 局所から大域への射と合成 |
| 台帳・phase・状態比較・語翻訳 | 原始入力と構成 | Pの操作と不変量 | 一般の変更構成への同定 |

## 完了条件

A–D・Pの構成、全Homと合成の比較、descent、指定例をLeanで証明する。
G-124・G-126への同一対象上の比較と必要仮定の放電をreportに記す。
未構成の射・witnessを除去した小さなcategoryの同値では本targetを達成しない。
反証は同じ原始入力と破れる比較を示して記録し、一般targetを黙って弱めない。

成果物はresearch/lean/ResearchLean/AG/のLean証拠と、
research/reports/G-151-aat-semantic-change-category.mdの宣言・前提対応に置く。
[共通完了基準](../../.codex/skills/target-theorem-loop/references/target-goal-contract.md#共通基準の参照適用)を適用する。
