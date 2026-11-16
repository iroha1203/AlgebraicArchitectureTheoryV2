# G-151-aat-semantic-change-category — 意味を保つ全変更とその局所性

- `id`: G-151-aat-semantic-change-category
- `status`: `draft`
- `research mode`: `target-theorem`
- 関連メモ: [#6359](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/6359)。実行用tracking Issueはactive化時に定める。
- 設計: [n1019 §5–6・8](../../docs/note/n1019_shigure_representability_design.md)
- 依存: G-149・G-150。G-142・G-146・G-148は具体的特殊化。

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

G-149の全Homのprofile表示とG-150のquantity引戻し・対応空間から、
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
SAGAのactual repair sheaf、係数、matching/completenessへの入力をこの構成から供給する。
指定mismatchと指定障害類の一致、零性と修復torsorの比較を証明する。
任意のsheaf条件をcallerに要求しただけの定理でこの義務を済ませない。

### D. 同じ意味を保持していることの試験

全lens Hom、全protocol自然変換、G-124の同じHom query、
G-126のquotient repairを比較対象にする。
非可逆な必須例として、V=Bool、hidden担体Kを持つlensの射K×V→Vを、
get/put保存・全Hom分類・合成とともに幾何へ運ぶ。|K|>1なら同型ではないことを示す。
G-126の共通behavior上端を保つ商修復と、指定adapter間の変更が別fiberであることを示す。
G-152の例で前者の一般的な組立て原理を後者へ誤用できないことを証明する。

台帳分割のsnapshot例で、独立に合法な二変形方向の同時liftが二次で失敗することを
同じ観測・許可操作で再現する。これは合成可能な意味保存射の合成とは異なるfiberの問題である。
adapterの原始操作保存も検査する。
G-148のK0指定類比較を再利用するときは、係数・台・Law値label・C0–C6等を揃える。
診断の次元が同じという理由で意味保存を結論しない。

## 前提・構成台帳

| 対象 | 役割 | 構成・証拠 | 使用先 |
| --- | --- | --- | --- |
| 指定観測・操作・語の翻訳 | 入力 | Aの状態mapと可換式 | 全語の意味保存 |
| 係数的実現・そのnative比較 | 先行構成 | G-149・G-150 | Bの射と合成の幾何 |
| 文脈support・witness・係数被覆 | 入力と構成義務 | Cの二種類のdescentを区別 | 組立て比較 |
| SAGA等の係数・完全性・比較射 | 放電義務 | C–Dの同じ原始変更から生成 | 指定障害・修復torsor |

## 完了条件

A–Dの構成、全Homと合成の比較、descent、指定例をLeanで証明する。
既存のSAGA・conormal・Atlasへの写像と必要仮定の放電をreportに記す。
未構成の射・witnessを除去した小さなcategoryの同値では本targetを達成しない。
反証は同じ原始入力と破れる比較を示して記録し、一般targetを黙って弱めない。

成果物はresearch/lean/ResearchLean/AG/のLean証拠と、
research/reports/G-151-aat-semantic-change-category.mdの宣言・前提対応に置く。
[共通完了基準](../../.codex/skills/target-theorem-loop/references/target-goal-contract.md#共通基準の参照適用)を適用する。
