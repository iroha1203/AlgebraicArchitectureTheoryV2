# G-142 — 診断の族・実修復・観測判定の紙上証明

[固定target](../../goals/G-142-aat-law-value-diagnostic-sheaf.md) A–G・Wの原始入力から、Law値診断の整数複体、実現scheme上のétale層、合流比較、実修復の指定障害、Atlas細分化、追加観測の判定を構成する。

診断次元は有限の零・非零条件で定める任意の有限値関数を実現できる。一方、実操作の組立てを判定するのは、同じ操作から生成して診断へ送った指定類である。この区別を保ち、細分化では評価条件を含む全修復fiberまで比較する。

| 本文 | 内容 | target |
| --- | --- | --- |
| [整数診断](integer-diagnostics.md) | 同じlabel、全微分、係数変更、既存K0/K1 | A |
| [診断のétale層](diagnostic-sheaves.md) | 原始scalar、有限root scheme、stalk、base change、partition | B |
| [値の合流](collision-comparison.md) | 値別部分複体、特殊化、Mayer–Vietoris、全粗化 | C |
| [診断次元の実現](dimension-realization.md) | 任意の零・非零条件、原始実現、pseudo-coherent複体の不存在 | D |
| [実操作の指定障害](specified-obstruction.md) | 原始relation、Ob、実Čech、SAGA、整数からの反映 | E |
| [Atlas細分化と全修復](atlas-refinement.md) | 同じ有限空間、C0–C6、全解、評価条件 | F |
| [観測に相対的な判定](relative-decision.md) | 三量化、係数域、kernel、全極小十分観測、幾何点 | G |
| [指定例](witnesses.md) | W1–W6の同じ入力と比較map | W |
| [source対応](source-map.md) | 全条項・既存宣言・仮定の使用箇所 | A–G・W |

## 規約と依存

環は単位的可換環で零環を含む。幾何の基礎環 `k`、Law値の値域、診断の加群係数 `Λ` を別々に指定する。診断の層は小étale site上の `Λ` 加群層である。整数複体をtensorする操作ではlabelを固定し、値域の変更では原始評価からlabelを再生成する。

複体は次数0・1・2、`d⁰` は右−左、`d¹` は三辺の交代和。graphの向きと増加添字の向きは符号mapで比較する。値合流のmapは合流後から合流前へ、reading比較のcochain mapは粗側から細側へ向かう。

[G-139](../G-139-aat-law-generated-relative-geometry/README.md)の独立な実現、[G-140](../G-140-aat-semantic-change-category/README.md)の全変更と探索fiber、[G-141](../G-141-aat-coherent-repair-effectivity/README.md)の実障害・全修復・有限算法を用いる。これは通常の数学による紙上証明であり、既存Leanへの比較は同じ原始dataを保ったmapとして記述する。
