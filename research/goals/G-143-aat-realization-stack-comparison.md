# G-143-aat-realization-stack-comparison — 実現の自己同型とstack表現

- `id`: `G-143-aat-realization-stack-comparison`
- `status`: `draft`
- `research mode`: `target-theorem`
- `tracking issue`: [#6359（設計）](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/6359)。個別のResearch Loop Issueはactive化時に定める。
- 設計: [多項式特殊化ノート §7](../../docs/note/n1020_shigure_polynomial_specializations.md#7-自己同型を保持する場合)
- 依存: [G-140](G-140-aat-independent-realization-descent.md)。schemeとの比較には[G-141](G-141-aat-semantic-scheme-representability.md)・[G-142](G-142-aat-shigure-reading-naturality.md)を使う。

主経路は[n1019](../../docs/note/n1019_shigure_representability_design.md)のG-149〜G-152にある。
本カードは多項式特殊化を構成する。主経路と同じ対象・射・Law評価への比較を要し、
本カードの達成だけでSHIGURE全体の達成とはしない。

## 研究目的

同じAtom / Lawの実現について、生成元を保持する意味と、実現の自己同型を保持する意味を
比較する。groupoidでのdescentと代数性を証明し、schemeが扱う実現の選択を明確にする。

## 固定target

### A. 基底付き実現と群作用

任意の可換環kとノート§3.1のPについて、基底付きQ_v=k^{n_v}上の演算係数と
required LawからX_Pをaffine schemeとして構成する。
G=∏_v GL_{n_v}の作用をtensor式の基底変更から生成し、Law idealの保存を証明する。
有限性はVと各階数に使い、演算・Lawの添字集合全体の有限性を追加しない。

### B. 独立なRealの代数性

G-140のRealからframe torsorとG同変なX_Pへの射を作り、逆にtorsor上の加群・演算を
descentする構成を与える。対象だけでなく全ての同型を運び、両方向の自然同値を証明する。
これによりfppf stackとしてのReal≃[X_P/G]とノート(G)を得る。

Gのsmoothness・有限表示を証明して代数性の標準定理へ接続する。
対角の表現可能性とsmooth surjective atlasを示し、stack条件だけで代数性を済ませない。
係数変更の単位・結合coherenceと、G-142のreading射に沿う2可換性も証明する。

### C. scheme版との比較

G-140の生成元忘却からM_P→𝓧_Pを構成する。任意のT→𝓧_Pによるpullbackを、
そのT上の実現に全射q_v:O_T^{m_v}→Q_vを付けるfunctorとして同定する。
これはHomのvector bundle内の全射行列のopen部分であり、m_v≥n_vを使って
representable、smooth、surjectiveになることを証明する。

各実現の自己同型群を∏_v GL(Q_v)の演算保存部分群に同定する。frame上ではGの
stabilizerに同定し、frameを変える共役作用による降下と係数変更との整合を証明する。
大域の基底を仮定せず、qを保持する自己同型が恒等であることを証明する。
Semの対象はq込みの同型類であり、Realの点ごとの同型類へ
忘れる写像と区別する。inertiaが自明な代数stackから得られるalgebraic spaceと、
G-141のopen chartによって得るschemeを区別して結論する。

### W. 同じ実現での検査

ノートW5のrank1、T=0を全Rについて分類し、Real≃B𝔾_mを証明する。
R=ℤでは−1が非恒等な自己同型であり、q=(2,3)を保持する自己同型は恒等になる。
同じ入力から作ったP¹→B𝔾_mがCの写像に一致することを示す。

さらにW1では、基底付き可逆操作の(a,b)=(2,1/2)と(1,1)がqを忘れると
R=ℚ上で同型になることを、その型p,qの二つの基底変更で示す。
生成元付きSemの二点の相違と、Realでの同型性を同時に保持する。

## 前提・構成台帳

| 対象 | 役割 | 出所・構成義務 | 使用先 |
| --- | --- | --- | --- |
| k、P、n≤m | 入力として保持 | ノート§3.1 | A–C |
| 独立Real・fppf descent | 先行構成 | G-140。商stackをRealの定義にしない | B |
| X_P、G作用、Law ideal保存 | 構成・証明義務 | 原始tensor式と基底変更 | A・B |
| frame torsor・逆descent・同値 | 構成・証明義務 | Realの加群と全ての同型 | B |
| Gのsmoothness・有限表示 | 放電義務 | 有限積のGLから証明 | Bの代数性 |
| M、表現同値、reading自然性 | 先行構成 | G-141・G-142 | Bの自然性・C |
| 全射行列open、自己同型計算 | 構成・証明義務 | qと演算を保つ等式 | C・W |
| W1・W5 | 構成・証明義務 | ノート§8の固定入力 | W |

## 完了条件

A–C・WをLeanで証明し、`research/reports/G-143-aat-realization-stack-comparison.md`に
対象・射・descent・代数性の証拠とscheme版との比較を記す。
証拠は`research/lean/ResearchLean/AG/`に置き、
[共通完了基準](../../.codex/skills/target-theorem-loop/references/target-goal-contract.md#共通基準の参照適用)を適用する。

否定の決着には、対象クラス内の具体的なdescent不能データ、代数性の必要条件を
破る実現、またはA–Cの固定比較を破る反例を証明し、`target-refuted`として記録する。
証明APIの未実装は反例ではない。coarse moduliと高次の実現の分類は、この固定targetに
追加せず、別の目標として設計する。
