# G-130：全変更範囲の相対修復を合成・分類するための構成

[固定target A–FとW1–W5](../../goals/G-130-aat-relative-repair-composition.md)の証明方針を定める。
入力・結論・完了条件はGOALに従う。以下の分割は証明依存による設計であり、
各段階の実行・査読・PRの記録はtracking Issueへ置く。

## 1. 一次仕様との対応

| GOAL | [n1017](../../../docs/note/n1017_aat_relative_boundary_repair_and_observation.md) | 構成の要点 |
| --- | --- | --- |
| A | §2.1–2.2・2.5、§3.1の系 | 実操作の固定とcochainの零、許された再同定と次数0の制限 |
| B | §2.3–2.5 | 次数ごとの完全列、再同定の延長、局所差と実defectの接続 |
| C | §2.6・3.1 | 候補を残した内部変数消去、対象・射の相互逆、共有セルの厳密一致 |
| D | §3.4 | 同じ面座標の商、双対分離、証拠支持の極小横断集合 |
| E | §3.2・3.5–3.6 | 一点環境、記号的右辺、実分解からの縮約・復元・自然同型 |
| F | §5.1 | 全アフィン写像の全核、実輸送、実修復と作用の往復 |
| W1–W5 | §5.8、§2.5、§5.6、§5.7、§5.2 | GOALの指定データを同じ一般定理へ適用 |

## 2. 既存宣言の再利用と新しい対応

以下のResearch pathは `research/lean/ResearchLean/AG/` からの相対である。
宣言の参照版はactive化時にtracking Issueへ固定する。

| 既存path・宣言 | そのまま再利用する部分 | 新しく構成・証明する部分 |
| --- | --- | --- |
| `TransportCoherence/FinitePresentation.lean` の `FiniteTransportPresentation`、`RewritePasting` | 頂点・型付き辺・面・3-cell、前後の文脈を持つ書き換え | 閉じた部分表示、包含、制限、全セルを覆う有限被覆 |
| `AbelianLiftingObstruction/OriginalTowerPresentation.lean` の `OriginalTowerPresentation`、`toTower` | 元辺・core・基準持ち上げと実核輸送 | 各部分表示への入力の制限、固定実操作との一致 |
| `AbelianLiftingObstruction/Cochains.lean` の `C0`–`C3`、`d0Hom`–`d2Hom`、`d1_d0`、`d2_d1` | 同じ経路・輸送による微分 | 制限との交換、相対複体、範囲ごとの部分複体 |
| `AbelianLiftingObstruction/Cohomology.lean` の `cochainComplex`、`firstShortComplex`、`secondShortComplex` | 加法群のnativeな複体とコホモロジーの計算表示 | 相対・範囲付き複体のコホモロジーと同じ商の対応 |
| `AbelianLiftingObstruction/Solutions.lean` の `Solution`、`solutionCorrection`、`solutionOfCorrection`、`solution_nonempty_iff_correction` | 独立した実解と核補正の往復 | 固定部分・禁止候補を保つ往復、groupoidの対象と射 |
| `AbelianLiftingObstruction/VertexGauge.lean` の `vertexGauge_correction`、`vertexGauge_edge_arrow` | 元の実射とcochain上の作用の一致 | 相対作用、射の制限・貼り合わせ、自己同型と $`H^0`$ |
| `AbelianLiftingObstruction/H1Classification.lean` の `solutionOrbitEquivH1` | 元解の頂点作用による軌道と $`H^1`$ | 範囲付き作用groupoidと相対torsor、descent |
| `AbelianLiftingObstruction/ReferenceLiftInvariant.lean` の `solutionChangeReference`、`defect_changeReference`、`obstructionClass_changeReference` | 同じ実解を保つ参照持ち上げの変更 | 候補のアフィン固定条件の同時輸送、局所生成との交換 |

有限消去、共有関係、groupoidの合成、内部辺分割、アフィン実現は、上表の既存結論から
必要な対応を新規に構成する。一般の群拡大への特殊化では元辺を恒等とする既存経路と、
Fの任意の元アフィン辺の経路を区別し、Fでは `OriginalTowerPresentation` の元辺を保つ。

## 3. 相対化から全修復groupoidへ

閉じた部分表示のセルは元のセルの部分型として表し、経路と書き換えの所属を追う。
制限の合成・恒等・微分との交換を先に揃える。零延長は各次数の全射性の証明に使い、
複体の写像として必要なのは制限と差写像である。

相対補正を独立した実修復に往復させた後、元の0-cochainを射として持つ作用groupoidを
構成する。射の合成は和であり、異なる作用元の同一視を行う前に自己同型を計算する。
禁止候補については $`d^0b`$ の該当成分も零となる部分群を使う。

Bの二領域descentでは、共有部分の0-cochainを一方へ延長して対象を厳密一致させる。
射の全忠実性は共有頂点上で一致する0-cochainの一意な貼り合わせから得る。
局所差の符号は差写像 $`r_U-r_V`$ と合わせ、持ち上げ $`(-h_U,-h_V)`$ の微分が
$`(\delta|_U,\delta|_V)`$ になることから接続像を求める。

## 4. 局所線形消去と厳密合成

有限生成の入力には明示した有限体演算・有限添字・実核の基底と実座標の対応を使う。
相対辺空間を $`X_i\oplus Z_i`$ に分け、$`X_i`$ に含めるのは非共有の常時許容辺だけとする。
行簡約から像の基底、商写像、線形section $`s_i:\operatorname{im}D_i\to X_i`$ を生成する。

局所の座標化と復元にはn1017の次の式を使う。

```math
\operatorname{rec}_i(z,k)=(s_i(r_i-F_iz)+k,z),\qquad
\operatorname{coord}_i(x,z)=(z,x-s_i(r_i-F_iz)).
```

作用の内部成分は $`\gamma_i b=a_i b-s_iD_i a_i b`$ と構成する。
$`D_ia_i+F_ic_i=0`$ から $`(z,k)\mapsto(z+c_ib,k+\gamma_ib)`$ が対象条件を保ち、
復元が元の $`d^0b`$ と交換することを示す。共有辺の値は $`z_i`$ に全て残っているため、
共有部分への制限は内部の $`k_i`$ に依存しない。

Glueの対象には共有辺の一致、射には共有頂点の一致を課し、セルごとの一意な
貼り合わせで大域の補正と再同定を得る。局所式の相互逆性とこの一意性により、
大域でも両合成が対象・射で恒等になる。
公開関係の解から内部成分を零として一つの実修復を作り、内部成分全体を動かして全解を戻す。
各 $`S`$ の解を先に列挙する代わりに、生成済みの候補座標へ零条件を課す経路を用いる。

被覆・sectionなどの表示変更は $`\operatorname{coord}'\operatorname{rec}`$ で比較する。
中間消去では未組立ての領域との共有辺と全候補を残し、比較の合成則を同じ復元から導く。

## 5. 双対分類と再利用

大域の常時許容列の像を商に取り、局所合成後の消去と同じ可解性・復元を与えることを示す。
候補列は名前付きで残し、有限次元の双対分離を $`o\notin\mathsf R_S`$ へ適用する。
得た評価の支持集合から横断集合条件を作り、包含極小性を移す。
有限体上では双対評価も有限データで扱え、空の支持・空の証拠族も同じ定義で計算する。

記号的右辺では $`r_i`$ の項だけをアフィンに変える。
kernel・section・作用の線形部分が $`r_i`$ に依存しないことを用いて更新則を示す。
G-131へ渡すのは、生成された同じ行列・候補名・実defectへの対応・復元写像である。

文脈同値の逆向きでは共有修復値 $`t`$ の各辺に平行な禁止候補を追加し、
基準実操作を $`\tau_{t_e}\widetilde L_e`$ とする。元の辺との恒等比較の面から
$`h_e=t_e`$ を導き、二領域の共有関係の差を検出する。

## 6. 内部辺分割

まず有限表示の全ての辺出現を置換し、面と3-cellの終点・書き換え順序を保つ。
実分解の輸送平方から $`\rho_e=\rho_2\rho_1`$ と縮約式を得る。
逆関手の補正を $`(0,h_e)`$、新頂点の再同定を $`\rho_1b_s`$ とし、
自然同型の新頂点成分を元の $`h_1`$ とする。

複体の新自由度は $`b_w-\rho_1b_s`$ と $`h_1`$ を座標に取ると恒等微分の二項複体になる。
この分解からコホモロジーと障害の比較を作り、常時許容列の像が一致することから
公開関係・候補列・双対証拠支持も対応させる。
新頂点での自由度を持つ実修復の対象集合と、再同定後の分類をそれぞれ計算する。

## 7. 証明の依存順と検証

| 数学的な段階 | 依存 | 終了時に対応させるもの |
| --- | --- | --- |
| 部分表示・相対修復、アフィン実現 | G-129 | A・Fの実辺、微分、固定条件、対象・射 |
| 全補正のdescent・相対障害 | A | B・W5、範囲付きの反例W2 |
| 全範囲の有限生成と合成 | A・F | Cの相互逆とW1・W3、表示比較 |
| 双対分類・記号的更新・文脈同値 | C | D、Eの該当項、G-131へ渡す同じ行列 |
| 内部辺分割と全体の指定例 | A・C・D | Eの比較、W1–W5の一般定理への接続 |

Leanの検証は[AAT guideline](../../../docs/aat/guideline.md#lean-build-運用hard-rule)に従う。
親が指定する単一の非aggregate fileのfocused checkを基本とし、必要な依存moduleだけを
親がtargeted checkする。Research package全体のbuildは実行しない。
完了時にはGOALの全条項と宣言、実操作への往復、前提の生成・使用、指定例をreportで対応させる。
