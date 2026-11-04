# G-138：実比較への接続と整数構成

## 1. G-125の実入力

Dでは、原係数の `faceEmptyCechComplex` をC、`lawGeneratedComplex`をDとする。
後者の有理線形群を加法群または整数加群として忘却する。前者の係数を有理化しない。
既存の `actualCechCoefficientCochain0/1/2` をそのままφの成分へ移し、
`actualCechCoefficient_comm0/1` からcochain性を証明する。
元の高次数はface-empty構成の空積から零性を示し、同型の評価APIを用意する。
元のactualMismatchはtransition+d(localState)なので、d_C a=zを満たす補正の
実適用はlocalState−aである。`actual_mismatch_adjust_local_state`へ−aを渡し、
修復後の元の不一致が零になることを証明する。補正aと実際の更新−aの符号を保持する。

比較する対象は次の通り。

| 元の対象 | 一般理論へ渡す値 | 必要な同定 |
| --- | --- | --- |
| `ActualCechAffineLocalData.actualMismatch` | z | 元のcocycleと次数1の代表 |
| 診断ChartCoordinate→ℚの補正 | b | 元の`lawGeneratedD0`とd_D |
| `actualCechCoefficientCochainMap` | φ | 全三次数の同じ加法準同型 |
| `actualCechDiagnosticH1Map` | H¹φ | 元のAdditiveCechH1と診断H¹商の可換図式 |
| `integralCorrection` | a₀ | `actual_mismatch_eq_d_integralCorrection` |
| `actualCechPullback0/1`と`generatedPullback0/1` | α,β | d⁰と比較の可換性、空な高次数の延長 |

DのA適用には共通label条件やReflectionConditionを加えない。
それらは既存床補正をa₀として使う段階だけの入力条件とする。
reading変更で床補正の厳密な自然性を仮定しない。輸送したa₀も補正であることを証明し、
新しい側で別に生成したa₀との差はBの選択独立性で処理する。
G-125の条件を満たす全入力で接続し、例だけの同型で代替しない。

## 2. 有限表示整数群のdecode

各次数の群をZ^n/im Rとして与える。微分行列A、比較行列Fについて、
A R_source、F R_sourceの各列が終域の関係像に入ること、d¹d⁰と
F¹d_C⁰−d_D⁰F⁰が関係像に入ることなど、次数0–2の全条件を検査する。
z,bの代表からd_C¹z=0、d_D⁰b=F¹zも商で検査する。
一般の有限表示はtorsionを含み、異なる整数代表を同じ群の元として扱う。

Liftの判定を、未知数x（C⁰の代表）、u,v（関係の証人）の整数系へ還元する。

```math
\begin{pmatrix}A_C^0&-R_C^1&0\\F^0&0&-R_D^0\end{pmatrix}
\begin{pmatrix}x\\u\\v\end{pmatrix}
=\begin{pmatrix}z\\b\end{pmatrix}.
```

解から[x]∈C⁰を復元し、逆に任意のLiftから関係の証人u,vの存在を導く。
この整数系の全解とLift自体は異なる。u,vの選び方、xの関係による変更を除いた
[x]の全体を回収し、差の像をker kφの有限表示へ同定する。
特解と整数核の射影像・関係を計算し、群の表示として全Liftへの両方向対応を与える。
一意性はこの商での核の零性で決め、補助未知数を含む整数核の零性では決めない。

停止する整数消去はunimodular変換を伴うSNFまたは同等の正確な整数算法を使う。
変換前後の解の同値、算法の停止、対角系の整除条件、零行矛盾をLeanで証明する。
整除鎖そのものを使わない算法を採ってもよいが、全整数入力での停止・完全性・全解復元は保つ。
既知の対角化結果を入力にした条件付き定理は補助APIに留め、原始入力producerを別に閉じる。

有限表示同型で元・射・代表を運んだとき、計算した判定と復元解はCの同値に一致する。
出力基底や特解の選択の字面一致は要求しない。元の群の解と作用の対応を要求する。

## 3. ArchSigとの関係

現行v0.6.0には整数fiber/SNF、局所族の大域持ち上げ、全解表示、元Assignmentの
一意性検査がある。新しい理論は、比較先で指定されたbに対する障害・fiber・作用を
それらの計算と対応させる。初めて修復を計算する理論とは位置づけない。

将来の処理系接続では、同じAtom定義・Law・ArchMap・changeから作る補正と比較を
原始位置・parameterへの復元とともに保持する。一般の複体を作れたことから、
元の構文の更新とcochain補正が一致することは自動では得られない。
有限列挙や非線形の全変更を、本GOALの線形torsorへ一律に読み替えない。

parameter pから補正aへの写像ρが非単射なら、aの一意性からpの一意性は従わない。
同じ許容Assignment域のfiberを別に検査するか、その域でρの単射性を証明する。
W6でこの差を固定する。現行repairは元Assignmentが一意の場合にだけ対象を生成する。
候補18から任意の特解を自動採用する仕様変更を導かない。

ArchSigのRust実装と局所診断・保存結果の性能改善は処理系の仕事である。
本GOALの完了はLeanのA–E・Wで判定し、Rust接続や速度向上は条件に加えない。
