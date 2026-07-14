# ArchMap・LawPolicy・ArchSig 責務憲章

この文書は、ArchMap / LawPolicy / ArchSig の三層が **何を語り、何を語らないか** の責務境界を述べる。
個々の schema 仕様や編集手順ではなく、なぜこの三分割なのかという理論的根拠を述べる。
編集方針は [guideline.md](guideline.md) を、
入力契約の一覧は [README.md](README.md) を見る。AAT 数学本文(`docs/aat/algebraic_geometric_theory/`)が正であり、本文書はそれに相対化される。

## 問い

**なぜ観測・制度選択・計算を三つの層に分けるのか。** 一つの層が二つの役割を兼ねると何が壊れるのか。

答えの核は責任の所在にある。三層を分けるのは、誤った結論が出たときに
「観測が間違ったのか、ポリシーが間違ったのか、計算が間違ったのか」を切り分けられるようにするためである。
層が混ざると、この切り分けが原理的に不可能になる。だから境界は美意識ではなく、体系が機能するための条件である。

## 中心原則

### 原則1: 観測と判定の分離

ArchMap が書くのは **"X is the case"(世界がこうなっている)** だけである。
**"X is good / bad / violation / mismatch / nonzero"(あるべきと照らした評価)** は一語も書かない。
後者は必ず `ArchMap × (LawPolicy + law-equation-surface + MeasurementProfile) → ArchSig` の計算でのみ生まれる。再現可能な run では三つの選択 artifact を policy-bundle で固定する。

第I部 **公理 A6(Observation Non-Generation)** は
「観測・測定・報告・検査・記録は Atom の成立を生成しない。それらは Atom family に対する読みを与えるが、生成元ではない」と述べる。
ただし A6 が禁じるのは観測による Atom の **存在(existence)** 生成であって、判定の混入そのものは A6 の射程ではない。
判定を観測に混ぜてはならない根拠は、本憲章の **原則1(観測と判定の分離)それ自体** にある——
観測が「読み」である以上、そこに評価を書き込むことは観測者を生成者・裁定者に変え、責任の所在を壊すからである。

### 原則2: 主観には二種類ある —— 守るものと排するもの

観測の主観と判定の主観は、まったく別物である。取り違えてはならない。

- **観測の主観(守る)**: 観測者が source を読んで下す意味の読み取り。
  第I部の semantic Atom は、後期ウィトゲンシュタインの「意味は使用である」を AAT に移したものとして定義され、
  その一意性は意味対象の絶対性ではなく **使われ方の規則に相対化** して与えられる。
  同じ `sendEmail` が、二要素認証のゲームでは検証経路を、ニュースレターのゲームでは配信経路を意味する(PHILOSOPHY.md)。
  この読み取りは本質的に主観的であり、それこそが grep や型解析では出てこない観測である。
  これを機械判定化したら、ArchMap は静的解析に堕ち、AAT が上に載せる計算の土台が消える。**主観はバグではなく機能である。**

- **判定の主観(排する)**: あるべきと照らした評価、どの語彙体系で見るかの選択裁量、ArchSig がやるべき計算結果の先書き。
  これらは観測者の責任を「正しく見たか」から「正しく判断したか」へ膨らませ、責任の所在を壊す。

第I部 **命題 A9** が両者を架橋する。「Atom の存在と Atom の観測は同じではない。観測が完全でないことは、Atom family の存在が曖昧であることを意味しない」。
観測は `obs : F → O` という、情報を忘れうる写像である。観測の主観性・不完全性は許される——それは存在の曖昧さではないから。
だが、観測写像に判定を混ぜることは別の話で、それは観測ではなくなる。

### 原則3: doctrine は固定され、観測者に裁量を残さない

第I部 **公理 A8(Essential Uniqueness)** は、canonical Atom family の一意性が
「source **と** extraction doctrine `(V, Γ, R, ρ, E, N)` を固定したとき」に成立する、という **相対化された条件付き一意性** を述べる。
A8 は複数 doctrine の共存を排除せず、doctrine の固定を要求もしない——
「同じ source でも doctrine が異なれば異なる Atom family が得られうる。これは一意性の失敗ではなく、一意性の相対化である」。
したがって doctrine を単一に固定することは A8 の **要件ではなく**、A8 に相対化された **tool 設計上の選択** である。
本ツールは実務上の単純さと観測者の責任最小化のためにその選択を採る。
理論本文は多 doctrine を許す一般論のまま残り、実務 tool はその一特殊化(単一固定 doctrine)を選ぶ、という関係になる。

その設計選択の下で:

- **理論本文では** doctrine を残す。それは semantic 観測を一意に定める錨であり、健全性の条件である。
- **実務 tool では** doctrine を固定する。語彙体系を観測者が選ぶ・拡張する裁量を与えない。
  観測者は固定された言語ゲームの中で主観的に意味を読むだけになる。
  「どの眼鏡で見るか」を観測者に選ばせることは、観測者を半分ジャッジにする行為であり、原則1・2 に反する。

語彙の **適用**(固定語彙のどれが当てはまるかを主観で読む)は観測の主観として守る。
語彙体系の **選択・拡張**(doctrine)は判定寄りの主観として排する。この区別が肝である。

## ArchMap は何か —— 観測層

ArchMap は、与えられた source から読み取った Atom 証拠を **生のまま** 提示する有限 poset site map である。
書くのは `sources` / `atoms`(component / relation / capability / effect / contract / authority / runtime / semantic)/ `contexts` / `covers`、
そして AG 計測のための per-context の生の section 値・生の関係・生の support である。

ArchMap が書かないもの:

- 評価語(`mismatch` / `violation` / `obstruction` / `risk` / `nonzero` …)。これらは判定であり、ArchSig の計算出力である。
- 比較結果(二つの section が overlap で食い違うか)。比較は ArchSig が生値から計算する。
- 選別(どの関係が obstruction generator か)。forbidden-ness は法であり LawPolicy の責務、minimal support は ArchSig の計算。
- 計算済み成果物(minimal forbidden support、nsdepth certificate、dimension、rank …)。これらは ArchSig が発行する。
- doctrine の選択。語彙は固定。

観測者の責任は「正しく見たか」だけである。「正しく判断したか」は背負わない。

## LawPolicy は何か —— 制度選択層

LawPolicy は、明示した law / lawPair / evaluator / basis / scope / severity を **選ぶ** selector である。退役した policy pack selector は受理しない。
加えて、何が forbidden か(law universe)を指定する。第III部は「law は atom を生成しない、coordinate を生成しない、law は loci を切り出す」と述べる。
law は存在の根拠ではなく、どの witness ideal / defect representative を読むかを指定する装置であり、witness variables と signature axis は supplied law-equation-surface と evaluator registry で解決される。

`law-equation-surface/v0.5.2` は、制度選択が参照する law universe と witness
variables を宣言する一次artifactである。`policy-bundle` はLawPolicy、law
surface、MeasurementProfileをcanonical JSON fingerprint付きで同じrunへ固定し、
run manifestとmeasurement packetにcomponentFingerprintsを残す。

LawPolicy が書かないもの: witness predicate の手書き、signature axis の手書き、score formula、obstruction circuit 定義、measurement profile 本体。
これらは supplied law-equation-surface、evaluator registry、または MeasurementProfile の責務である。
何が forbidden かの **選択** は LawPolicy にある(第III部:law は loci を切り出す)。
一方、forbidden support の inclusion-minimal 列挙や obstruction ideal の構成は、法代数理論では必要な数学的操作として現れるが、
その **実行者は理論上未指定** であり、本ツールでは ArchSig がそれを担うという実装上の分割を採る。

## ArchSig は何か —— 計算層

ArchSig は、`ArchMap + LawPolicy + supplied law-equation-surface + MeasurementProfile` の入力検証が通った `analyze` run で `archsig-measurement-packet/v0.5.2` を作る AG measurement layer である。
**Lean 証明器ではない。** 神の視点も持たない。

判定はすべてここで生まれる。cech defect の比較、minimal forbidden support の enumeration、obstruction ideal、
H^n / Tor / rank / representative の計算、そして `structuralVerdict`。
第VIII部 **定義 11.1** が出力契約を定め、verdict は `measured_zero` / `measured_nonzero` / `unmeasured` / `unknown` / `not_computed` の五値に限られる。

第VIII部 **原則(verdict discipline)** が決定的である。

```
unmeasured ≠ measured_zero
unknown    ≠ measured_nonzero
not_computed ≠ unmeasured
```

`unknown` は「現在の method で決定できない」であって nonzero claim ではない。`unmeasured` は「選ばれた profile の外」であって zero claim ではない。
ArchSig は「分からない」を「ある/ない」に丸めない。

そして第VIII部 **原則2.2(Measurement Is Internal)** と tooling 側の **ウィトゲンシュタイン的責務境界**:
ArchSig は与えられた contract から語れることだけを語り、語れないことには沈黙する。入力 contract を補完・推測・拡張しない。
source extraction の健全性、semantic の正しさ、global lawfulness、未来予測は主張しない。
`analyze` の出力は選択された contract に対する structural verdict と analytic reading である。
`compare` は analyze run の比較記録を作り、`gate` は必須の measurement packet と任意の比較記録に対して gate policy を適用し、CI判断へ写像する。
`refactor-morphism/v0.5.2` は既存 verdict の declared transport compatibility を供給し、
`refinement-comparison/v0.5.2` は coarse-to-fine の class-zero preservation data を供給する。
いずれも conclusion 相当の値を supplied block に入れず、validator 通過時だけ対応する analytic reading を解放する。
RepairPlan の explicit H¹ comparison は、次数0/1/2の有限基底写像表と変数対応を供給し、
ArchSig が差保存・零保存・微分可換性を再計算する。適合条件の宣言booleanは入力として採用しない。

## 三層を混同すると何が壊れるか

具体例で示す。「mismatch を ArchMap に書く」場合を考える(これは仮想ではない——現に
`tools/archsig/tests/fixtures/ag_measurement/archmap_v2_cech_h1_visible.json` の
`atom:left-bottom-cech-mismatch` が `predicate:"mismatch"` を持ち、これを体現している。以下の破損は現状そのものである)。

観測者が「left と bottom は overlap で食い違う(`mismatch`)」と ArchMap に書き、ArchSig がそれを数えて H1 を出すとする。
このとき H1 の計算は形式上は正しい代数(potential recovery による coboundary 判定)だが、**入力 `e_ij` の各成分は観測者の判定**である。
結果として:

- **責任の切り分けが壊れる。** H1 が nonzero と出たとき、それが「本当に大域的な貼り合わせ障害」なのか「観測者が局所比較を間違えた」のか「ポリシー選択が悪い」のか分離できない。
- **計測が判定の言い換えに堕ちる。** ArchSig は集計器になり、「計測している」という主張が空洞化する。観測者がすでに下した判定を、代数の衣をまとって追認しているだけになる。
- **観測者の責任が膨張する。** 観測者は「正しく見たか」に加えて「正しく比較したか」を背負い、原則2 の観測の主観と判定の主観が混ざる。

正しい姿は、ArchMap が per-context の生の section 値を書き、ArchSig がそれを比較して `e_ij` を計算することである。
このとき観測者は「left は overlap で a、bottom で b」と書くだけで、「食い違う」とは言わない。比較=判定は ArchSig が独占する。

同じことが obstruction 選別(誰が obstruction かを観測者が決める)、certificate 先書き(計算結果を観測者が貼る)にも当てはまる。
いずれも「観測者が ArchSig の仕事を代行している」点で同じ病である。

## AAT 本文への対応(引用)

本文書の原則は AAT 数学本文に裏づけられる。本文は正であり、本文書はそれに相対化される。

| 原則 | 典拠 |
| --- | --- |
| 観測は Atom の **存在** を生成しない(判定排除の根拠は本憲章の原則1) | 第I部 公理 A6(Observation Non-Generation) |
| Atom の存在と観測は別、観測は情報を忘れうる写像 | 第I部 命題 A9(観測不完全性と存在一意性)、`obs : F → O` |
| doctrine を固定したときの相対化された一意性(多 doctrine を許す。単一固定は tool の設計選択) | 第I部 公理 A8(Essential Uniqueness)、`(V, Γ, R, ρ, E, N)` |
| semantic は「意味は使用」で相対化された主観的観測 | 第I部 semantic Atom 定義、PHILOSOPHY.md |
| law は atom / coordinate を生成せず loci を切り出す | 第III部 Law Algebra |
| 計測出力契約と五値 verdict | 第VIII部 定義 11.1 |
| verdict discipline(unknown ≠ nonzero ほか) | 第VIII部 measurement verdict discipline |
| 計測は理論内部の reading、外部妥当性を主張しない | 第VIII部 原則2.2(Measurement Is Internal) |
| ArchSig は contract 内だけ語り沈黙する | README.md / AGENTS.md / CLAUDE.md ウィトゲンシュタイン的境界 |

## 関連文書

- [guideline.md](guideline.md) —— tooling の編集方針と検証コマンド。
- [README.md](README.md) —— 入力契約と現行 boundary statement の一覧。
- [PHILOSOPHY.md](../../PHILOSOPHY.md) —— プロジェクト全体の思想基盤。
