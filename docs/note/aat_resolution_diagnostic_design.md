# 解像度診断の設計ノート — defect 意味論と observation factorization

本ノートは設計考察ノートである。AAT 数学本文(第I部〜第X部)を変更せず、
新しい公理・定理を理論本文へ導入しない。ここで固定するのは、G-104 Atlas 定理の
必要十分化プログラム(G-107 初版〜v2)が5世代の exact 反例と Stop B 終端で
閉じた経緯を**設計の水準で**再読した結果と、その帰結としての成果物の分割、
および G-107 v3 以降のカード設計の根拠である。ここに現れる定義・statement は
GOAL カードと将来の本文改訂のための candidate であり、本ノート自体は正本では
ない。

参照(証拠。証明根拠ではない):

- [G-104 report](../../research/reports/G-104-aat-resolution-invariance.md)
  (Atlas 定理 = 条件 C の十分性定理)
- [necessity-map hunt report](../../research/experiments/g104-necessity-map/hunt-report.md)
  (候補系譜 v1–v5、反例群、`G_local-v1`、Stop B)
- `research/experiments/g104-necessity-map/results-stop-b-summary.json`
  (2点分離の恒久証拠)
- [表示的意味論ノート §10](aat_denotational_semantics_of_architecture.md)
  (診断 local-system 構想、`Z_univ`)
- G-107 カードと PR #3955 のレビュー往復(反例の三重検証記録)

---

## 1. 何が起きたかの要約

G-104 の Atlas 定理は「条件 C ⟹ H¹ comparison 全単射」の十分性定理である。
その必要十分化(一様不変性 ⟺ 有限 syntactic 条項系)を狙った探索は、次の
系列で終端した。

| 世代 | candidate | 反例 | 破れの方向 |
| --- | --- | --- | --- |
| v1 | DIRECT | Chain3 | 必要性(uniform だが swap 推移連鎖が未認証で条項破れ) |
| v2 | COMPONENT | UnkilledTwin | 十分性(共出現 ≠ 差消滅) |
| v3+sa | CERTIFIED + support-active | CONTRACTIBLE-TRIANGLE | 必要性(H¹-neutral な filled face) |
| v4 | JOINT-COLLAPSE | NONFREE-MUTUAL-KILL-SPLIT | 必要性 |
| v5 | COORDINATE-DOUBLED | TERNARY-CYCLE-3 | 必要性 |
| v3+sa(再) | 同上 | PROPER-CHAIN3-PLUS-BRIDGE-DIGON | 十分性(bridge lift の digon) |

さらに人間裁定で観測 grammar `G_local-v1`(半径1 typed ball を含む登録
観測成分。正確な成分表は恒久 contract を正本とする)を
固定した上で、`TERNARY-CYCLE-3 / 6` の2点分離により
**`CSTAR-not-expressible-in-G_local-v1`**(Stop B)が確定した。false negative
と false positive が交互に現れ、最後に観測 grammar 相対の分離不能性が立った —
この全体は個別の候補の失敗ではなく、探索というゲームの設計に対する証拠として
読むべきである。

## 2. 中心構図: observation factorization

正本に据えるべき数式は一つである。comparison data の圏(G-103 / G-104 の
確定構成)の上で、exact な defect 意味論

```text
J : ComparisonData → DefectProfiles
J_A(f) := (dim ker H¹(f_A), dim coker H¹(f_A))   (非空 A ごと)
```

を考える。このとき:

```text
ComparisonData ── J ──▶ DefectProfiles
      │                       │ zero?
    Obs_G                     ▼
      │                      Bool
      ▼                       ▲
Observation ────── p ? ───────┘
```

- **一様不変性** = 零判定 `∀ nonempty A, J_A(f) = (0, 0)`。
- **十分条件** = `C(data) → J(data) = 0` という含意。
- **exact な構造的特徴づけ** = 零判定が観測写像 `Obs_G` を通して
  **factor** すること(`zero? = p ∘ Obs_G` なる `p` の存在)。
- **Stop B** = `G_local-v1` に対してその `p` が存在しないこと(T3 / T6 の
  2点分離)。
- **repair / modification** = data の変形により `J` を零へ近づけること。

この構図の下で、5世代の反例史は「固定 observer の情報量では exact zero-locus
が factor しない」ことの徴候として一元的に読める。kernel / cokernel の両側性は
`J = (ker, coker)` の内部構造であり、成果物の分割(§4)は章構成であり、
いずれも factorization を中心に従属する。

## 3. 反例史の機構再読

### 3.1 条項の役割分類

C / C\* の条項族に「余核側の語彙が無かった」わけではない。役割はおよそ
次に分類できる。

- **coverage / kernel control**(粗側の生成元・関係を細側で失わない):
  C2\*・C4\*・C6\*、C1\* の port 非空性。
- **descent / cokernel control**(fine-only の自由度を同一視・消滅させる):
  C1\* の連結性、C3\* の fiber acyclicity、C5\* の swap 連結性。
- **support / block alignment**(どの A-block を比較しているかの整合):
  C0\*。
- **reduction stability**(presentation の差をどこまで無視するか):
  FaceTwin 類・one-pass free-pair 除去・criticality。

### 3.2 系統的欠陥は2軸

1. **coarse-anchored visibility**: 余核制御を含む全条項が coarse-critical
   data に索引付けされていた。PROPER-CHAIN3-PLUS-BRIDGE-DIGON は、粗側で
   非 critical な bridge の上に fine-critical な digon が生じることでこの
   索引を破る。欠けていたのは fine 側の新しい topology を粗側の検査対象へ
   反映する reflection である。
2. **presentation sensitivity**: 意味(H¹)を変えない構造展開に条項系が
   反応する。CONTRACTIBLE-TRIANGLE(filled face の H¹-neutral 展開)、
   TERNARY-CYCLE 系列(neutral relation cycle の長さ)がこの軸の証人で
   ある。

「条項族は片側設計だった(余核側の語彙欠落)」という読みは症状としては
分かりやすいが機構分類としては粗く、上の2軸が正確である。

## 4. 成果物の四分法

この層で理論が提供すべき deliverable は次の4種であり、混同してはならない。

1. **exact diagnosis(計算)**: `J_A` の定義と、一様不変性の decidable な
   零判定。値部分集合還元(law 全量化 → 有限個の非空 `A`)+有限次元 `ℚ`
   線形代数で決定可能になる。ただし現時点の engine `is_uniform()` は強い
   exact evidence であって Lean の正本ではない — **還元定理と
   sound / complete decider の確立自体が第一の成果物**である。
2. **structural certificate(構造条件)**: 十分条件は iff である必要が
   ない。価値は「各条項=名指しできる失敗機構の排除」という**機構カタログ**
   にある: 安価な sufficient certificate、人間が読める説明、合成・局所
   変更に耐える proof object、failure mechanism と repair 方向の分類。
3. **expressivity limit(観測限界)**: どの observer では零判定を特徴づけ
   られないかの定理。Stop B(`G_local-v1` 非分解性)はその最初の実例で
   ある。
4. **modification calculus(変形)**: cell 追加・除去・refinement・合成が
   `J_A` をどう変えるかの計算規則。repair を tooling ではなく comparison
   geometry 上の変形理論として置く。機構カタログの各 entry を
   「obstruction signature / `J_A` への寄与または上界 / それを排除する
   sufficient certificate / defect を減らす elementary modification」の
   4点組にすると、反例カタログがそのまま理論になる。

iff ハントの敗因はこの分割の混同にある: (1) がすでに決定可能である以上、
条項系に判定を competitively 再現させる理由はなく、(2) の説明的価値は
iff を要求しない。「制約された局所・説明的語彙で exact iff を得る」という
ゲームだけが敗北した — 任意の decidable 性質は判定結果の answer-encoding で
自明に「特徴づけ」られるため、観測限界 (3) は語彙の資格制限(半径・成分・
禁止情報)に**相対して**のみ意味を持つ。将来 iff を再び問うなら、observer
grammar の階層・観測コスト・compositionality・anti-answer-encoding を目的
関数として先に固定する。

## 5. 記号の統一: `J_L` と `J_A`

表示的意味論ノート §10 の診断 local-system 構想は law family `L` ごとの
jump data `J_L := (dim ker, dim coker)` を用い、`Z_univ = { f | ∀ adequate
L, J_L(f) = (0, 0) }` を定義した。本ノートの `J_A` は block 別の defect
profile である。両者は別物ではなく、値部分集合還元によって結ばれる同一
対象の二座標である:

```text
∀ adequate L, J_L(f) = (0, 0)   ⟺   ∀ nonempty A, J_A(f) = (0, 0)
```

(左辺 = law 量化の semantic 座標、右辺 = 有限 block の computational
座標。還元定理はこの座標変換の正当化である。)`Z_univ` は `J` の零 locus で
あり、Atlas 定理の位置(§6)は零 locus に対する包含として述べられる。

## 6. G-107 v3 への設計帰結

以上から、G-107 v3 は**新しい条項系候補を含めず**、次の三本柱で固定するのが
設計として正しい。

1. **defect 還元と決定可能性**: `J_A` の定義、一様不変 ⟺ `∀ A, J_A =
   (0, 0)`(還元定理の `J`-版)、computable presentation 上の
   sound / complete decider。
2. **Atlas positioning**: 幾何述語 `ConditionCAllA`(G-104 の law 非依存
   条項 C0・C5・C6 と、C1–C4 の label-block 評価を全非空 `A` の
   A-subnerve 評価へ移した読み替え条項の conjunction)⟹ 零 defect を、
   bridge theorem(`ConditionCAllA → ∀ laws, ConditionC`。label の値
   fiber と `A` の対応= (1) の還元機構の再利用)+ G-104 受理済み
   pointwise theorem の2段で固定する。Lean 実体の `ConditionC` は
   law-indexed(C1–C4 が `LawValueLabel` 量化)であり、素朴な量化交換は
   不可 — この bridge 構成は 2026-08-11 の claim scope 裁定(案b)で
   確定した。C0–C6 の各条項が個別には必要でないこと(7 witness)と
   あわせ、`Condition-C locus := { M | ConditionCAllA M }`(幾何決定
   可能)について `Condition-C locus ⊊ uniform locus` という包含の
   真性が定理水準で立つ。
3. **observation nonfactorization**: 恒久 `G_local-v1` の忠実 `Obs_G`、
   T3 / T6 の観測等値と反対 label、任意の `p` に対する factorization
   不可能性(grammar 相対。量化域は computable presentation 全体に限定
   する — abstract geometry への拡張は presentation 存在と変更不変性を
   要するため candidate にとどめる)。

この3本で `Condition-C locus ⊊ uniform locus` かつ `uniform locus は
G_local-v1 を通して定義不能` という **Atlas 定理の正確な位置**が初めて
定まる。claim を痩せさせる撤退ではなく、計算・certificate・観測限界・変形を
混ぜずに位置を定める改訂である。

現 C\*(CERTIFIED-v3 + support-active)は active claim から除外し、両方向の
exact 反例(CONTRACTIBLE-TRIANGLE / PROPER-CHAIN3-PLUS-BRIDGE-DIGON)を持つ
研究史・mechanism artifact として保存する。中心補題候補だった certificate
閉包(blocker `PB-R2-NONFREE-GLOBAL-FACE-CHAIN` の定理化)は、後継の
structural certificate 設計(G-108 以降)の素材へ移る。

## 7. G-108 以降の素材

- **structural certificate の再設計**: 機構カタログ(§4 の4点組)を先に
  整備し、各条項が排除する defect mechanism と、合成・presentation 変更に
  対する振る舞いを固定してから、criticality-reflection 型条項を含む後継
  certificate を設計する。v6 ハントの再開はその後である。
- **modification calculus**: elementary modification の目録と `J_A` への
  作用。第V部 repair 系譜(repair cochain、conormal first-order descent)
  との接続。
- **observer 階層**: 半径 `r` 一般化(`T_n` 族の `n > 2r+1` 論法による
  分離の witness 族化)、大域情報1成分の追加で特徴づけに届くかの判定 —
  いずれも**未証明 candidate** であり、成功見込みとして前提化しない。

## 8. 方法論的教訓

1. **bounded zero-result を方向の安全性と読まない**。CERTIFIED-v3 の
   checkpoint 時点 1,918 case 二方向反例ゼロは bounded 証拠であり
   (2,166 は Round 15 の v5 用 union)、十分性方向には候補系譜で反例史
   (UnkilledTwin)があった。「この方向は安全」という要約が反例の
   一世代後に覆るのは、要約が証拠の型(bounded / 一般)を落とした
   ときである。
2. **観測限界の定理は語彙の資格制限に相対してのみ意味を持つ**。
   anti-answer-encoding の規律なしに「iff 不可能」を語らない。
3. **決定可能な性質に対して条項系へ判定を再現させるゲームを設計しない**。
   条項系の価値は判定の再現ではなく機構の説明にある。この分割を GOAL 設計の
   段階で固定する。
