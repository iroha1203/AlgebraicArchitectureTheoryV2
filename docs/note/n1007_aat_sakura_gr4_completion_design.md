# SAKURA 海域と Gr4 完了設計 — 命名記録と後続カード6枚の定義

本ノートは考察ノートである。新しい公理・定義・定理は導入せず、証明済み定理の
statement を変更しない。目的は二つある。第一に、Gr 階梯が立つ海域の固有名
**SAKURA** の命名を記録する。第二に、Gr4 完遂 gate 5項を閉じる後続カード
6枚(G-111〜G-116)のラインナップを定義する。将来の statement はすべて
未証明の candidate であり、カードの起票・昇格・採否はユーザー裁定に従う。
lifecycle の経緯(PR・Issue・cycle 履歴)は各 report と tracking Issue を
正本とし、本ノートには持ち込まない。

## 要旨

1. Gr 階梯(Gr0–Gr4、n1001 §3.5)が立つ海域の固有名を **SAKURA** と定める。
   説明名は **Sea of Coherent Readings**。命名体系は山頂の呼び名 SHIGURE
   と同じ register(季語の大文字ローマ字+数学の像を写す情景+英語
   backronym)の拡張である。
2. 命名の証明根拠は範囲併記で固定する — **開花宣言** = G-110 完遂
   (Gr0–Gr3 の完全証明+Gr4 exact-bottom 第一手)、**満開** = Gr4
   capstone 完遂。開花と満開の二段観測に倣い、G-109 の Gr3 記録様式
   (範囲併記)を命名側にも適用する。
3. Gr4 は G-110 だけでは閉じない。完遂 gate 5項(正本 = G-110 カード
   program context)を単責務6枚で閉じる — G-111 schema / G-112 全域分類 /
   G-113 診断分類 / G-114 refinement / G-115 上段 lift / G-116 capstone。
4. 起票は draft 6枚の一括、昇格は G-111 から一枚ずつ。昇格レビューの
   右サイズ化(Claude 3レーン+Codex 2巡上限)は提案であり、G-111 昇格前に
   正式裁定する。
5. G-116 capstone が Gr4 達成 = SAKURA 満開を記録する。満開は Atlas 補強
   論文(n1006)の着手条件を解く。

## 参照

**正本**(事実関係の判定基準):

- [G-110 カード](../../research/goals/G-110-aat-doctrine-fiber-product.md)
  (Gr4 完遂 gate 5項・(D) full-domain 移管・frontier の正本)
- [G-110 report](../../research/reports/G-110-aat-doctrine-fiber-product.md)
  (完了判定 = `target-theorem-proved`)
- [G-109 カード](../../research/goals/G-109-aat-cross-stage-coherence.md)
  (Gr3 達成記録と範囲併記の様式)

**上流考察ノート**(定義・分割の初出。正本ではない):

- [n1001](n1001_atom_is_all_you_need_discussion.md)(§3.3 塔、§3.5
  達成階梯 Gr0–Gr4)
- [n1004](n1004_aat_denotational_semantics_of_architecture.md)(§10
  SHIGURE の呼び名と backronym の初出、§11 研究プログラム命名記録)
- [n1005](n1005_aat_semantic_geometry_route_after_g107.md)(§4.3
  五層分解、§5 隊列、§7 論文B「連合する読み」)
- [n1006](n1006_aat_atlas_reinforcement_plan.md)(Atlas 補強計画 —
  着手条件が Gr4 完了)

## §1 SAKURA — 海域の命名記録

**命名対象**: Gr 階梯が立つ海域。G-106 / G-108 / G-109 / G-110 が渡った
水域であり、後続6枚が満開まで渡り切る。

- 固有名: **SAKURA**。表記は大文字ローマ字(SHIGURE と同 register)。
  日本語文中は「SAKURA 海域」と書く。
- 説明名(英名): **Sea of Coherent Readings**。内容名として固有名と併用
  する(論文B「連合する読み」n1005 §7 と連動)。
- backronym: **Semantic Ascent through Kartesian Universality and
  Relative Alignment**。kartesian は fibration 文献の綴りを採る。
  Ascent = 上昇(登路と海面)、Kartesian Universality = fiber product の
  普遍性と carrier 大域 cartesian lift(G-110 (A)(B))、Relative
  Alignment = 終対象を置かない相対原理と段横断整合(Gr3)。全語が
  証明済み内容に対応する。
- 命名日: 2026-08-25(G-110 完遂日)。

**情景**(SHIGURE の「片時雨 = descent 貼り合わせの写し絵」と同じ役割):

- 桜前線は列島を段階的に北上する。海域は上昇する海の一段であり、前線が
  届いた水域が咲く。Grothendieck が Récoltes et Semailles で語った
  「上昇する海(la mer qui monte)」への敬意は、人名でなく方法の像を
  経由して一段抽象化された形で残る。
- 開花の報は合格電報の言葉(サクラサク)と重なる。この体系では証明が
  立った時にだけ名が付くから、咲きは常に実である。
- 「満ちる」という動詞は潮と花に共有される。満ち潮と満開が同じ言葉で
  進行を刻む。
- 季節の弧: 晩春(SAKURA)から初冬(SHIGURE = 山頂)へ。命名体系
  そのものが登路の一年を刻み、後続の海域名にも季語の続きが自然に控える。
  次の海域の命名は、その海域の開花の時に行う。

**二段記録(範囲併記)**:

- **開花宣言** = G-110 完遂(2026-08-25)。証明根拠は Gr0–Gr3 の完全証明
  (Gr3 = G-106+G-108+G-109 の三点セット、範囲は G-109 カードの記録に
  従う)+Gr4 exact-bottom 第一手(G-110 — 有限 presentation 付き
  (realization 像)底層射上の全域 lift exact-bottom・diagnostic-covariant
  subcalculus)。
- **満開** = G-116 capstone 完遂(Gr4 達成記録)。満開の条件は §5。

**運用**:

- outreach で SAKURA を使うときは Gr 階梯の経緯を一段添える(Atlas 命名の
  運用と同型)。
- 航海記事は海域の固有名を記さない方針を維持する。
- 俗語の読みへの反論は体系が内蔵する(開花 = 完了判定)。

**衝突調査(2026-08-25)**: 数学圏に SAKURA を冠する定理・予想は検索で
確認されない。近接分野では暗号の Sakura(tree hashing の coding)と
サイドチャネル評価ボード SAKURA-G / X、国内技術圏にさくらインターネット・
サクラエディタがあるが、いずれも海域名の使用域と重ならない軟衝突である。

## §2 Gr4 完遂 gate(正本の整列)

正本は G-110 カード program context。本節は番号の整列のみを行う。

- **gate (i)**: 全 semantic exact-bottom への coverage 拡張と全域作用・
  分類+(D) 診断 base change の full-domain 化(source-fiber incidence
  資格の解除 = global / indexed base-change schema の建設)。
- **gate (ii)**: refinement 系統(`RefinementDoctrineHom` の圏化と
  refinement base change)。
- **gate (iii)**: 上段(`GeomRead` / `ObProblem`)への base-change lift
  (Gr3 段横断輸送への接続 bridge)。
- **gate (iv)**: IsIso 水準の Beck–Chevalley exchange-failure の存否決定
  (存否は未決定の問い。本 sector と refinement / 上段 regime を含む
  設定で決定する)。
- **gate (v)**: 診断保守性・反射・orbit exactness の分類。

## §3 ラインナップ定義 — 単責務6枚

**分割原理**: 一枚 = 一責務(gate (i) のみ schema 建設と分類の二枚に
分ける)。gate 5項は語彙が互いに異質であり、合併は statement の膨張を
招く。単責務分割は反証時の影響を一枚に局所化する(statement の conjunct
数が cycle 数・改訂回数と相関する実測: G-106 = 5 cycle から
G-110 = 111 cycle まで)。

### G-111(仮 slug: `G-111-aat-indexed-base-change-schema`)

- 責務: gate (i) 前半 — global / indexed base-change schema の建設と
  (D) の full-domain 化。全 `ExtractionInstance` 上の base 作用、各固定
  carrier 内の全 package に対する cocartesian 保存 lift、実 BC 経路との
  制限比較。
- 素材: `no_universalBCDiagnosticSourceFiberIncidence`(現行 ordinary
  schema からの incidence 普遍生成の不在を確定した G-110 の schema no-go
  theorem)が、必要な indexed schema の形式要件を反面から特定している。
  F0 typing cycle の一次入力とする。
- 依存: G-110。

### G-112(仮 slug: `G-112-aat-exact-bottom-coverage`)

- 責務: gate (i) 後半 — realization 像の coverage theorem(第一段 = 有限
  carrier・有限 Source 上の同型までの coverage、第二段 = sector 全域)と
  全域作用・分類。G-110 (B) は左枝(carrier 大域の全域 lift)で確定した
  ため、分類の読みは「全域 lift の coverage と、像外入力の帰趨の決定」で
  ある。
- 依存: G-111(schema 基盤)。

### G-113(仮 slug: `G-113-aat-diagnostic-conservativity`)

- 責務: gate (v) — full-domain indexed action 上で
  `DiagnosticConservative` を構造的に生成する class の固定、target
  vanishing から source vanishing への反射、reselection orbit の検出、
  class 外で非零 obstruction が消える有限 witness、恒等・水平・垂直
  貼り合わせ閉性。生成診断部分圏上の `Full` + `Faithful` は十分条件候補
  として statement をこのカードで固定する。
- 素材: G-110 の旧 `H_bc` 系 declaration(履歴 artifact)。
- 依存: G-111。frontier 接続: (D) の `J_A` defect profile 枝(係数 base
  change カードとの接続点)。

### G-114(仮 slug: `G-114-aat-refinement-base-change`)

- 責務: gate (ii) — `RefinementDoctrineHom` の圏化と refinement base
  change。
- 依存: G-110(fiber product・regime)。

### G-115(仮 slug: `G-115-aat-upper-stage-lift`)

- 責務: gate (iii) — `GeomRead` / `ObProblem` への base-change lift と、
  Gr3 段横断輸送(G-109 pseudofunctor 塔)への接続 bridge。
- 依存: G-110+G-109。

### G-116(仮 slug: `G-116-aat-gr4-capstone`)

- 責務: gate (iv) — IsIso 水準 exchange-failure の存否決定(全同型定理
  または反例の二枝 disjunction 型。分岐固定の様式は G-110 (B) を前例と
  する)+**Gr4 達成記録 = SAKURA 満開の記録**(G-109 が Gr3 を記録した
  前例に従う)。
- 依存: 存否決定の設定は G-114 / G-115 の regime を含む(gate (iv) の
  定めどおり)。達成記録は G-111〜G-115 の全完遂に依存する。

依存グラフ:

```
G-110 ──→ G-111 ──→ G-112
               └──→ G-113
G-110 ──────→ G-114 ──┐
G-110 / G-109 → G-115 ─┴→ G-116(存否決定+達成記録)
```

## §4 隊列運用

- **起票**: draft 6枚を一括 batch PR で起票する(Gr3/Gr4 カード3枚
  draft の batch 起票と同型)。G-110 完遂済みで錨 head は固定済みであり、
  起票条件は満たされている。
- **昇格**: 一枚ずつ、G-111 から。昇格時は敵対レビュー往復を経る。依存
  カードの statement 改訂時は draft 差し戻し(G-109 の伝播規定と同型)。
- **昇格レビューの右サイズ化(提案 — G-111 昇格前に正式裁定)**: gate
  カードは reviewed G-110 / G-109 artifact への錨止めを主とし、新設
  schema の発明を statement に持ち込まない設計とする。この前提の下で
  レビュー上限を Claude 3レーン+Codex 2巡とし、型細部は F0 typing
  cycle へ移す。
- **後続接続**: SAKURA 満開は Atlas 補強論文(n1006)の着手条件を解く。

## §5 満開の定義 — Gr 系列の完了

SAKURA 満開 = Gr4 達成の記録であり、次の全条件で成立する。

1. G-111〜G-115 が各 gate 責務を `target-theorem-proved` で完遂して
   いる。gate の義務は移管でのみ動かし、削除しない(G-110 の移管規律の
   継続)。
2. G-116 が gate (iv) の存否をどちらかの枝で確定している。
3. G-116 が Gr4 達成を範囲併記付きで記録している(様式は G-109 の Gr3
   記録に従う。coverage の到達段(第一段 / 第二段)を明記する)。

満開の記録をもって Gr 階梯(Gr0–Gr4)は閉じ、SAKURA 海域は渡り切りと
なる。次の海域(係数 base change 方向、n1005 §5 の後続 draft 候補)の
命名は、その海域の開花の時に行う。
