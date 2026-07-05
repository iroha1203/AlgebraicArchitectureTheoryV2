# website リニューアル W2 — statement-first + wayfinding 設計ノート

- 日付: 2026-07-05
- 対象: `website/`(Eleventy no-build static surface)
- 位置づけ: W1a / W1b(AAT 正典リライト)完了後のデザイン品質波。
  [website_renewal_design_note.md](website_renewal_design_note.md) の方針(AAT 正典 1:1、抑制された研究サイト)を維持したまま、
  「構造の可視化」と「道案内」だけを強化する。

## 問い

読者が理論ページを開いたとき、**章の数学的骨格(公理・定義・定理)と、塔の中の現在地**が、
スクロールとひと目で分かるか。

この問いに寄与しない装飾・改修は採らない。

## 決定事項

### 1. Statement-first(案1)

現状、数学的言明は `p.statement` + `a.statement-anchor`(例: `Definition I.1.1 (Atom).`)として
全サイト一貫マークアップ済み(AAT/SFT 合計 約440件)。しかし視覚上は通常段落と区別がなく、
Lean 連携のある theorem card だけが突出している。

- `p.statement` をセマンティックブロックに昇格する: 細い左罫 + 控えめな面 + 余白。
  **HTML は変更しない**(CSS のみ)。
- 種別は既存 id 接頭辞で判別する(CSS 属性セレクタ、新規クラス不要):
  - `theorem- / proposition- / lemma- / corollary-` → accent(teal)
  - `definition- / meaning-` → 無彩(rule-strong)
  - `axiom- / assumption- / principle- / condition-` → accent-warm
  - `example- / candidate- / position- / novelty- / status- / counterexample-` → 破線・muted
  - `statement-proof` → 引き込み(細罫・muted)
- theorem card(左罫 5px)と同じ視覚語彙に揃え、card は statement の「Lean 連携つき特殊形」として読めるようにする。
- `:target` の statement に一時ハイライト(anchor 遷移時の現在地明示)。

### 2. Wayfinding(案2)

- **series ナビ**: サイドバーに「In this series」パネルを新設。
  同一 `navSection` のページを front matter `order` 順に列挙し、現在ページをハイライト。
  Eleventy collections から自動生成(`_includes/series-nav.njk`)。ページ側は include 1 行の追加のみ。
  - 対象: aat / sft / archsig の記事ページ(セクション landing 自身と outreach は除外)。
  - SFT の入れ子(`sft/computation/interface/` など)は URL 深さでインデント。
  - デスクトップでは既定で開く(`data-sidebar-open="true"`)。モバイルは既存 drawer の折りたたみに従う。
- **TOC scrollspy**: 「On this page」のリンクに IntersectionObserver で現在節ハイライト
  (`site.js` に追加。既存の `.site-nav` scrollspy と同じ機構)。

### 3. やらないこと

- ヒーロー圧縮・summary ボックス(案3)、定理索引・用語ポップオーバー(案4)は本波に含めない。
- 配色・書体・レイアウトグリッドの変更はしない。派手さを足さない。
- 本文 HTML の statement マークアップ改変はしない(誤植リスクと差分ノイズを避ける)。

## 実装メモ

- 変更ファイル: `assets/css/theory.css` / `components.css`、`assets/site.js`、
  `_includes/series-nav.njk`(新規)、`eleventy.config.js`(series 用フィルタ)、
  各記事ページ(include 1 行 × 約38ページ)。
- 検証: ローカル Eleventy + スクリーンショット(light/dark、desktop/mobile)、`git diff --check`、hidden Unicode scan。
