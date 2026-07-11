---
name: website-review
description: website/ と docs/website の差分を4観点で敵対レビューし、編集せず合否を返す。"$website-review"、website差分のレビュー、公開前のweb品質監査で使う。websiteの実装・修正依頼には使わない。
---

# Website Review

公開 web surface の差分を敵対的にレビューする。分野の所有範囲は
`website/` に加え `docs/website/`。

## 必須契約

`.codex/skills/_shared/review-protocol.md` と
`.codex/skills/_shared/refutation-checklist.md` を全文読み、
非編集・独立査読・fail-closed・報告形式をそのまま適用する。

## 基本方針

- Website は docs の複製ではなく、AAT / SFT / ArchSig を公開向けに読む
  web-native surface として機能する。

## 4観点(サブエージェント必須)

4観点を4つの独立したsubagentに分け、共有契約どおり利用可能枠まで並行する。

1. **public reading surface**
   - Website が docs の複製に退化していないか、主題が first viewport で
     明確か、docs source of truth と navigation / sitemap の対応が
     破綻していないかを疑う。

2. **claim scope と public scrub**
   - AAT / SFT / ArchSig の claim scope を越える product claim、
     proof claim、forecast claim を疑う。
   - private name、private path、内部作業名、未公開メモの混入を疑う
     (checklist §6 の privacy scan)。
   - ArchSig / FieldSig の責務が否定的 non-goal 羅列でなく肯定的責務として
     書かれているかを疑う。

3. **cross-surface 同期**(#3082 由来)
   - Lean status・台帳語彙・claims 集約の website 表示が、`docs/aat/` の
     台帳・guideline の現在の語彙と drift していないかを疑う。
   - theorem 数、status タグ、部構成など docs 由来の数値・ラベルの
     転記が現在の source of truth と一致するかを突合する。

4. **static UX と検証**
   - route、asset path、link、responsive layout、text overflow、
     accessibility の崩れを疑う。
   - first viewport で次 section の hint が見えるか、カードの入れ子や
     過剰装飾がないかを疑う。manual / command reference は scanning、
     comparison、repeated use に向いた密度かを疑う。
   - local static preview、link / asset / title / layout checks、
     `sitemap.xml` / `robots.txt` の破綻を確認する。
   - mobile / desktop viewport の text overlap / clipping を疑う。

## 検証

- local static preview(Eleventy: `cd website && npx @11ty/eleventy --serve`
  または `python3 -m http.server`)
- link / asset / title / layout checks(必要なら Playwright)
- checklist §6 の横断機械 scan
- 実行できない検証は理由と残リスクとして報告する。

## 親 Codex の統合判定

共有契約の統合出力に従い、判定を
`Needs changes` / `No major findings` / `Blocked / cannot determine` で返す。
