---
name: website-review
description: Website / Manual 分野の敵対レビュー SKILL。website/ と docs/website を対象に、claim boundary・public scrub・static UX・cross-surface 同期を4観点の並列サブエージェントで反証的にレビューする。Use when the user says "$website-review", or when $review-pr / $issue-to-pr routes a diff touching website/ or docs/website to this skill.
---

# Website Review

公開 web surface の差分を敵対的にレビューする。分野の所有範囲は
`website/` に加え `docs/website/`。

## 敵対レビュー原則

これは**敵対レビュー**である。レビュワーの成果は反証の試行記録であり、
チェックリストの消化ではない。各観点は「この差分/主張を落とすとしたら
どこか」を先に立て、反証を試み、その試行と失敗を報告する。承認は反証の
失敗としてのみ与える。

反証の手がかりの正本は `.codex/skills/_shared/refutation-checklist.md`
(特に §5 帰属・名前だけ repackage、§6 横断機械 scan、§7 finding ゼロの
資格条件)。各観点はこれを読み、項目を複製せず参照する。

## 基本方針

- ユーザーへの報告は日本語で行う。
- 実装者の自己申告は監査対象であって証拠ではない。
- 既存の未コミット変更はユーザー変更として扱い、勝手に戻さない。
  破壊的操作をしない。ファイルを編集しない。
- Website は docs の複製ではなく、AAT / SFT / ArchSig を公開向けに読む
  web-native surface として機能する。

## 4観点(サブエージェント必須)

4観点を4つのサブエージェントに分けて**必ず**並列実行する。
起動できない場合は親が代替せず `Blocked / cannot determine` に落とす
(fail-closed)。

1. **public reading surface**
   - Website が docs の複製に退化していないか、主題が first viewport で
     明確か、docs source of truth と navigation / sitemap の対応が
     破綻していないかを疑う。

2. **claim boundary と public scrub**
   - AAT / SFT / ArchSig の claim boundary を越える product claim、
     proof claim、forecast claim を疑う。
   - private name、private path、内部作業名、未公開メモの混入を疑う
     (checklist §6 の privacy scan)。
   - ArchSig / FieldSig の境界が否定的 non-goal 羅列でなく肯定的責務として
     書かれているかを疑う。

3. **cross-surface 同期**(#3082 由来)
   - Lean status・台帳語彙・claims 集約の website 表示が、`docs/aat/` の
     台帳・guideline の現在の語彙と drift していないかを疑う。
   - theorem 数、status タグ、部構成など docs 由来の数値・ラベルの
     転記が現在の source of truth と一致するかを突合する。

4. **static UX と検証**
   - route、asset path、link、responsive layout、text overflow、
     accessibility の崩れを疑う。
   - local static preview、link / asset / title / layout checks、
     `sitemap.xml` / `robots.txt` の破綻を確認する。
   - mobile / desktop viewport の text overlap / clipping を疑う。

## Sub-Agent Prompt

```text
Use the website-review skill context. Review only the assigned perspective.
You are an adversarial reviewer: you are called to find grounds for rejecting
this diff, not to approve it. Read .codex/skills/_shared/refutation-checklist.md
and use it as refutation leads.
Perspective: <観点1〜4の名前>
Target: <files, diff range, or working tree scope>

Report in Japanese:
1. Findings, ordered by severity, with file/line references.
2. Refutation attempts: what you tried to refute and what evidence defeated
   each attempt (at least 3 entries when you report no findings).
3. Evidence checked.
4. Checks that should be run for this perspective.
5. Coverage limits.

Do not edit files. Do not treat the implementer's claim list as evidence.
Report any privacy leak regardless of your lane. The parent must not pass
expected findings to you.
```

## 検証

- local static preview(Eleventy: `cd website && npx @11ty/eleventy --serve`
  または `python3 -m http.server`)
- link / asset / title / layout checks(必要なら Playwright)
- checklist §6 の横断機械 scan
- 実行できない検証は理由と残リスクとして報告する。

## 親 Codex の統合判定

1. 判定: `Needs changes`, `No major findings`, `Blocked / cannot determine`
2. Findings: 重大度順。
3. 観点別まとめ: 4観点それぞれの結論と反証試行。
4. 実行した検証。
5. Coverage / residual risk。

4観点すべての報告が揃わない限り合格を出さない。finding ゼロの観点報告に
反証試行3件の記載がなければレビュー未実施として扱う。
