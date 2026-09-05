# arXiv 投稿要件

確認日: 2026-09-05。投稿直前に下記の原典を開き、変更と確認日を投稿記録へ残す。
本書は投稿先の要件を整理する。repo の品質基準は [guideline](guideline.md) にある。

## 公式要件

| 項目 | 確認した要件 | 原典 |
| --- | --- | --- |
| AI | 重要な生成 AI 利用を分野の慣行に従って開示し、各著者が生成方法を問わず全内容に責任を負う。AI を著者にしない | [Moderation: AI](https://info.arxiv.org/help/moderation/index.html#policy-for-authors-use-of-generative-ai-language-tools) |
| 処分 | 投稿権限の一定期間停止、アカウント停止、投稿の撤回等を認める。確認した本文は AI の停止期間を一律1年とは定めていない | [Enforcement](https://info.arxiv.org/help/policies/code_of_conduct_enforcement.html) |
| 完成度 | 研究論文は完成した最終草稿を投稿する | [Content types](https://info.arxiv.org/help/policies/content-types.html) |
| CS 総説・position paper | 査読を経た雑誌・会議での採択と査読完了の証拠が必要。journal reference と DOI を記載。workshop の査読は一般に十分とされない | [2025-10-31 公式告知](https://blog.arxiv.org/2025/10/31/attention-authors-updated-practice-for-review-articles-and-position-papers-in-arxiv-cs-category/) |
| 英語 | 全文の英語版が必要。多言語併記では英語版を先に置く | [Languages](https://info.arxiv.org/help/faq/multilang.html) |
| 投稿資格 | 初回・新カテゴリで endorsement が必要。個人推薦の経路もある | [Endorsement](https://info.arxiv.org/help/endorsement.html) |
| license・著者 | 投稿権限、共著者の同意、配布権と投稿先との両立を確認する | [Submission agreement](https://info.arxiv.org/help/policies/submission_agreement.html) |
| 組版環境 | TeX Live 2025 が既定、2023 も選択可。2025 の資源状態は2025-08-03 | [TeX Live](https://info.arxiv.org/help/faq/texlive.html) |
| source | 必要な TeX・図・書誌を同梱し不要ファイルを除く。処理は投稿ディレクトリのルートから行う。生成 PDF の確認が必須 | [TeX submission](https://info.arxiv.org/help/submit_tex.html) |
| 書誌処理 | `.bib` の処理をサポート。`.bbl` を含める場合は主 TeX と同じ basename とし、backend・形式を適合させる | [Bibliography](https://info.arxiv.org/help/submit_tex.html#include-bib-or-bbl-files-if-you-use-bibtexbiber) |
| metadata | 要旨は1,920文字以内。独自マクロを展開し、著者・題名・要旨等を投稿画面で確認する | [Metadata](https://info.arxiv.org/help/prep.html) |

## AI 出力に対する停止の運用説明

2026-07-23 の CERN Courier による arXiv 科学ディレクターへの取材は、架空文献や
実験の実数値を入れる指示の残存など、未確認の AI 生成を示す明白な証拠に対する
1年間の停止を説明している。期間後は復帰申請が必要で、査読済み論文を求める場合がある。
これは公式規約の執行についての取材であり、一般的な誤植への一律処分と解釈しない。
原典: [arXiv’s one-strike rule on AI](https://cerncourier.com/arxivs-one-strike-rule-on-ai/)。

## 投稿時の記録

各投稿の `submission.md` に、上記ページの再確認日、適用する種別とカテゴリ、
利用処理系、preview の確認結果を記録する。規則変更があれば本表を更新する。
