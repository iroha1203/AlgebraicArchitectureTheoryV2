# 投稿・公開記録

共通基準: docs/paper/guideline.md。arXiv 要件: docs/paper/arxiv.md。
空欄は未確認として扱う。

- 状態: published
- 投稿先・種別・カテゴリ・資格: Zenodo / Publication–Preprint。資格=権利を持つ登録ユーザーなら誰でも deposit 可。license は CC BY 4.0 で確定(2026-09-23、record 全体に適用)。
- 公式要件の確認日・URL・変更点: 2026-09-23、https://about.zenodo.org/policies/ 。全分野・全形式可、1 record 50GB 上限、公開ファイルは license 指定必須。SAGA 投稿時(2026-07)から実質変更なし。
- 原稿 commit / 未コミット差分の有無 / source manifest hash: `dabe696fd`(main)。paper.json 対象の原稿一式に未コミット差分なし(変更は記録文書のみ)。source_sha256 `1890535153c57aefd6a84e6c4e98d00191e88438be5b6df9ad4e8f8d4257c9a7`
- 処理系の版・TeX 資源・OS / ビルド手順・記録: 2026-09-23、macOS 26.5.2 arm64。執筆用=Tectonic 0.16.9(PDF `b178d162…`)。投稿前確認用=TeX Live 2025 xelatex+bibtex(TinyTeX-1 v2025.08、lock の SHA-256 一致を確認して展開。mathtools・pgf・urlbst 等を凍結スナップショット texlive.info/tlnet-archive/2025/08/31 から追加。xelatex executable_sha256 `af0a1824…`)。両ビルドとも exit 0・未解決参照 0・overfull 0・underfull 0・285ページ。build.json は `.tmp/paper-rs-tectonic-0923/`・`.tmp/paper-rs-texlive-0923/` に記録
- 投稿用 ZIP / PDF / metadata の hash: source.zip(22 files)SHA-256 `12acdee48775d3712c46650ed98e767395877e53b7e812d2d2c0ca607829b411`、展開先で xelatex+bibtex 再ビルド=285ページ・引用/参照警告 0。投稿前確認版 PDF(TeX Live)SHA-256 `6aeaafe0208f84bb60bbcfb2f0578ed54616b23c11933bb14d848e0069bbba8a`。metadata は zenodo_metadata.md(DOI・公開日は TBD)。DOI の title page 印字はしない(2026-09-23 著者裁定)ため、この zip と PDF が投稿する最終成果物である
- 文献全件確認の対象・結果・確認者: 全24 key を Codex(GPT-6)が原典と照合(2026-09-21〜22、references.csv)。その後の原稿変更(PR #4918・#4920・#4922)の影響範囲を Claude(Fable 5)が評価(2026-09-23): \cite の集合と references.bib は照合時から不変、ja/14 の差分はURL表記・句点のみ、CSV が参照する本文アンカー(P.2–P.4、1.5–1.6、1.9、1.32、2.2、2.5、2.9–2.10、3.4、3.11、4.1、4.4、5.2、8.6、8.12、序論 Rising Sea 段落)の番号・内容の保持を機械照合で確認。references.csv の hash 列は README の規約に従い共通検査の hash へ更新。
- 主要主張・数値・図表の証拠対応: claims.md の結合原稿 SHA-256 `a1059a18…` が現行 ja 原稿と一致することを再計算で確認(2026-09-23)。主張と Lean 固定版の対応は claims.md・付録A、全件照合は lean-correspondence-audit.md。
- 独立レビューの対象 hash・担当・結果・指摘解消: 原稿全体レビュー=Issue #4855(修正 PR #4856 approve)。直近変更=PR #4918(C型復元)・#4920(要旨1ページ化)・#4922(序論可読性)を Claude がレビューし、修正要求→解消確認→approve。全て人間がマージ済み(HEAD dabe696fd)。
- 読者向けレビューの対象 hash・担当・本文の理解を妨げた箇所と修正後の確認: 1〜8章通読チェック(Issue #4844、章間ドリフト指摘→改訂反映)、日本語FIXゲート3回通読(Issue #4896)、序論可読性 PR #4922 で読者導線を改善し解消確認。
- 論文の語彙確認(原稿・完成 PDF)の対象・担当・内部用語の修正と残す識別子の配置理由: 日本語FIXゲートで通読確認済み。英訳時に用語対応表(en/README.md)を作成し Lean 宣言名・SAGA 英語版と照合。Lean 宣言名は付録A の対応表としてそのまま残す(照合可能性のため)。
- 自動検査結果 / 残った検出候補の箇所・確認理由: `paper.py check` findings 0(2026-09-23、source_sha256 `1890535153c57aefd6a84e6c4e98d00191e88438be5b6df9ad4e8f8d4257c9a7`)。`check --references` findings 0(hash 更新後、2026-09-23)。`check --pdf` findings 0(Tectonic・TeX Live 両 PDF)。
- 完成 PDF 全ページ目視の対象 hash・担当・結果: 対象 `6aeaafe0…`(TeX Live 版)。Claude(Fable 5)が全285ページを目視(2026-09-23、6ページ/枚の contact sheet 48枚)。組版崩れ・文字欠落・図表/書誌の異常なし。人間の著者による最終目視は未実施
- 日英内容・定理番号・数値・引用の対応: 英訳・TeX化(Issue #4899、PR #4900・#4902・#4905・#4908)で全17パートの機械照合 0 error。以後の変更 PR #4918・#4920・#4922 も日英同時修正+照合で維持(各 PR・ai-use.md に記録)。
- AI 開示の照合: 付録C(en/17)と ai-use.md を突合(2026-09-23)。役割分担(Codex=Lean・証明、Claude=設計・原稿、複数AIの独立レビュー)・記録の所在の記載が実利用と一致。
- 著者・所属・題名・要旨・版・識別子・license の照合: 公開 record と zenodo_metadata.md を突合(2026-09-23、Claude)。題名・著者(Nakahata, Hiroyuki、ORCID 0009-0008-5928-0234)・Preprint・v1.0.0・英語・CC BY 4.0・description 4段落が一致。keywords は deposit 時に3語(software architecture / algebraic geometry / algebraic architecture theory)へ絞られた。related identifiers は未設定。
- 人間の著者による最終確認・日付: 2026-09-23(著者が最終版を確認して deposit・publish を実施)
- 投稿先生成 preview の hash・確認者・結果: publish 前 preview の独立記録はなし。代替として公開 record 上で file 一覧(2点)と checksum を突合し一致(2026-09-23、Claude)
- 実際の投稿日時・識別子: 2026-09-23、Zenodo record 22913489
- 公開 URL・DOI / arXiv ID・版: https://zenodo.org/records/22913489 、version DOI `10.5281/zenodo.22913489`、concept DOI `10.5281/zenodo.22913488`、v1.0.0。arXiv は未投稿(改訂版で判断)
- 公開後に取得した source・PDF の hash・照合結果: 公開 record からダウンロードした main.pdf の SHA-256 `6aeaafe0208f84bb60bbcfb2f0578ed54616b23c11933bb14d848e0069bbba8a`、source.zip の SHA-256 `12acdee48775d3712c46650ed98e767395877e53b7e812d2d2c0ca607829b411` が投稿前確認の記録と一致。record の MD5(25a03522… / 24be6fb3…)もローカル成果物と一致(2026-09-23、Claude)
