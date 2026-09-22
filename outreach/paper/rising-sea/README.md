# Foundations of Algebraic Architecture Theory

*A Rising Sea of Geometry, Transport, Comparison, and Reconstruction*

Atom と Law から、相対的なアーキテクチャの幾何、局所整合性、診断、輸送、比較、
再構成を展開する長編の基礎論文を準備する。
初版は障害・診断比較と局所再構成までをまとめ、正規化・比較群との整合と有限決定性の
統合成果を改訂版へ追加する。収録範囲と数学内容は、以下の構成マスターと数学棚卸しに記す。

- [論文構成マスター](paper-structure.md): 主題、収録方針、章構成、各章の役割。
- [数学内容の棚卸し](mathematics-inventory.md): 第1〜8章の定義・構成・定理・反例、成立条件、CS 対応、章間の接続と一次資料。数学本文の全10部・付録の配置も整理する。
- [Related Work 収録案](related-work-plan.md): 第1〜8章に対応する主要文献と補足候補、比較する結果、原典の参照箇所と本文との対応。
- [論文作成 ToDo](TODO.md): 日本語原稿の確定、英訳・TeX化、投稿・公開、改訂版の作業項目。
- [AI 利用記録](ai-use.md): 構成・執筆・文献確認に用いた AI、その利用範囲。
- [主張と証拠の対応](claims.md): 原稿の主張と、数学・形式化の固定版との対応。
- [Lean対応の全件照合記録](lean-correspondence-audit.md): 第1〜8章の314項目と番号外の主張について、対応宣言・適用条件・未確認箇所を記録する。
- [ResearchLean実行検証記録](researchlean-execution-report.md): 検証時の付録Aに記載されたResearchLean宣言の実行成否と再現手順を記録する。
- [論文作成ガイドライン](../../../docs/paper/guideline.md): 共通の執筆・検証・公開手順。

日本語原稿を `ja/` で執筆・レビューし、内容を確定してから英訳して公開する。
公開する英語版は、日本語原稿と同じ内容とする。
日本語原稿の各パートは、
[要旨](ja/01-abstract.md)、
[序論](ja/02-introduction.md)、
[準備と記法](ja/03-preliminaries-and-notation.md)、
[第1章 相対的アーキテクチャの構成](ja/04-relative-architecture.md)、
[第2章 Lawの幾何と局所整合性](ja/05-law-geometry.md)、
[第3章 標準解像度と診断不変性](ja/06-resolution-invariance.md)、
[第4章 輸送と合成の整合性](ja/07-transport-coherence.md)、
[第5章 基底変換と生成比較](ja/08-base-change.md)、
[第6章 冪等正規化と実現](ja/09-idempotent-normalization.md)、
[第7章 比較を保つ変更と情報](ja/10-comparison-and-information.md)、
[第8章 表示と局所再構成](ja/11-local-reconstruction.md)、
[Related Work](ja/12-related-work.md)、
[結論と今後の方向](ja/13-conclusions-and-further-directions.md)、
[文献](ja/14-references.md)、
[付録A Lean形式化との対応](ja/15-appendix-a-lean-correspondence.md)、
[付録B リポジトリとLeanのビルド](ja/16-appendix-b-verification-and-reproduction.md)に配置する。
執筆・照合・PR レビューの完了は ToDo で管理する。

[文献確認記録](references.csv)の hash は、Markdown 原稿の段階では、
`bib_sha256` に `ja/14-references.md` の SHA-256 を記録する。
`manuscript_sha256` は、`ja/01-abstract.md`、`ja/02-introduction.md`、
`ja/03-preliminaries-and-notation.md`、
`ja/04-relative-architecture.md`、`ja/05-law-geometry.md`、
`ja/06-resolution-invariance.md`、`ja/07-transport-coherence.md`、
`ja/08-base-change.md`、`ja/09-idempotent-normalization.md`、
`ja/10-comparison-and-information.md`、`ja/11-local-reconstruction.md`、
`ja/12-related-work.md`、`ja/13-conclusions-and-further-directions.md`
の順にファイルのバイト列を連結したものの SHA-256 とする。
図の編集元は `figures/` の SVG とし、その hash は `claims.md` に記録する。
TeX 化の際には、[共通検査](../_tools/README.md)が算出する書誌・原稿一式の hash へ更新する。
