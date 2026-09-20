# Foundations of Algebraic Architecture Theory

*A Rising Sea of Geometry, Transport, Comparison, and Reconstruction*

Atom と Law から、相対的なアーキテクチャの幾何、局所整合性、診断、輸送、比較、
再構成を展開する長編の基礎論文を準備する。
初版は障害・診断比較と局所再構成までをまとめ、正規化・比較群との整合と有限決定性の
統合成果を改訂版へ追加する。収録範囲と数学内容は、以下の構成マスターと数学棚卸しに記す。

- [論文構成マスター](paper-structure.md): 主題、収録方針、章構成、各章の役割。
- [数学内容の棚卸し](mathematics-inventory.md): 第1〜8章の定義・構成・定理・反例、成立条件、CS 対応、章間の接続と一次資料。数学本文の全10部・付録の配置も整理する。
- [論文作成 ToDo](TODO.md): 日本語原稿17パートの執筆・レビュー、英訳・TeX化、投稿前確認。
- [AI 利用記録](ai-use.md): 構成・執筆・文献確認に用いた AI、その利用範囲。
- [主張と証拠の対応](claims.md): 原稿の主張と、確認した数学・形式化の固定版との対応。
- [論文作成ガイドライン](../../../docs/paper/guideline.md): 共通の執筆・検証・公開手順。

日本語原稿を `ja/` で執筆・レビューし、内容を確定してから英訳して公開する。
公開する英語版は、日本語原稿と同じ内容とする。
[準備と記法](ja/03-preliminaries-and-notation.md)、
[第1章 相対的アーキテクチャの構成](ja/04-relative-architecture.md)、
[文献](ja/14-references.md)の下書きを作成している。
執筆・照合・PR レビューの完了は ToDo で管理する。

[文献確認記録](references.csv)の hash は、Markdown 原稿の段階では、
`bib_sha256` に `ja/14-references.md` の SHA-256 を記録する。
`manuscript_sha256` は、`ja/03-preliminaries-and-notation.md`、
`ja/04-relative-architecture.md` の順にファイルのバイト列を連結したものの SHA-256 とする。
TeX 化の際には、[共通検査](../_tools/README.md)が算出する書誌・原稿一式の hash へ更新する。
