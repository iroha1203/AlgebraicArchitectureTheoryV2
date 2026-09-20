# AI 利用記録

共通基準は [論文作成ガイドライン](../../../docs/paper/guideline.md)に従う。

| ツール・モデル・利用時期 | 用途 | 対象範囲 | 検証方法・確認者 |
| --- | --- | --- | --- |
| Codex（GPT-6）、2026-09-19 | 人間との対話に基づく論文構成の初版作成、CS 対応詳細の棚卸し文書への移管 | `paper-structure.md`、`mathematics-inventory.md` とディレクトリの案内 | Codex が n1012・n1015、AAT 数学本文の構成、関連 GOAL、論文作成ガイドラインと照合。CS 対応は G-123・G-124 の report と lens・protocol・変更分類・有限決定の Lean 宣言にも照合。移管前後の数学内容、相対リンク・表記・差分を検査 |
| Codex（GPT-6）、2026-09-19 | 数学棚卸しを第1〜8章全体へ拡張し、成立条件・反例・章間の接続を整理 | `mathematics-inventory.md`、`README.md` | Codex が構成マスター、固定版の数学本文全10部・付録、G-101〜G-124 の関連固定命題・report、対応する主要 Lean 宣言と入力条件を照合。G-105・G-117 の反証と G-123・G-124 の個別成果・共通再構成の接続項目を区別。参照先・章別収録・表・数式区切り・Unicode・公開情報・差分を検査。既存証明の全行再査読と Lean 再検証は実施していない |
| Claude Code、2026-09-19 | 構成・数学棚卸しの独立レビュー | `paper-structure.md`、`mathematics-inventory.md` を中心とする PR #4784 | commit `2f26ff2f5` に対する[レビュー記録](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/4784#issuecomment-5739468612)に、一次資料との照合方法、修正要求1〜5、推奨事項を記載 |
| Codex（GPT-6）、2026-09-19 | Claude の修正要求1〜5への対応 | `mathematics-inventory.md`、本利用記録 | Codex が引用先の実宣言、G-119 B・D、数学本文VIを照合し、引用修正、比較群の2項目追加、特異性の配置明示を実施。相対リンク・表・Unicode・公開情報・差分を検査。この変更では推奨事項を対象に含めなかった |
| ChatGPT（モデルの記載なし）、2026-09-19 | 修正後の正確性と推奨事項の採否についての追加レビュー | commit `9b305cbfc` の構成・数学棚卸し | [PR の追加レビュー](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/4784#issuecomment-5739679573)に、主要箇所の一次資料照合、収録・配置・引用・表現の提案と検証範囲を記載 |
| Codex（GPT-6）、2026-09-19 | 人間が承認した推奨事項の採否を反映 | `mathematics-inventory.md`、`paper-structure.md`、本利用記録 | 固定版の数学本文IV・V・VII・VIIIと対応する Lean 宣言を照合し、正例・短い結果・補足・展望の配置、仮定、直接参照を補完。相対リンク・章別収録・表・数式区切り・Unicode・公開情報・差分を検査。既存証明の全行再査読と Lean 再検証は実施していない |
| Codex（GPT-6）、2026-09-19 | 人間が指定した執筆順序に基づく ToDo の作成と文体確認項目の追加 | `TODO.md`、`README.md`、本利用記録 | 構成マスターの全17パートとファイル案を照合し、日本語原文の完成・レビュー後に英訳・TeX化する手順を確認。文献・証拠対応、日英の整合、PDF 確認、投稿準備を論文作成ガイドラインと照合。人間の指示と照合し、先回り防衛記述・メタ記述がないことの確認を追加。相対リンク・Unicode・公開情報・差分を検査 |
| Codex（GPT-6）、2026-09-19 | 人間が承認した構成補強案の反映 | `paper-structure.md`、本利用記録 | 四部八章・全17パートを保持し、章間の接続節、AAT の入力から述べる主要定理、第6〜8章の到達点を数学棚卸しの対応項目と照合。係数・障害類の比較、可逆比較と生成比較、正規化と section の整合の成立条件を確認。相対リンク・表・Unicode・公開情報・差分を検査 |
| Claude・ChatGPT（モデルの記載なし）、2026-09-19 | 構成補強の独立レビュー | commit `6bae59f22` の構成マスターと本利用記録 | [Claude レビュー](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/4788#issuecomment-5740144972)と[ChatGPT レビュー](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/4788#issuecomment-5740157163)に照合方法と範囲を記録。両者が承認相当とし、第7章の同定先の限定を提案。Claude は節名の表記統一も提案 |
| Codex（GPT-6）、2026-09-19 | 人間が採用したレビュー指摘2件への対応 | `paper-structure.md`、本利用記録 | 棚卸し7-Hと `QualifiedComparisonGroup.lean` の部分群・群同型の実宣言に照合し、同定先の両端の射が底で恒等射となる条件を明記。本文と図の節名を統一。相対リンク・表・Unicode・公開情報・差分を検査 |
| Codex（GPT-6）、2026-09-19 | 人間が指定した第2章から第3章への接続の Lean 実装要件を ToDo に追加 | `TODO.md`、本利用記録 | 構成マスター第3章と数学棚卸し第3章の接続項目に照合し、係数・被覆・nerve からの cochain 比較、微分との可換性、指定障害類の対応、零性の保存・反映を実装・証明する項目を追加。相対リンク・表・Unicode・公開情報・差分を検査 |
| Codex（GPT-6）、2026-09-20 | 人間が指定した初版・改訂版の収録方針と G-125 の数学内容を反映し、進行状況を記載しない方針へ修正 | `paper-structure.md`、`mathematics-inventory.md`、案内・ToDo・本利用記録 | commit `c245b49b0825f653307f396f4dc9f76e1ecad44a` の G-125 実装について、共通 Atom 入力、実 Čech・係数比較、既存障害の生成経路、整数補正による零性反映、reading 平方・類の輸送、条件 C、零・非零例の定義・定理・証明を照合。G-124 A・B を初版、C–E を改訂版の内容へ対応づけた。研究の進行状況と完了待ちの記述を削除し、数学内容・配置・一次資料の対応を記した。相対リンク・表・数式区切り・Unicode・公開情報・差分を検査。この作業では Lean 再検証と GOAL の完了再判定を実施しなかった。Claude Code の独立レビュー呼び出しは認証エラーで終了した |
| Claude・ChatGPT（モデルの記載なし）、2026-09-20 | 収録方針と数学棚卸しの独立レビュー | commit `451234cb6` の変更5文書 | [Claude レビュー](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/4827#issuecomment-5748215209)と[ChatGPT レビュー](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/4827#pullrequestreview-5259830728)に、固定版の実装・G-124 の仕様との照合方法と範囲を記録。双方が承認相当とし、Claude は未使用の参照定義3件の削除と改訂版での定義の共通適用の明確化を提案 |
| Codex（GPT-6）、2026-09-20 | Claude の軽微な提案2件を反映 | `mathematics-inventory.md`、本利用記録 | 未使用の参照定義3件を使用箇所がないことを確認して削除。§8.3 の定義を §8.5 の D で共通に適用する収録分担を明記。参照先・表・数式区切り・Unicode・公開情報・差分を検査。Lean の再実行は行っていない |

利用範囲は論文の企画・構成と既存数学の棚卸しである。原稿作成、証明、文献調査、図表作成などに
利用した場合は、実際の対象と検証方法を追記する。論文の開示文は、原稿の利用記録と
投稿先要件が揃った段階で作成する。
