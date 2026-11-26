# AAT 数学本文モノグラフ PDF 生成パイプライン

[代数幾何的アーキテクチャ論](../../docs/aat/algebraic_geometric_theory/README.md)（`docs/aat/algebraic_geometric_theory/`）の Markdown 群を唯一の編集元（Single Source of Truth）として保ち、ゼロ依存の Python 3.10+ スクリプトで決定的・一方向に LaTeX ソースを生成し、1 本のモノグラフ PDF を組版するツール群である。
査読前・公開論文を管理する `outreach/paper/`（[論文作成ガイドライン](../../docs/paper/guideline.md) の適用対象）とは分離し、`outreach/monograph/` に配置している。

- 数学本文（`docs/aat/algebraic_geometric_theory/`）は読み取り専用入力として扱い、このツールから変更しない。
- 生成される `.tex`・`.pdf`・ログ・メタデータはすべて `--out` で指定した作業ディレクトリ（既定運用では `.tmp/` 配下）へ隔離出力し、リポジトリへコミットしない。
- 定理番号・補題番号・式番号は LaTeX に自動採番させず、枝番（例：`命題11.5a`、`構成14.6b`、`式(16.22a)`、`定理22.2a`）を含め本文の固定番号をそのまま組版する。

## 構成ファイル

- `manifest.json`: 構成順（序論 → 共通記号 → 第I–VII部（第1–24章）→ 付録A–E）、除外ファイル（`README.md`）、`README.md` の部アンカー対応、TeX 処理系の固定版を定めるマニフェスト。
- `preamble.tex`: XeTeX / `xeCJK` 用の LaTeX プリアンブル（A4、IPAex TrueType フォント `ipaexm.ttf` / `ipaexg.ttf`、`amsmath`/`amssymb`/`mathrsfs`/`xltabular`/`hyperref`/`bookmark`、宣言・証明・QED・式幅調整マクロ）。
- `monograph.py`: 静的検査（`check`）、TeX 生成（`generate`）、PDF ビルドおよびログ／テキスト検証（`build`）を実行する CLI。
- `test_monograph.py`: 変換の忠実性・リンク解決・失敗ケース検出（未閉じ数式、不在リンク／アンカー、未登録ファイル、上書き拒否、TeX ログエラー、PDF ハッシュ不一致）の `unittest` 回帰テスト。

## TeX 処理系の選定と環境固定

既存の論文ビルド基盤（`outreach/paper/_tools/paper.py` および `outreach/paper/_tools/texlive-macos.lock.json`）との統一と OS 非依存の再現性、および PDF.js（IDE 内蔵ビューア・ブラウザ）・macOS プレビュー等の幅広いビューア互換性を優先し、**XeTeX 系（`xeCJK` + 同梱 TrueType 和文フォント `ipaexm.ttf` / `ipaexg.ttf`、`CID TrueType` + `ToUnicode` 埋め込み）**を採用する。これにより、以下の両処理系で同一の LaTeX ソースをビルドできる。

1. **Tectonic 0.16.9（既定 `--engine tectonic`）**:
   - 初回のみ `--allow-network` を付けて TeX 資源をローカルキャッシュへ取得する。
   - 2回目以降は `--only-cached`（既定）でオフライン再現ビルドを行う。
2. **TeX Live 2025 `xelatex`（`--engine xelatex`）**:
   - macOS では [texlive-macos.lock.json](../paper/_tools/texlive-macos.lock.json) で SHA-256 固定された TinyTeX-1 v2025.08 を [paper tools README](../paper/_tools/README.md#macos-の固定-tex-live-環境) の手順で `.tmp/paper-env/` へ展開し、`PATH` を通して実行する。
   - `xeCJK` や `ipaex` が未導入の場合は、その展開済み環境に対する差分を記録したうえで導入する。

PDF テキスト検証には Poppler の `pdftotext`、代表ページの目視確認画像出力には `pdftoppm` を使用する。

## 実行コマンド

リポジトリルートから実行する。`--out` には未作成の新しいディレクトリを指定する（既存ディレクトリがある場合は上書き防止のため終了コード 2 で停止する）。

```bash
# 1. Markdown 構文・リンク・アンカー・未登録ファイル・衛生検査（TeX ビルドなし）
python3 outreach/monograph/monograph.py check

# 2. LaTeX ソースのみ隔離出力
python3 outreach/monograph/monograph.py generate --out .tmp/aat-monograph-tex

# 3. Tectonic で PDF ビルド（初回キャッシュ取得時は --allow-network を付与）
python3 outreach/monograph/monograph.py build --allow-network --out .tmp/aat-monograph-pdf

# 4. キャッシュ済み環境でのオフライン再現ビルド（既定: --only-cached）
python3 outreach/monograph/monograph.py build --out .tmp/aat-monograph-pdf-cached

# 5. 生成済み PDF と build.json のハッシュ・抽出テキスト照合
python3 outreach/monograph/monograph.py check \
  --pdf .tmp/aat-monograph-pdf-cached/build/aat_monograph.pdf

# 6. TeX Live 2025 xelatex でのビルド
python3 outreach/monograph/monograph.py build --engine xelatex --out .tmp/aat-monograph-xelatex
```

### 出力物（`--out` 配下）

- `source/`: 生成された `aat_monograph.tex`、`preamble.tex`、`chapters/*.tex`
- `build/aat_monograph.pdf`: 組版されたモノグラフ PDF
- `build/aat_monograph.log`: 最終パスの TeX ログ
- `process.log`: 処理系の標準出力・標準エラー出力
- `build.json`: 入力・生成物・PDF・処理系の SHA-256、変換統計、ログ検査結果（エラー・未定義参照・文字欠落・Overfull/Underfull）

## 目視確認と回帰テスト

代表ページの目視確認用 PNG は `.tmp/` 配下へレンダリングする。

```bash
# ページ数・目次・主要キーワードのテキスト確認
pdfinfo .tmp/aat-monograph-pdf-cached/build/aat_monograph.pdf
pdftotext .tmp/aat-monograph-pdf-cached/build/aat_monograph.pdf .tmp/aat-monograph-pdf-cached/extracted.txt

# 代表ページを PNG 化（例: 表紙・目次・記号表・定理・付録）
mkdir -p .tmp/aat-monograph-pages
pdftoppm -png -r 150 -f 1 -l 5 \
  .tmp/aat-monograph-pdf-cached/build/aat_monograph.pdf \
  .tmp/aat-monograph-pages/front
```

単体テスト・回帰テストの実行：

```bash
python3 -m unittest discover -s outreach/monograph -p 'test_*.py' -v
```

## 検査範囲と終了コード

- 終了コード `0`: 変換・静的検査・TeX ビルド・ログ検査（エラー 0 / 未定義参照 0 / 未定義制御列 0 / 文字欠落 0 / 重複ラベル 0）・PDF テキスト検査がすべて通過。
- 終了コード `1`: 変換エラー（未閉じの ``$`...`$`` や ```` ```math ````、存在しない相対リンク／アンカー、マニフェスト未登録ファイル、不可視 Unicode、ローカル絶対パス）または TeX ビルド・ログ検査・PDF 照合で問題を検出。
- 終了コード `2`: 引数・設定スキーマ・出力先既存・処理系不在／版不一致などの入力・環境エラー。

## 保守

`docs/aat/algebraic_geometric_theory/` に新しい章や付録（例：付録 F）を追加した場合、`monograph.py` は未登録ファイル検出で非ゼロ終了する。`manifest.json` の `structure` に正しい配置順で追記すること。
