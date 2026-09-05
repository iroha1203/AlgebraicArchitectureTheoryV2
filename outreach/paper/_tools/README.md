# Paper tools

`paper.py` は `paper.json` のファイル一覧から静的検査、隔離ビルド、投稿用 source を作る。
Python 3.10 以上の標準ライブラリを使用する。品質基準と投稿可否は
[Paper guideline](../../../docs/paper/guideline.md) に従う。

## セットアップ

執筆用は Tectonic 0.16.9、投稿前確認用は TeX Live 2025 の `xelatex` または `pdflatex`
と `bibtex` を用意する。Tectonic はインストール後に一度通常ビルドし TeX 資源をキャッシュする。
共通 CLI は `--only-cached` で実行する。年次・処理系の版は各 `paper.json` で固定し、
合わない環境では停止する。TeX Live の資源状態は [arXiv 要件](../../../docs/paper/arxiv.md)
に合わせる。年次一致だけでは配布内の package 更新差まで固定できないため、環境取得元と
資源の版・digest を投稿記録に残し、arXiv preview でも最終確認する。
PDF テキスト検査は Poppler の `pdftotext`、目視用画像の生成は `pdftoppm` を使う。

## コマンド

repository root から実行する。各 `--out` は新しいディレクトリを指定する。
既存ファイルの削除・上書きを避けるため、出力先が存在すれば停止する。

```bash
python3 outreach/paper/_tools/paper.py check outreach/paper/saga/paper.json
python3 outreach/paper/_tools/paper.py build outreach/paper/saga/paper.json --out .tmp/paper-saga-tectonic
python3 outreach/paper/_tools/paper.py check outreach/paper/saga/paper.json --pdf .tmp/paper-saga-tectonic/build/main.pdf
python3 outreach/paper/_tools/paper.py build outreach/paper/saga/paper.json --engine xelatex --out .tmp/paper-saga-texlive
python3 outreach/paper/_tools/paper.py package outreach/paper/saga/paper.json --out .tmp/paper-saga-source
```

`build` は変換後 source、PDF、ログ、`build.json` を保存する。終了コード0は、処理が成功し、
未定義参照・文字欠落等を最終ログで検出しなかったことを示す。行幅警告は記録し目視確認する。
`package` は明示した source のみを ZIP に入れ、外側にファイル hash と ZIP hash を記録する。
ZIP は執筆用 source を投稿ルートから処理できる配置へ整える。投稿は人間が実施する。

## 検査範囲

`check` は列挙した UTF-8 TeX/BibTeX 等について、不可視文字・ローカル絶対パス・編集残存候補、
静的な `input/include/includegraphics/bibliography`、label、citation key の欠落・重複を検査する。
TeX マクロを展開する処理ではないため、動的な参照や独自の引用命令、`.bbl` のみの書誌は
対応するビルドと個別確認を必要とする。共通検査は `.bib` を持つ原稿を対象にする。
完成 PDF は `build.json` の source/PDF hash と照合する。外部で生成した PDF は同じ項目の
生成記録を `--build-record` で指定する。完成 PDF の抽出テキスト検査も、PDF 目視・原典確認・証明検証とは別の結果として扱う。

終了コード: 0=対象範囲の機械検査通過、1=検出またはビルド失敗、2=入力・環境エラー。
すべての機械レポートは `submission_ready: false` を返す。

文献記録の機械照合:

```bash
python3 outreach/paper/_tools/paper.py check outreach/paper/saga/paper.json --references outreach/paper/saga/references.csv
```

`references.csv` は [雛形](../../../docs/paper/templates/references.csv) から作る。
`check` の `bib_sha256` は書誌ファイル一覧とその hash の JSON に対する hash、
`source_sha256` は config と原稿一式の hash であり、CSV の `manuscript_sha256` に記録する。
全書誌・原稿の変更で確認対象の hash が変わる。内容を確認した担当者が影響範囲を評価し、
必要な再確認後に記録を更新する。機械照合は入力された記録の整合だけを確認する。

## 新しい論文

SAGA の `paper.json` を参考に、`files` に各入力と投稿先相対パスを明示する。
`main` は投稿ルートの TeX。`tex_replacements` はコピー内の参照パスを置換するので、
原稿本文と数式が不変であることを差分で確認する。symlink・ルート外・重複パスを拒否する。
論文資料全体の梱包は各論文の固有スクリプトに置く。

## ツールの検証

```bash
python3 -m unittest discover -s outreach/paper/_tools -p 'test_*.py'
```

## macOS の固定 TeX Live 環境

[TinyTeX の公式配布](https://github.com/rstudio/tinytex-releases/releases/tag/v2025.08) の
取得元と SHA-256 を [lock ファイル](texlive-macos.lock.json) に記録している。
システムの PATH を変更せずに、この checkout の作業領域へ展開できる。
資源更新を行った場合は、その変更を含む別の環境として記録する。
`build.json` は処理系バイナリと TeX Live package inventory の SHA-256 を記録する。

```bash
set -e
mkdir -p .tmp/paper-env
curl -fL https://github.com/rstudio/tinytex-releases/releases/download/v2025.08/TinyTeX-1-v2025.08.tgz -o .tmp/paper-env/TinyTeX-1-v2025.08.tgz
python3 - <<'PY'
import hashlib, json
from pathlib import Path
lock = json.loads(Path('outreach/paper/_tools/texlive-macos.lock.json').read_text())
archive = Path('.tmp/paper-env/TinyTeX-1-v2025.08.tgz')
if hashlib.sha256(archive.read_bytes()).hexdigest() != lock['sha256']:
    raise SystemExit('checksum mismatch; do not extract')
PY
# 上の checksum 確認が成功した場合だけ、新しい展開先で実行する。
tar -xzf .tmp/paper-env/TinyTeX-1-v2025.08.tgz -C .tmp/paper-env
PATH="$PWD/.tmp/paper-env/TinyTeX/bin/universal-darwin:$PATH" python3 outreach/paper/_tools/paper.py build outreach/paper/saga/paper.json --engine xelatex --out .tmp/paper-saga-texlive
```

この配布と arXiv サーバーの資源状態には更新日の差があるため、最後に arXiv preview を確認する。
