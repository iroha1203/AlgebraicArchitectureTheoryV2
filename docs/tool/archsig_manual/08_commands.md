# 8. コマンド

```text
archsig <コマンド> [引数]
```

コマンドは、リポジトリの根で実行する。結果は JSON で標準出力に返し、終了コードは 0 である。
Law の誤り、沈黙、成り立たない結論も、結果として返す。
入力のファイルが読めないなど、結果を作れないときは、理由を標準エラーに書き、0 以外の終了コードを返す。

## 観測と Law

| コマンド | すること |
| --- | --- |
| `archsig status` | 古い範囲と、読んでいない範囲を返す。 |
| `archsig record <Atom のファイル>…` | 取り出した Atom を ArchMap に書く。`--drop <ソース>` で消えたソースを外す。 |
| `archsig law check` | Law ファイルが正しく書けているかを確かめる。 |

## 問い

| コマンド | 問い(第5章) |
| --- | --- |
| `archsig check` | 1. Law を守っているか、2. 全体で貼り合うか |
| `archsig plan check <候補>` | 3. 変更の後も保たれるか |
| `archsig compare --plan <候補>`、`--base <コミット>` | 3. 実装の後も保たれ、候補どおりか |
| `archsig paths <経路> <経路>` | 4. 経路や順序で結果が変わるか |
| `archsig check --reading <読み> --against <読み>` | 5. 粒度を変えても診断は変わらないか |
| `archsig view --reading <読み>` | 5. 粗い読みでまとめた構造 |
| `archsig plan choices <候補>` | 6. 条件を満たす変更は何通りあるか |
| `archsig plan split <候補>` | 7. 仕事をどう分けるか |
| `archsig plan glue <候補> <候補> … --as <名前>` | 7. 局所の候補をどう組み立てるか |
| `archsig next` | 8. 次にどこを読むか |

## 結果

| コマンド | すること |
| --- | --- |
| `archsig show <結果>` | 一つの結果の詳細を返す。 |
| `archsig diff <実行> <実行>` | 二つの実行で、新しく成り立たなくなった結果と、成り立つようになった結果を返す。 |
| `archsig verify <実行>` | 実行の検算データを確かめる。 |
