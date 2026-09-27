# 8. コマンド

ArchSig のコマンドの一覧である。呼び出すのは SKILL に従うエージェントで、人が直接打つことは前提にしない。

```text
archsig <コマンド> [引数] [オプション]
```

ArchSig は、カレントディレクトリから上へたどって見つけた `.archsig/` を使う。

## どのコマンドにも付けられるオプション

- `--format json|text|github`:表示の形。何も指定しなければ `json`。
- `--detail`:すべての結果の詳細を書き出す。
- `--require-decided`:沈黙も成り立たない結果として数える。

終了コードは第6章のとおり、`0` 成り立たない結果なし、`1` あり、`2` 入力を受け付けない、`3` 内部エラーである。

## 準備と状態

| コマンド | すること |
| --- | --- |
| `archsig init` | `.archsig/` と、その下の `law/`、`map/`、`plans/`、`runs/` を作る。 |
| `archsig status` | 古い範囲、読んでいない範囲、古くなった結果、前回から変わった Law を返す。 |
| `archsig validate` | ArchMap と候補を、形と Law の語彙に照らして検査する。 |
| `archsig schema atom\|law\|result` | Atom、Law、結果の形を、エージェントが読める形で返す。 |

## Law

| コマンド | すること |
| --- | --- |
| `archsig law check` | Law ファイルが正しく書けているかを確かめる。 |
| `archsig law diff <コミット>` | 定義を展開した後の Law で、そのコミットから何が変わったかを示す。 |

## 問い

| コマンド | 問い(第5章) |
| --- | --- |
| `archsig check [--law <名前>]` | 1. Law を守っているか、2. 全体で貼り合うか |
| `archsig check --reading <読み> --against <読み>` | 5. 粒度を変えても診断は変わらないか |
| `archsig plan check <候補>` | 3. 変更の後も保たれるか |
| `archsig compare --plan <候補> [--only <局所>]` | 3. 実装が候補どおりで、変更の後も保たれるか |
| `archsig paths <経路> <経路>` | 4. 経路や順序で結果が変わるか |
| `archsig plan choices <候補>` | 6. 条件を満たす変更は何通りあるか |
| `archsig plan split <候補> [--reading <読み>]` | 7. 仕事をどう分けるか |
| `archsig next [--for <結果、候補、Law>]` | 8. 次にどこを読むか |

## 結果

| コマンド | すること |
| --- | --- |
| `archsig show <結果>` | 一つの結果の詳細を返す。 |
| `archsig diff <実行> <実行>` | 二つの実行で、新しく成り立たなくなった結果と、成り立つようになった結果を返す。 |
| `archsig verify <実行>` | 実行の検算データを確かめる。 |
