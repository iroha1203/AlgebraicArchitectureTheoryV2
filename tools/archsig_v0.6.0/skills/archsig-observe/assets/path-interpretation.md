# パスの由来と解釈

設定されたglobと、発見して追加するliteral pathを併用する操作を考える。
この自己完結例は架空の候補モデルを読む。実ファイルシステムやpytest実装の観測とは分ける。
要求は、設定patternの対象と発見literalの対象の両方を選択することとする。

## 同じ文字列から異なる対象を読む

平坦な名前集合を `("project?1", "projectX1")` と固定する。
大文字小文字は区別し、相対pathの基準は同じ一つのroot。
この例のidentityは名前の完全一致とし、symlink、実path解決、再帰glob、separatorを含めない。
Python標準の `fnmatchcase` による名前照合だけをglobの意味とする。
`?` は一文字に一致するため、名前に含まれる文字 `?` 自身にも一致する。

```python
from fnmatch import fnmatchcase

names = ("project?1", "projectX1")

def targets(entry, universe):
    origin, interpretation, raw = entry
    if interpretation == "glob":
        return tuple(name for name in universe if fnmatchcase(name, raw))
    if interpretation == "literal":
        return tuple(name for name in universe if name == raw)
    raise ValueError(interpretation)

configured = ("configured", "glob", "project?1")
generated = ("generated", "literal", "project?1")
```

| entry | raw | 解釈 | targets(entry, names) |
| --- | --- | --- | --- |
| configured | `project?1` | glob | `(project?1, projectX1)` |
| generated | `project?1` | literal | `(project?1)` |

同じraw文字列を持つ二つのentryを、文字列の集合や「発見済み文字列への所属」だけで
分類すると、この区別が失われる。発見literalまでglob展開すると余計な `projectX1` が
入り、設定globまでliteral扱いすると要求された `projectX1` が落ちる。
設定と発見のentryを分けて解釈してから対象を合わせれば、この二つを区別できる。

## rawへの所属で生じる誤反証

別の代入 `universe=("project",)`、設定entry `("configured", "glob", "proj*")`、
発見literal `"project"` を考える。設定のrawリストは `["proj*"]` のままで、
`targets` が返す対象は `("project",)` となる。
解釈済みの対象に発見pathが含まれるため、rawへ `"project"` を追加せずとも要求を満たす。

ここで `roots=["project"]` と `testsRaw=["proj*"]` を同じ意味のリストと見なし、
`forall r in roots . r in testsRaw` を採用するとfalseとなる。
この式は文字列包含の追加要求であり、対象包含という元要求と対応しない。
engineがその式を反証しても、実装の対象欠落を示す証拠にはならない。
`testsTargets=["project"]` を別に読み、`forall r in roots . r in testsTargets` と照合する。
元要求が対象包含ならこの対応が必要であり、反証を消すための無条件trueや要求削除で代替しない。

## CLIで区別の必要性を確かめる

同梱の二表の有限族Sは、最初のPythonモデルのconfigured/generatedを
同じ `names` で読む二要素である。vの `targets` は上表の順序付きtupleを読むview。
値はソースと固定代入から手で読み、等号を保つ文字列tokenへ対応づけた。
raw表のqはraw文字列、interpreted表のqは由来・解釈・rawのtupleを読む。
後者のtoken内の `|` はこの二要素だけの符号化で、任意文字列の一般serializerではない。

`cli` と `skill` は [SKILLのバンドル指定](../SKILL.md#バンドルを使う)に従う。

```sh
"$cli" law-fibers --table "$skill/assets/path-raw.json"
"$cli" law-fibers --table "$skill/assets/path-interpreted.json"
```

最初は終了1、adequate_on_table=false。同じrawの一対でtargetsが異なる反例を返す。
二つ目は終了0、adequate_on_table=true。qが二要素を区別するので、この表では十分である。
いずれも空族ではない。これは固定した名前集合でのview値の保存の計算であり、
raw包含式の三入力checkや、任意root・filesystemでの十分性を証明するものではない。
`law-fibers` はPythonを実行せず、globの意味やtokenの正しさを解釈しない。

## 実ソースを三入力へ写す

Atom定義のfieldは、raw設定の出現、発見したliteral、解釈方法、解釈へ渡す基準root、
対象identityの意味を分ける。同じrawを持つ設定出現と発見出現に別entryを持たせるか、
由来付きのListとして保持する。原始の出現indexとbefore/afterの対応を残し、
Kept/Addedを文字列だけに結ばない。設定重複の保持と追加重複の抑止は別の要求として読む。
集合のunionだけで順序や重複の保存を確認済みにしない。

実装観測では、上流の設定読込み、発見側の生成、分岐、展開関数のbinding、
root/cwdの選択、identity比較、選択側の使用箇所を同じentryについて読む。
任意filesystemで展開した値を静的な実装Atomへ埋めない。
上のような固定した名前集合への代入を使うなら候補モデルとして明示し、実装観測と区別する。
解釈後の対象を静的に確定できない場合、読める変換・引数・条件を記録し、
対象集合の具体値を仮定したLawの成立を実装全体の結論へ広げない。
canonical identityを使うなら、文字列一致、root相対の正規化、realpath等のどれを
読むかを明示し、その変換元・基準・対応を保つ。名前から意味を推測しない。

独立した実行検証では、markerを持つ `project?1` と持たない `projectX1` を用意し、
発見だけなら前者、同じ綴りの設定globも指定したら双方が選択されることを確認する。
成功exitだけでなく収集した対象identityを比較する。設定重複、追加重複、rootとsubdirectory、
空の展開、適用するpath正規化も仕様に合わせて検証する。
この実行結果は実装観測Atomと分けて報告する。
