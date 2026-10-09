# 構文・型・入出力の検証

## 1. 一つの Law、三つの入力

[Law](examples/law.json) は、一つのsnapshot内の名前付き有理数操作の全順序対について、
二つの合成の作用が等しいかを問う。原始語彙はOperationの存在とbodyだけである。
式の入力順は `then(f,g)=g∘f`。

| 入力 | 原始の式 | 出力の要点 |
| --- | --- | --- |
| [反証](examples/refuted.archmap.json) | f(x)=x+1、g(x)=2x | `affine/commute: refuted`。x=0でg(f(x))=2、f(g(x))=1。exit1 |
| [成立](examples/established.archmap.json) | f(x)=x+1、g(x)=x+2 | 4順序対すべての全Q代入で成立。`established`、exit0 |
| [欠測](examples/missing.archmap.json) | fの式だけ記録、gの存在は保持 | `undetermined/missing_observation`。missingは(sample,g,affine/body)。exit2 |

三入力の語彙bindingとLawは同じ。欠測例のgをx+2で補完すると成立、2xで補完すると反証になる。
補完対を観測の反例と呼ばない。端点の一致や同じsupportだけから二操作を同一視しない。

想定呼出しは次である。これは新CLIの仕様例であり、現存v0.5.x binaryのコマンドではない。

```sh
archsig run --archmap examples/refuted.archmap.json --law examples/law.json --out result-refuted
```

出力の `Answer` はquery、Proposition参照、status、証拠参照、scopeを持つ。
反証の `Evidence.kind=counterexample` には、型Qの値0の代入、二つの順序を持つ操作経路、
型Qの2と1、二つのbody Atomへの原始位置を保存する。
方程式の全Q量化はscope.domain=all_assignments、quantifiersにQ変数のforallとして残る。
欠測回答は同じ位置をmissingに持ち、provisionalな式を確定valueに置かない。

式を短く書くための独自入力フォーマットは追加していない。基本例の4ファイルはすべて通常のJSON。
入力の観測sourceは本文の二行の式を表す小さな実装例であり、source digestの検算も
[検算スクリプト](verify_examples.py)内で再現できる。

## 2. 自己モデルの小さな構成

[自己Law](examples/self.law.json) と [自己Atom](examples/self.archmap.json) も同じ書式を使う。
SourceのVar/Lit/Add、IRのLoad/Const/Plus/Minusをdataで定義し、foldで変換と二つの評価を記述する。
原始入力はsource treeと候補の演算選択だけ。完成IR、行列、保存判定は入れない。

sourceはx+(1+2)。AddをPlusへ写す候補はx+3、Minusへ写す候補はx−(1−2)=x+1となる。
同じLawが、前者の全Q代入での保存と、後者の反証（x=−1でsource=2、IR=0）を計算する。
snapshotはspecification由来であり、実装済みコンパイラの検証結果と混同しない。
この二入力は、自己モデルを型付きADT/構造再帰で表せることの短い確認である。

## 3. 短い反証的な検査

| 試み | 期待する判定と保持する情報 | 根拠 |
| --- | --- | --- |
| 欠測gをjoinで落とす | query未決、gを保持 | subjectから列挙しfield lookupを別に行う |
| 同じHole hの再読 | h−h=0は成立できる | slotのidentityを共有 |
| 2−hを非零多項式として反証 | h=2/3の補完で判断が異なるため未決 | 観測Holeと全称変数の区別 |
| none・[]・欠測の同一視 | Option不在、空の有限集合、Holeを分離 | 原始値のencodingと型 |
| 同じFactRefに二つの値 | invalid_input/duplicate_fact | 単一値predicate |
| 未約分有理数2/2 | invalid_input/type | Qの正規形 |
| 識別子を変えて違う結論を出す | 同型に沿う同じ判断 | ID文字列をLawから解析できない |
| 2z=1をQで解いてZの解とする | Qでは1/2、Zでは整除違反 | 係数環の型引数とSNF |
| 面の[e,e]をSetへ変換 | 係数2を保持 | Listの反復と符号付き和 |
| chart X={0,1}→{*} の二つの投影を潰す | p₁*≠p₂*、差は(0,1,−1,0) | ContextMapがcarrier作用を持つ |
| Lawの十分性から診断同型を付与 | 別の実cochain比較が必要 | sufficientとpreserves_diagnosticsを分離 |
| Čechを次数nで打ち切りH^(n+1)を読む | invalid_construction | last_diagnosable_degree |
| 旧resultのverifiedラベルを採用 | 現在の根から再検査/再計算 | 再利用は第三入力にならない |
| 未観測の候補を全部探索したとする | 量化域をfinite_modelに固定 | 有限候補族と任意の変更を区別 |
| 自己Lawの成功を原始Atomに戻す | sealed値・結果参照の入力を拒否 | 導出根の非循環性 |

三操作の局所例については、原始端点(p,q),(q,r),(p,r)から
`D=[[-1,1,0],[0,-1,1],[-1,0,1]]` を生成し、λ=(1,1,−1)がλD=0を満たすことを検算した。
b=(1,1,3)ではλb=−1、b=(1,1,2)ではz=(0,1,2)を元の式へ代入できる。
この計算は [既存の局所・大域構成](../archsig_atom_law_engine/local_global_example.md)との
接続点の確認であり、行列を新しい入力欄に追加するものではない。

## 4. 実行した検査

```sh
python3 docs/tool/archsig_v0_6_0_io/verify_examples.py
git diff --check
```

検算スクリプトは次を確認する。

- 6 JSONの構文、重複key、例に使った欄・参照、語彙digest。
- 例で使ったExprの束縛と型、原始Termの型、自己モデルのADT/constructor/foldの型。
- 同じLawに対する成立・反証・欠測の算術、非可換な順序、補完対。
- 整数/有理数の違い、反復incidence、chartの平行射、端点からの方程式生成。
- 重複Atom、未約分有理数、未知sortの三つの不正入力変種の拒否。

このスクリプトは固定した例の検算であり、全DSLのparser・solver・ArchSig処理系を実装しない。
未使用の文法の実行検証、全入力に対する型保存、CLIの実動、出力の再読込みは
後続実装の検証事項である。現存ツールのcargo testやLean buildを、新I/Oの成立証拠にしない。

仕様作成中の独立点検では、入力/束縛/欠測、計算の型接続、wire/再利用を分担して確認した。
見つかったpureの間接効果、dataへの導出型混入、role衝突、query/defの循環、
係数型消去、一般chartの射、作用の欠落、出力型消去、DAG自己参照を仕様へ反映した。
これはPR公開後の正式tool-reviewに代わる合格判定ではない。

## 5. 後続実装の適合確認

実装者は上の三入力と反証表に加え、次を同じpublic CLIで確認する。

1. 入力のarray/object順だけを変更して、意味値が対応すること。
2. renameした原始IDの全単射を出力の対象・操作・反例へ運べること。
3. Z/Fpの線形問題、アフィン方程式の局所support、kernelへのlift、商からのfactorを接続できること。
4. 一般chartの二つの制限が別のcochain項になり、d²=0を検査すること。
5. 解なし、零類、修復値、意味側比較を別の型・条件として出力すること。
6. 不正入力・未対応算法・観測不足・予算中断・signal・I/O失敗の終了コードと結果を確認すること。
7. 改竄した再利用候補を破棄し、元の二入力からの結果が変わらないこと。
8. 全resultの型・参照・導出DAGを再読し、原始根と各条件へ到達できること。

これらは本仕様で決めた振る舞いの検査であり、実装時に新しいI/Oを選ぶための保留事項ではない。
