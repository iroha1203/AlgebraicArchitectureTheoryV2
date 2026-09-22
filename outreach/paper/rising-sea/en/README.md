# Rising Sea — English LaTeX source

投稿・公開する英語版の編集元である。日本語原稿 [`../ja/`](../ja/) と同じ内容を英語で書く。
本文内容を変えるときは日英の両方を直し、[日英照合](#日英照合)を通す。

## 構成

| ファイル | 内容 |
| --- | --- |
| `main.tex` | preamble、題名、要旨、各パートの取り込み、文献 |
| `NN-*.tex` | 日本語原稿 `../ja/NN-*.md` と同じ名前の各パート(01 要旨は `main.tex` の abstract 環境に取り込む) |
| `references.bib` | 文献。書誌は `../ja/14-references.md`、原典確認は [`../references.csv`](../references.csv) |
| `pending-labels.tex` | 未翻訳のパートにある番号の仮ラベル。全パートの翻訳後に削除する |
| `arxiv-abstract.txt` | arXiv の要旨欄に入れる短縮版要旨(metadata 用) |

## ビルド

共通の検査・隔離ビルド・投稿用 source の作成は [paper tools](../../_tools/README.md) と
[`../paper.json`](../paper.json) を使う。

```bash
python3 outreach/paper/_tools/paper.py check outreach/paper/rising-sea/paper.json
python3 outreach/paper/_tools/paper.py build outreach/paper/rising-sea/paper.json --out .tmp/paper-rising-sea
```

## arXiv 用の短縮版要旨

`arxiv-abstract.txt` は、arXiv の投稿画面の要旨欄にそのまま貼る短縮版である。
本文の要旨(`01-abstract.tex`)は日本語原稿と同じ内容を保ち、短縮版はそこから
五つの判定と主定理を保持して、要旨欄の字数上限(1,920文字、
[arXiv 投稿要件](../../../../docs/paper/arxiv.md))に収めた派生物とする。
ASCII のみで書き、数式・特殊文字を使わない(Čech は Cech と書く)。
本文の要旨を変更したときは短縮版へも反映する。投稿前確認では、字数と最新の
投稿要件を再確認して `submission.md` に記録する。

## 原稿の規約

- 定義・構成・定理・補題・命題・系・例は、章ごとの共通カウンタで自動採番する。
  番号は日本語原稿と同じになる。ラベルは `def:1.1`、`thm:1.18` のように種別と番号で付け、
  環境の直後に置く。節は `sec:1.1`・`sec:P.1`、章は `chap:1`、付録は `app:A`、図は `fig:2.1`。
- 式番号は日本語原稿の番号を `\tag{1.27}\label{eq:1.27}` で付け、`\eqref` で参照する。
- 準備節の節番号は P.1…、Related Work は R.1…。`main.tex` の `\lettersections` が切り替える。
- 数式は日本語原稿の式をそのまま移す。GitHub 表示用の Unicode 字(𝒞、ℤ、𝐒𝐞𝐭 など)は
  `\mathcal`・`\mathbb`・`\mathbf`・`\mathfrak` へ戻す。
- 引用は `\cite[\href{URL}{Tag~0013}]{Stacks}` の形で、文献の見出しは引用キーそのもの
  (`[Stacks, Tag 0013]`)。文献一覧の順序は日本語原稿に合わせ、`main.tex` 冒頭の `\nocite` で固定する。
- TeX と BibTeX の source は ASCII のみで書く(アクセントは `\v{C}` などの命令)。
- 本文にはリポジトリ内部の管理用語を書かない([論文の語彙](../../../../docs/paper/guideline.md#論文の語彙))。

## 日英照合

[`../tools/ja_en.py`](../tools/ja_en.py) が、日本語原稿と英語原稿の機械的に対応する部分を照合する。

```bash
python3 outreach/paper/rising-sea/tools/ja_en.py check --aux .tmp/paper-rising-sea/build/main.aux
```

- 数式: 各パートの数式の集まりが一致する。`\text{}` の中の注記だけが異なる式は件数を示す。
- 番号: 番号付き項目・節・章・式・図の番号と種別が一致し、組版後の番号もラベルと一致する。
- 相互参照: 日本語原稿の参照先と `\ref`・`\eqref` の参照先が一致する。
- リンク: URL の集まりが一致する。引用に移した URL は `references.bib` の該当項目で数える。
- 英語原稿に日本語・ASCII 以外の文字・未解決の Markdown リンクが残っていない。

`skeleton` は、日本語原稿の構造・数式・番号・参照を TeX へ移し、地の文を日本語のまま残した
翻訳用の骨組みを出力する。`pending` は `pending-labels.tex` を生成する。

## 用語の対応

同じ日本語の用語には同じ英語を当てる。本文に載せる英語はこの表に従う。
Atom・Law は大文字で書き、reading・core・configuration・source などは小文字で書く。
外部の意味論の法則(lens の三法則など)は小文字の law とする。

### 対象と構成

| 日本語 | English | 注記 |
| --- | --- | --- |
| 型付きの原始的事実 | typed primitive fact | |
| Atom、Atom族 | Atom, Atom family | |
| 種別・軸・対象・述語・内容(Atomの座標) | kind, axis, subject, predicate, payload | ここの「対象」は subject |
| 抽出、抽出doctrine、抽出族 | extraction, extraction doctrine, extracted family | |
| configuration、architecture object | configuration, architecture object | |
| 構造データ、量 | structure data, quantity | |
| operation、操作 | operation | 同じ概念 |
| invariant、signature | invariant, signature | |
| 局所文脈、文脈圏 | local context, context category | |
| 方程式系、残差、記号的座標 | equation system, residual, symbolic coordinate | |
| 対象形成 | object formation | |
| 基点(第1章の $A_r$) | base object | |
| 被覆、重なり、被覆要件 | cover, overlap, coverage requirements | |
| 係数、係数環、係数変更 | coefficients, coefficient ring, change of coefficients | |
| 幾何、完全幾何 | geometry, full geometry | |
| 三段の射影、射影の塔 | three-level projections, tower of projections | 段 = level、段階 = stage |
| 抽出の底、底、底の射 | extraction base, base, base morphism | 底 = base、基準 = reference |
| 基準、基準fiber、基準view | reference, reference fiber, reference view | |
| 変更先、変更前、変更後 | target, original, after the change | |
| 実際の | actual | 付録Aの「実」も actual |

### 局所整合性と診断

| 日本語 | English | 注記 |
| --- | --- | --- |
| 局所整合性 | local consistency | |
| 貼り合わせ、貼り合う | gluing, glue | 層の意味。比較・面の貼り合わせは pasting |
| 障害、障害類、障害クラス | obstruction, obstruction class | |
| 零性、消滅、同時消滅 | vanishing, vanishing, simultaneous vanishing | |
| 補正、修復、大域的修復 | correction, repair, global repair | |
| 大域状態、局所状態 | global state, local state | |
| 零点空間、lawful locus | zero locus, lawful locus | |
| 解像度、標準解像度 | resolution, canonical resolution | |
| 診断、診断類、診断複体 | diagnosis (diagnostic), diagnostic class, diagnostic complex | |
| 条件C、一様不変性 | Condition C, uniform invariance | |
| 台 | support | Spec の台は underlying set |
| 細分 | refinement | |
| 始点・終点(グラフ) | start, end | AAT の source と区別する |
| 道、経路 | path, route | 二経路 $D,V$・構成経路は route。プロトコルの経路は path |
| 判定(変更を判断すること、五つの判定) | judgment | 零・非零などの判定結果は verdict |
| 判定(有限判定、判定可能) | decision, decidable | 第7章の観測による判定は determine |

### 輸送・比較・正規化

| 日本語 | English | 注記 |
| --- | --- | --- |
| 輸送、運ぶ、移送 | transport, carry, transfer | |
| exactな変更 | exact change | |
| 強いopcartesian射、強いcartesian射 | strongly opcartesian morphism, strongly cartesian morphism | |
| 再添字づけ | reindexing | |
| 標準(射・比較・輸送・lift) | canonical | 教科書の標準的構成は standard |
| 指定(比較・障害類・自己同型) | specified | 指定点は designated point |
| 整合性(比較・図式・輸送) | coherence | 射影との整合は compatibility |
| 食い違い、不一致 | discrepancy, mismatch | |
| 辺の再選択、再選択軌道 | edge reselection, reselection orbit | |
| 合成比較、単位比較 | composition comparison, unit comparison | |
| 基底変換、引き戻し | base change, pullback | fiber product は fiber product |
| 生成比較、可逆な比較 | generated comparison, invertible comparison | |
| 有限code、有限例外表 | finite code, finite exception table | |
| 実現台 | realized locus | |
| 冪等正規化、冪等射、冪等像 | idempotent normalization, idempotent, idempotent image | |
| 冪等完備化 | idempotent completion (Karoubi envelope) | |
| 標準表現(設計上の表現) | standard representation | |
| 選択対象、選択 | selected object, selected | |

### 変更と再構成

| 日本語 | English | 注記 |
| --- | --- | --- |
| 比較を保つ変更、比較保存群 | comparison-preserving change, comparison-preserving group | |
| 適合する、適合性 | compatible, compatibility | 比較への適合(定義7.2) |
| 追随する、追随変更 | follow, following change | |
| 持ち上げ | lift | |
| 観測、観測準同型 | observation, observation homomorphism | |
| 可視変更、可視群、隠れ状態 | visible change, visible group, hidden state | |
| 分裂短完全列 | split short exact sequence | |
| 表示(第8章・有限表示・表示の射) | presentation | 画面の表示は display、表示値は displayed value |
| 積表示 | product decomposition | |
| 有限片、整合族、整合条件 | finite fragment, compatible family, compatibility condition | |
| 分離、組立て | separation, assembly | |
| 原始データ、局所モデル、局所圏 | primitive data, local model, local category | |
| 再構成、局所再構成、回復 | reconstruction, local reconstruction, recovery | |
| 構造保存射、意味保存射 | structure-preserving morphism, semantics-preserving morphism | |
| 型付き(対象・射・構成) | typed | |
| 方式(射の方式) | variant | 代表表示による方式 = representative variant |
| 復号関手、復号写像 | decoding functor, decoding map | |
| 読取り(lens の $g$) | read | 更新($p$)は update |
| 読取り(その他の写像・関手・項目) | readout | reading は AAT の reading に限る |
| 格納する(意味論を体系に) | encode | |

### CS の意味論と例

| 日本語 | English | 注記 |
| --- | --- | --- |
| モデル同期 | model synchronization | |
| lens、全域lens、積lens | lens, total lens, product lens | |
| プロトコル、制御点、名前付き操作、実現 | protocol, control point, named operation, realization | |
| adapter | adapter | |
| 行内送金システムの刷新 | modernization of an intrabank transfer system | |
| 口座・送金・会計の各担当 | account, payment, and accounting teams | BIAN の Current Account・Payment Execution・Financial Accounting |
| 配送先、未設定値 | shipping address, unset value | |
| ワーカー、コンテキストの受渡し | worker, handoff of contexts | 待機中・実行中は Queued・Running |

### 章題

| 日本語 | English |
| --- | --- |
| 序論 | Introduction |
| 準備と記法 | Preliminaries and Notation |
| 第1章 相対的アーキテクチャの構成 | Construction of Relative Architecture |
| 第2章 Lawの幾何と局所整合性 | Geometry of Laws and Local Consistency |
| 第3章 標準解像度と診断不変性 | Canonical Resolution and Diagnostic Invariance |
| 第4章 輸送と合成の整合性 | Transport and Coherence of Composition |
| 第5章 基底変換と生成比較 | Base Change and Generated Comparisons |
| 第6章 冪等正規化と実現 | Idempotent Normalization and Realization |
| 第7章 比較を保つ変更と情報 | Comparison-Preserving Changes and Information |
| 第8章 表示と局所再構成 | Presentation and Local Reconstruction |
| 結論と今後の方向 | Conclusions and Further Directions |
| 付録A Lean形式化との対応 | Correspondence with the Lean Formalization |
| 付録B リポジトリとLeanのビルド | Repository and Lean Build |
| 付録C AI利用の開示 | Disclosure of AI Use |
