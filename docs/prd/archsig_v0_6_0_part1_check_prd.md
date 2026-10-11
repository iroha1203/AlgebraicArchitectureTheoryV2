# ArchSig v0.6.0 第1パート PRD: 二入力の静的検査

## 問いと到達点

Law の作者と ArchMap の観測者が、宣言の読みと二入力の適合を、元の入力位置に
戻れる結果で確認できるか。

第1パートは **`archsig check` の完成**とする。Law 全体の構文・名前・型・再帰を解決し、
語彙 manifest を生成する。ArchMap が指定された場合は、その語彙との binding、
原始値・参照・由来・補完の整合性まで検査する。利用者は manifest を観測に使い、
作成した ArchMap を同じ Law で検査できる。

この検査は後続の全計算に共通する依存であり、solver や対象構成を待たずに
規定済みの `check` の入出力だけで受入判定できる。成功は入力検査の完了を意味する。

## 設計基準

- [I/O 仕様](../tool/archsig_v0_6_0_io/README.md)の
  [入力](../tool/archsig_v0_6_0_io/inputs.md)、[Law](../tool/archsig_v0_6_0_io/law.md)、
  [実行](../tool/archsig_v0_6_0_io/execution.md)、[結果](../tool/archsig_v0_6_0_io/results.md)、
  [適合例](../tool/archsig_v0_6_0_io/validation.md)のうち、`check/version` の要件を実装する。
  外部の構文・版・欄・状態・終了コードはこれらに従い、段階実装用の変更を加えない。
- [製品コンセプト](../tool/archsig_v0_6_0_concept.md)、
  [Atom と Law のエンジン設計](../tool/archsig_atom_law_engine/README.md)と
  [設計判断](../tool/archsig_atom_law_engine/decisions.md)を構成の基準とする。
  同文書の設計記法を、I/O 仕様の DSL に追加しない。
- Law は語彙・意味・条件・許す変更を宣言し、ArchSig は二入力から構成・計算する。
  SQL とクエリプランナーの分担と同様に、作者へ計算計画の配線を要求しない。
  DSL の解釈、realization・写像の生成と正確性は ArchSig の責務である。
  実コードの観測と忠実な ArchMap の作成は観測者の責務とし、追加の AAT 証明を
  このパートの開始・完了条件にしない。

## 実装範囲と入出力

独立した Rust クレートを **`tools/archsig_v0.6.0`** にゼロから新規実装する。
ソース、Cargo manifest/lock、テスト、fixture、利用手順をこのディレクトリに置く。
v0.5.x 系のコード・fixture・テストのコピー、移植、流用を禁止する。
旧版とのリンク、path dependency、ソースの共有・参照読込み、実行時呼出し、
ビルド・テストを介した間接依存も導入しない。旧版は変更しない。
一般の第三者ライブラリは新クレートから利用できる。
旧版の入力・CLI・artifact との互換性は要求せず、旧版の挙動を正解とする互換テストも作らない。

実装する利用経路は次の三つとする。`A` と `L` はローカルファイル、`OUT` は未作成のディレクトリである。

```text
archsig check --law L --out OUT
archsig check --law L --archmap A --out OUT
archsig version
```

| 対象 | 完成条件 |
| --- | --- |
| Law の検査 | Law 仕様の全宣言・型・式を構文解析し、名前・alias・束縛・依存型・構造再帰・純粋性を検査する。利用されない宣言や実行されない分岐も検査し、原式の出現と byte span を保持する。計算算法の対応範囲を理由に、有効な式を拒否しない |
| 語彙と解決結果 | manifest と digest、全 DeclarationInfo、参照先・式の型・既定規則を生成する。明記と省略を区別し、暗黙 align や guard の説明を原始語彙へ混ぜない |
| ArchMap の検査 | 入力仕様の全型・encoding、ID、field、snapshot、owner、Map の全域性、binding、origin/source を検査する。有限の構造検査で補完の存在を確認する。欠測 slot の identity と型を保持し、Law の成立を補完条件に使わない |
| 内部表現 | 型付き宣言、原式・出現位置、参照・依存関係、既知値と欠測 slot、由来を保持する。表示用 JSON から情報を復元せず、後続処理へメモリ上で渡せる構成にする。新しい外部 IR ファイルを追加しない |
| 出力 | 実行仕様 §§5–7 と結果仕様 §1 に従い、開始時の入力コピー、`result.json`、stdout の一行 receipt を出す。`check` の `requests/answers/nodes` は成功・失敗とも空とする。`version` は既定の一行 JSON を返す |

対象外は `run` の問い解決・評価、対象・写像・cover・複体の生成、診断、solve/repair、
再利用、観測 SKILL、実コード観測の PoC、旧版移行、配布・CI への追加とする。
提供範囲は `check/version` と明示し、v0.6.0 全体の適合版として配布しない。
未実装の `run` を、空の成功結果や `unsupported_algorithm` を返す代替処理で提供しない。

## 失敗時の振る舞い

[実行仕様 §6](../tool/archsig_v0_6_0_io/execution.md#6-状態終了コード予算)と
[IssueCode](../tool/archsig_v0_6_0_io/results.md#6-証拠と理由)に従い、入力位置と理由を返す。
特に次を検証する。

- 構文・型・参照・重複・binding・補完不能の不正入力は `invalid/65`、未知版は
  `unsupported/69`、CLI の不正は `invalid/64` とする。未知版の欄を先に未知欄として拒否しない。
- 欠測を零・空・none に補わない。型の正しい Map の端点不保存や、偽となる Law は
  入力エラーにしない。`check` から Law の成立・反証を返さない。
- Law 検査が未完了なら宣言・語彙の表は空とし、完了後に ArchMap の検査だけが失敗した場合は
  両表を保持する。実装の欠落を検査成功、反証、数学的な算法非対応へ読み替えない。
- 読込み・出力失敗、内部障害、SIGINT/SIGTERM は既定の状態と終了コードへ接続する。
  出力の非上書き、finalize と receipt 配送の区別を実行仕様どおりに保つ。

受入条件を満たすために I/O の変更、入力の意味の縮小、検査の省略が必要になった場合は
実装を停止し、不一致箇所と必要な判断を報告する。仕様の変更を実装内で決めない。

## Acceptance Criteria

v0.6.0 の仕様から新しく定めた CLI テストと単体テストで、次の全項目を満たす。
fixture は[適合例](../tool/archsig_v0_6_0_io/validation.md)に基づいて新クレートに置き、
テスト時に docs や旧版を読み込まない。期待値は新旧の実装出力から転記せず、v0.6.0 の仕様から定める。

1. **利用の一周。** Reservations と Engine の両規範例を無改変で fixture にする。
   Law 単独から得る語彙 digest が例の binding と一致し、対応する ArchMap と再検査すると
   `complete/0` となる。入力コピーは元 byte 列と一致し、
   `result.json`、receipt、実終了コードが整合する。ArchMap 省略時は inputs にその欄を作らない。
2. **DSL 全体の検査。** 両例に加えて、use/alias、align、relation/Path、Term、全 container・数値型の
   正例と、名前衝突・循環・型不一致・不正再帰・捕獲・不正な型位置の負例を持つ。
   非アフィン式や無限量化も型が正しければ受理する。空の観測族でも不正な body を拒否する。
3. **解決の追跡。** Reservations の短形と明示形で、語彙 digest・解決先・body の型が一致し、
   `guard_true` の有無と元 span が区別される。`local_declared/local_support`、暗黙 align、
   constructor metadata を検査し、全 Location が同梱入力の実在箇所を指す。
4. **原始値と整合性。** 欠測、零、空 List/Set、Option none を別々に保持する。
   任意精度 Z、既約 Q、Fp の素数・範囲、有限木、Term の型・純粋性、snapshot を含む参照、
   origin の条件を正負で検査する。未知 owner/ref/Map に補完がある例を受理し、
   補完不能を `inconsistent_observation` とする。既知の不正参照、Map 全域性違反、
   同値でも重複した fact は拒否する。端点不保存の Map と Law 反証例は静的検査を通る。
5. **digest と順序。** Law の空白・コメント変更で、各 digest のうち bytes_digest だけが変わり、
   原始宣言を保つ条件変更で語彙 digest は変わらず Law の model_digest が変わる。
   ArchMap の集合表順は model_digest を変えず、List の順・重複は保持する。
   Unicode・制御文字の canonical bytes と digest を固定期待値で検査し、文字列を正規化しない。
6. **拒否と出力保持。** 重複 JSON key、未知欄、null、不正 UTF-8/BOM/surrogate、未知版、
   binding 不一致、CLI 不正で code・位置・終了コードを検査する。
   Law の失敗と ArchMap の失敗で宣言・語彙の保持が異なり、全 check 結果の
   requests/answers/nodes が空であることを確認する。
7. **ファイルと中断。** 入力 symlink は開始時に解決し、source URI・Law 参照の追加読込みをしない。
   既存出力先、出力確定時の競合、read/write/flush/rename 失敗、SIGINT/SIGTERM、
   公開後の receipt 配送失敗を再現し、非上書きと実行仕様の確定状態を確認する。
8. **独立性。** `cargo test --manifest-path tools/archsig_v0.6.0/Cargo.toml` で全テストを実行でき、
   ソース・依存関係・ビルド・テストに v0.5.x 系のコピー・移植・流用・直接間接の依存がない。
   互換テストを含め、旧版の挙動を期待値に使わない。`version` は実行仕様に一致する。
   新クレートの利用手順から上記二つの check を再現できる。

## 実装順と次パートへの接続

1. 新クレートに、位置付きの入力読込み、Law の構文・型検査、manifest・digest を新規実装する。
2. ArchMap の型・参照・補完の整合性検査を新規実装して接続する。
3. check/version と出力確定処理を新規実装し、v0.6.0 の仕様から定めた受入テストを完成させる。

次パートは、同じ検査を通した内部表現へ問いの解決と評価を接続する。
元の二入力を引き続き必須とし、check の結果 JSON を第三入力にしない。
局所の公開値、原式の各出現、change の元 parameter と更新を保持して引き渡す。
後続の修復は[元 Assignment の一意性](../tool/archsig_v0_6_0_io/computations.md#修復の一意性)に従い、
複数解では SolutionSet と存在判定を保持し、Repair/object を生成しない。
複数解を同じ更新後状態や JSON shortlex で一つに選ぶ処理を、この段階の正規化へ入れない。
実コードを観測して使う PoC は、計算エンジンの実装後に扱う。
