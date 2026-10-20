# ArchSig v0.6.0

共通の Atom 定義を参照する Law・ArchMap を検査し、観測環境の view の値と Law の
成立・反証・未決を、型と導出元を持つ結果として計算する Rust クレートである。
旧版 [`tools/archsig`](../archsig/) とは独立している。

## ビルドと利用

リポジトリルートで実行する。Rust 2024 edition 対応のツールチェーンが必要であり、
`--offline` は依存 crate がローカルに取得済みであることを前提とする。

```bash
cargo build --offline --manifest-path tools/archsig_v0.6.0/Cargo.toml -j 1
export PATH="$PWD/tools/archsig_v0.6.0/target/debug:$PATH"
archsig version
```

三入力と問いを一回の run へ渡す。`--out` には存在しないディレクトリを指定する。

```bash
archsig run --atom-definition tools/archsig_v0.6.0/tests/fixtures/counter.atoms.json \
  --law tools/archsig_v0.6.0/tests/fixtures/counter.law \
  --archmap tools/archsig_v0.6.0/tests/fixtures/counter.archmap.json \
  --ask 'n=evaluate(CountCheck.amount,s=@v/s)' \
  --ask 'ok=check(CountCheck.nonnegative,s=@v/s)' \
  --ask 'audit=check(CountAudit.bounded,s=@v/s)' --out result-counter
jq '.answers[] | {id, status}' result-counter/result.json
jq -r '. as $r | .answers[] | select(.id == "n") | .outputs.value.node as $id
  | $r.nodes[] | select(.id == $id) | .value' result-counter/result.json
```

回答は3件とも established、値は2で、終了コードは0となる。値を12へ変えるとboundedは
refutedで終了コード1、count Atomを除くと不足位置付きundeterminedで終了コード2となる。
型、導出、支持と入力コピーは同じresult.jsonから確認できる。

同じrunへ `--ask 'need=needed($audit)'` を加えると、依存先の未観測位置を
`need.outputs.plan` のObservationPlanで読める。`requirements` はslot・依存Ref・元位置、
`blockers` は欠測以外の理由を保持する。この例のcount=12の反証には追加の観測要求はない。

以前の出力directoryは `--reuse result-counter` で候補として指定できる。
現在の三入力から全再計算し、検査済みの導出へ候補の型・内容・全依存・由来を照合する。
node番号や共有方法の違いは吸収し、候補の推論は計算へ採用しない。
照合できない候補も通常の評価を妨げず、理由は結果の `reuse.rejected` に残す。

### 入力だけの検査

共通定義・Law・ArchMap を一回の check で検査する。

`--out` には存在しないディレクトリを指定する（出力先が既に存在する場合は別の名前にする）。

```bash
archsig check --atom-definition tools/archsig_v0.6.0/tests/fixtures/reservations.atoms.json --law tools/archsig_v0.6.0/tests/fixtures/reservations.law --archmap tools/archsig_v0.6.0/tests/fixtures/reservations.archmap.json --out result-check
```

`status=complete`、終了コード0となる。結果は `result-check/result.json` に保存し、stdout には一行の receipt を出す。
結果の形式は `archsig.result/2`。定義のコピーは `inputs/definitions/0.json` に置き、
入力 ID `definition0` と JSON Pointer から元の定義位置を追える。

複数の定義ファイルは `--atom-definition` を指定順に繰り返す。
明示したファイルだけを読み込み、未使用の語彙・依存・import も検査して保持する。
ファイル操作と終了コードの詳細は [実行仕様 §§5–7](../../docs/tool/archsig_v0_6_0_io/execution.md#5-ファイル操作と出力)を参照する。

## Rust API で観測値を評価する

呼出し側の crate から、このディレクトリを `archsig` の path dependency として指定する。
次の例の実行時 cwd はリポジトリルートとする。三入力の byte 列を渡すと、入力検査と
要求解決を経て Counter の値と二つの Law を評価できる。

```rust
use archsig::observed::{
    control::{Control, Limits, Usage},
    evaluate_observed_bytes,
    input::InputSources,
};

fn main() -> std::io::Result<()> {
    let fixtures = std::path::Path::new("tools/archsig_v0.6.0/tests/fixtures");
    let sources = InputSources::from_bytes(
        vec![std::fs::read(fixtures.join("counter.atoms.json"))?],
        std::fs::read(fixtures.join("counter.law"))?,
        std::fs::read(fixtures.join("counter.archmap.json"))?,
    );
    let asks = [
        "n=evaluate(CountCheck.amount,s=@v/s)",
        "ok=check(CountCheck.nonnegative,s=@v/s)",
        "audit=check(CountAudit.bounded,s=@v/s)",
    ];
    // この小例は予算制限・取消通知を設定しない。
    let mut control = Control::new(Limits::default(), |_| Usage::default());
    let result = evaluate_observed_bytes(sources, &asks, &mut control)
        .expect("対応範囲内の Counter 例");
    println!("{}", result.wire().canonical());
    Ok(())
}
```

結果の `status` は `complete`、`n` の値は型 `Z`・payload `"2"`、`ok` と `audit` は
`established` となる。Bool=false の view も値が確定すれば `established`、同じ false を
要求する Law は `refuted` となる。`guard=false` の行は `not_applicable` として保持する。

入力検査と要求解決を分ける場合は [`prepare_observed`](src/observed/mod.rs) と
`evaluate_observed`、検査済み bundle を使う場合は `prepare_checked_observed` を使う。
view は全 parameter の束縛を必要とし、Law の未束縛 parameter は型の全域で検査する。
同じ batch の `$id.value`・`$id.evaluation.value` と公開成分射影を後続の束縛へ渡せる。
計算は依存順、回答は指定順に返し、循環は要求 ID と依存グラフを保持して拒否する。
`Control` は入力検査・要求解決・評価で共有し、呼出し側が予算と計測・取消通知を設定できる。

検査済み三入力の対象構成を読むには
`construction::construct(&checked, "CountCheck", "v", "s", &mut control)` を使う。
`universe()` は全snapshotの存在事実と既知field Atom、`base()` と `components()` は
選択rootとowned entityのConfiguration候補を返す。候補の `configuration()` は構成が
確定した場合に値を返す。未観測の所属・参照がある場合は `known()` の断片と
`blocking_slots()` を読み、未観測の数量slotは `requirements()` で確認する。
`recheck()` は現在の検査済み入力と同じ選択から構成を再照合する。
このRust APIのConfigurationと、LawやObjectAlgebraの成立は別の計算結果である。

## 仕様

- [I/O 仕様](../../docs/tool/archsig_v0_6_0_io/README.md): 入力・問い・型付き結果の形式と意味。
- [実行仕様](../../docs/tool/archsig_v0_6_0_io/execution.md): コマンド構文、出力、終了コード。
- [計算仕様](../../docs/tool/archsig_v0_6_0_io/computations.md): 対象・写像・診断・修復の構成と決定範囲。

## テスト

クレート内の小さい試験を exact 名で一件ずつ実行する。入力検査と
上の Rust API 例に対応する試験は次のとおり。

```bash
cargo test --offline --manifest-path tools/archsig_v0.6.0/Cargo.toml -j 1 --test cli normative_examples_complete_both_checks -- --exact --test-threads=1
cargo test --offline --manifest-path tools/archsig_v0.6.0/Cargo.toml -j 1 --test observed_counter_evaluation counter_two_has_typed_ordered_complete_answers -- --exact --test-threads=1
```

他の試験は `--test TARGET NAME -- --exact --test-threads=1` で対象を指定する。
`tests/fixtures/` の規範例は [適合例](../../docs/tool/archsig_v0_6_0_io/validation.md)の
`examples/` と同じ byte 列を保持し、テスト入力はクレート内の fixture を使う。
