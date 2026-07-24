# train-ticket ドッグフーディング系列

外部 OSS [FudanSELab/train-ticket](https://github.com/FudanSELab/train-ticket)
(Benchmark Microservice System、commit `313886e99bef`)に対して、公開ワークフローどおりに
ArchMap 供給 → LawPolicy → `archsig analyze` → gate → ArchView 表示を通した end-to-end 実験の系列。

| 段 | 報告 | 実施日 | 対応 Issue |
| --- | --- | --- | --- |
| 1. 試運転 | [trial.md](trial.md) — cancel/refund スライス 7.4kLOC のワンショット | 2026-07-18 | #3498 |
| 2. フルビルド | [fullbuild.md](fullbuild.md) — 全42サービス+ts-common 28.5kLOC の完全抽出と計測 | 2026-07-18 | #3545 |
| 3. SAGA フル診断階段 | [saga_diagnosis.md](saga_diagnosis.md) — 実在 one-cent 三角形の非零類 → BLOCKED → repair 事前検証 → PASS | 2026-07-19 | #3545 |

系列全体の中心的成果は第3段にある: **「局所的には合法、大域的に貼り合わない」構造
(3流儀 × 1-サイクル × triple 不在)が、合成例ではなく実在 OSS に存在し、
非零 F₂ 残差類として計測された。**

## 証拠束(evidence/)

各報告の数値・結論コードの一次根拠を `evidence/` にコミットしている。trial / fullbuild は
ArchSig v0.5.3 の履歴証拠、SAGA 診断階段は ArchSig v0.5.4 の現行再計測証拠である。

| パス | 内容 |
| --- | --- |
| `evidence/trial/` | 試運転の ArchMap(431 atoms)・調停記録・timelog、`law/` に LawPolicy 3点+bundle、`analyze/` に当時の analyze/gate 一次出力、`analyze-postfix/` に PR #3504(vacuous zero 是正)後の同一入力再実行 |
| `evidence/fullbuild/` | scope-manifest、統合 ArchMap(2,118 atoms)+ money/status 変種、調停・整合性・正準化記録、coverage ledger、供給指示書、ArchView スクリーンショット |
| `evidence/fullbuild/law/` | money / status 各系列の LawPolicy・law surface・measurement profile・policy bundle |
| `evidence/fullbuild/analyze-money/`, `analyze-status/` | analyze / gate 一次出力(summary・packet・gate report・insight report/brief・run manifest・validation 一式) |
| `evidence/saga/` | SAGA 用 ArchMap 変種(head / repaired)、law surface・policy・profile・gate policy、presentation-generated repair-plan(head / repaired)、builder スクリプト |
| `evidence/saga/out/` | head / repaired の analyze 一次出力、compare 出力、gate report(head / repaired) |

### 除外物と再生成

コミットしていないものは2種類ある。

1. **再実行で導出可能な重量出力** — `archsig-atom-viewer-data.json`(run あたり約7.4MB)と
   `normalized-archmap.json`。下記の再現コマンドを実行すると `--out-dir` に再生成される。
2. **中間生成物** — dual-pass の候補パケット、extraction 実験、preview run、SAGA 作業用の
   train-ticket checkout。正本記録の対象外であり、ローカル退避(`.tmp/dogfooding-evidence/`)にのみ残る。

供給指示書・build スクリプト内のローカル絶対パスは `<REPO>` / `<SCRATCHPAD>` に redact してある
(digest 固定対象は JSON artifact のみで、指示書・スクリプトは対象外)。

未保存物: 試運転の gate policy は実体が保存されておらず、
`evidence/trial/analyze/archsig-gate-report.json` の `inputDigests.gatePolicy` に digest のみ残る。
フルビルドの gate policy は repo 内 fixture
`tools/archsig/tests/fixtures/ag_measurement/gate_policy_conservative.json` そのもの(canonical digest 一致)。

### digest 整合の機械検査

```bash
python3 docs/reports/train_ticket_dogfooding/evidence/verify_digests.py
```

コミット済みの各 analyze summary / gate report の `inputDigests` と、コミット済み入力 artifact の
canonical JSON digest の一致を検査する(2026-07-19 時点で全 33 検査 OK)。

### 再現コマンド

**注**: trial / fullbuild の履歴証拠は ArchSig v0.5.3 artifact であり、schema 版数は受理完全一致のため、
再現には v0.5.3 時点の tree(2026-07-19 の main、例: PR #3626 マージコミット)を使う。
SAGA 診断階段はこの tree の ArchSig v0.5.4 で再現する。

すべて deterministic であり、2026-07-19 にコミット済み証拠束から再実行して確認済み:
フルビルド・SAGA の全 run は runId・結論コード・gate 判定まで一致、試運転は runId 一致で
結論コードは PR #3504 是正後の挙動(`evidence/trial/analyze-postfix/` と一致)になる。
例(フルビルド money 系列):

```bash
EV=docs/reports/train_ticket_dogfooding/evidence
cargo run --manifest-path tools/archsig/Cargo.toml -- analyze \
  --archmap $EV/fullbuild/archmap-money-variant.json \
  --law-policy $EV/fullbuild/law/law-policy-money.json \
  --law-surface $EV/fullbuild/law/law-surface-money.json \
  --measurement-profile $EV/fullbuild/law/measurement-profile-money.json \
  --out-dir .tmp/reports-repro/fullbuild-money
cargo run --manifest-path tools/archsig/Cargo.toml -- gate \
  --packet .tmp/reports-repro/fullbuild-money/archsig-measurement-packet.json \
  --policy tools/archsig/tests/fixtures/ag_measurement/gate_policy_conservative.json \
  --out .tmp/reports-repro/fullbuild-money/archsig-gate-report.json
```

status 系列は `money` を `status` に読み替える。SAGA 診断階段(head / repaired の analyze、
compare、gate ×2)の完全な再現手順は [saga_diagnosis.md](saga_diagnosis.md) に記載する。
