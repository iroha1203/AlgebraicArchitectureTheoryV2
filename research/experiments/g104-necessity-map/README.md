# G-104 necessity map final Stop-B checkpoint

> **これは off-loop 探索 artifact であり、GOAL 完了の証拠ではない。**

Issue #3948 の C0–C6 必要性地図、C* 候補探索、有限 local grammar に対する
非表現可能性証明を exact rational engine で再現する。最終終端は PRD の停止条件 B である。
ただし `task_complete` は実装PRのmergeまで `false` とし、PRDの完了判定とは区別する。

## 成果物

- `necessity_map.py`: R0 calibration、A-subnerve還元、R1必要性地図
- `r2_hunt.py`: 事前登録済みR2候補、二方向query、Round 1–15
- `g_local_v1.py`: H¹・uniformity labelを読まない有限観測 grammar `G_local-v1` と `Obs_G`
- `g_local_v1_stop_b.py`: pure preregistration、immutable Round 15 ledger、Stop-B checker
- `build_results.py`: Round 12までの immutable parent artifact generator
- `build_stop_b_results.py`: Stop-B canonical full / slim summary generator
- `test_necessity_map.py` / `test_r2_hunt.py` / `test_r2_v4.py`: historical engine regression
- `test_g_local_v1_prereg.py`: grammar、source bundle、ledger分離、checker contract
- `test_build_results.py` / `test_build_stop_b_results.py`: parent / Stop-B artifact regression
- `hunt-report.md`: 一般手証明、round履歴、`G_local-v1` 二点分離、最終停止判定
- `results-summary.json`: Round 12までの committed immutable parent summary
- `results-stop-b-summary.json`: final Stop-B committed slim audit summary

canonical full JSONはrepoには置かず、各generatorから得る導出物とする。

## 再現

```bash
cd research/experiments/g104-necessity-map
PYTHONDONTWRITEBYTECODE=1 python3 -m unittest \
  test_necessity_map.py test_r2_hunt.py test_r2_v4.py \
  test_g_local_v1_prereg.py test_build_results.py test_build_stop_b_results.py
PYTHONDONTWRITEBYTECODE=1 python3 build_results.py \
  --output /tmp/g104-necessity-map-results-through-round12.json \
  --summary-output results-summary.json
PYTHONDONTWRITEBYTECODE=1 python3 build_stop_b_results.py \
  --output /tmp/g104-necessity-map-stop-b-results.json \
  --summary-output results-stop-b-summary.json
shasum -a 256 \
  results-summary.json /tmp/g104-necessity-map-results-through-round12.json \
  results-stop-b-summary.json /tmp/g104-necessity-map-stop-b-results.json
```

期待 SHA-256:

```text
afa334056b52938044c0acad9b693a0c437300382b855f32450af5750020caa5  results-summary.json (immutable parent through Round 12)
cabfbcae7075280a6d10de3c819c25ca2396a21deaed2099bafdd71daa252306  regenerated parent full results.json (through Round 12)
82d7bd904ffc2dcacf55966bc071385946abf3bab8967aba4970732e7f9b9bc0  results-stop-b-summary.json
bf508a0997a9197012c67ba9b58de1c9afa242ddba8851e03a0ba15f1471e6f8  regenerated full Stop-B results.json
```

Issue #3948 comment `5231857267` の人間裁定により、旧repo fileのSHA
`cabfbcae…2306` は regenerated parent full JSON の期待値へ役割を変更した。この配置補正は
PRD上の進展ではない。Round 12までの2 SHAは final Stop-B artifactのimmutable parentとして
そのまま保持する。

Python standard libraryのみを用い、global / A-block rank計算は
`fractions.Fraction` 上で行う。乱数は使わない。parent / final result JSONは
UTF-8 / LF / `indent=2` / `sort_keys=True` / 末尾改行で固定する。`Obs_G` 自体は
UTF-8 / `ensure_ascii=True` / compact sorted JSON / 末尾改行なしで固定する。

## Round 13–15

| round | candidate / strict expansion | population | payload SHA-256 | 結果 |
| --- | --- | ---: | --- | --- |
| 13 | `R2-CSTAR-SUPPORT-ACTIVE-JOINT-COLLAPSE-v4`、cross-chart triangle support | 2,160 | `e15fc8dcb99ea7e8e17b1a52cc045379f9757c558a92f25e9d1bfc2bda5450e3` | candidate semantic changeとguard calibration fix、progress |
| 14 | v4、`NONFREE-MUTUAL-KILL-SPLIT` | 2,161 | `17c9907928a63cdf97e474e7f8813447601010ede07bbe7a43b525ef8551b450` | uniformかつcandidate falseのnecessity反例、progress |
| 15 | `R2-CSTAR-COORDINATE-DOUBLED-CYCLE-v5`、固定control 5件追加 | 2,166 | `21b59632026d5ec0f104700f26808a8455e2ca607802a108c6934f68e8911969` | `TERNARY-CYCLE-3` がuniformかつcandidate false、progress |

Round 13–15はいずれも新しいcanonical反例またはcandidate/calibration改訂を生じたため、
historical Stop C streakには数えない。Round 15の `TERNARY-CYCLE-6` は同じlocal形を持つが
nonuniformであり、この組を最終の二点分離に用いる。

## `G_local-v1` と停止 B

`G_local-v1` は、全support-active scopeと全非空 A-scopeについて、v5の全irreducible
terminalから次だけを読む有限 grammarである。

- retained chart / vertex / edge / actual face memberのradius-one typed incidence ball
- endpoint / ordered face slotと符号、critical / guard / port / bridge / self-loop /
  `FaceTwin` の閉じたflag集合
- scoped supportと `π` image、fine edge/faceの `None` / mapped status
- 4 packet kindのall-path union、各descriptor・root・A-recordのmultiplicity `clip2`
- `π` を保つtarget relabel orbit、whole C0/C5/C6、AごとのC1–C4とそのAND

候補predicate、global / A-block H¹、uniformity truth、Round 15 resultは `Obs_G` の入力にしない。
C3の登録済み局所fiber linear algebraだけを例外として保持する。source bundleは
`g_local_v1.py`、`r2_hunt.py`、`necessity_map.py` のnormalized source、checkerの登録値正規化
source、AST reachable closure、runtime binding、`Q = Fraction` とMatrix/Nerve依存を固定する。

pure manifestは Issue #3948 comment `5245279192` で事前登録され、SHA-256は
`32e5db03f8f66b091b2594954bd121e2c97c5bfb70fb049c50cd97a070b59969` である。
checkerは先に `TERNARY-CYCLE-3` と `TERNARY-CYCLE-6` の `Obs_G` をcomponent-wiseかつ
最終canonical bytesまで一致させ、その後にだけimmutable Round 15 ledgerから
uniformity `true / false` を読む。新しいv5 candidate classification、global / A-block H¹、
population queryは0であり、実行する構造評価はこの2件の `Obs_G` だけである。

任意の admissible condition family が `G_local-v1` で表現できるなら、ある関数 `f` により
`condition = f ∘ Obs_G` と因子化する。同じ `Obs_G` を持つ上記2件には同じ判定を返すが、
immutable ledger上の一様不変性は異なる。従って、一様不変性と同値なcondition familyは
この固定grammarでは表現できない。これは有限zero-resultではなく一般factorizationによる
停止 B の証明だが、結論は登録した `G_local-v1` に相対的であり、他のgrammarや非局所dataを
含むcharacterization全般の不可能性は主張しない。

## 最終判定

- R0(a)–(e): post-PUnit payload
  `37873129ed7d2d6fc0375b721e6e95bd213966836ed8b29484224fd88321d3cf` でpass
- R1: C0–C6 全て `not-necessary`
- R2: v3、v4、v5はいずれも必要条件ではなく、最終v5反例は `TERNARY-CYCLE-3`
- terminal: A=false、B=true、C=false
- Stop-B result: Issue #3948 comment `5245347326`
- G-107 sync: comments `5245356130` / `5245356137`
- state: `task_complete=false`（実装PRのmerge後にのみ更新）

停止 B は `G_local-v1` に相対的な非表現可能性である。任意graph size、任意非局所
certificate、無制限のface multiplicity / chart数 / support分配を読む別grammarまで排除しない。
