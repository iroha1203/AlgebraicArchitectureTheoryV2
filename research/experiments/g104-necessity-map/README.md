# G-104 necessity map final Stop-B terminal

> **これは off-loop 探索 artifact であり、GOAL 完了の証拠ではない。**
> `G_local-v1` 相対の数学的terminal Bを記録する。

Issue #3948 の C0–C6 必要性地図、C* 候補探索、有限 local grammar に対する
非表現可能性証明を exact rational engine で再現する。最終終端は停止条件 B である。
成果物はこの数学的終端だけを固定し、Issue / PR の可変な lifecycle state は含めない。

## 成果物

- `necessity_map.py`: R0 calibration、A-subnerve還元、R1必要性地図
- `r2_hunt.py`: 事前登録済みR2候補、二方向query、Round 1–15
- `g_local_v1.py`: H¹・uniformity labelを読まない有限観測 grammar `G_local-v1` と `Obs_G`
- `g_local_v1_stop_b.py`: permanent structural contract、immutable Round 15 ledger、Stop-B checker
- `build_results.py`: Round 12までの lifecycle-free mathematical parent generator
- `build_stop_b_results.py`: Stop-B canonical full / slim summary generator
- `test_necessity_map.py` / `test_r2_hunt.py` / `test_r2_v4.py`: historical engine regression
- `test_g_local_v1_prereg.py`: grammar、source bundle、ledger分離、checker contract
- `test_build_results.py` / `test_build_stop_b_results.py`: parent / Stop-B artifact regression
- `hunt-report.md`: 一般手証明、round履歴、`G_local-v1` 二点分離、最終停止判定
- `results-summary.json`: Round 12までの committed current parent summary
- `results-stop-b-summary.json`: final Stop-B committed slim audit summary

canonical full JSONはrepoには置かず、各generatorから得る導出物とする。

## 再現

repository rootをworking directoryとする。

```bash
PYTHONDONTWRITEBYTECODE=1 python3 -m unittest discover \
  -s research/experiments/g104-necessity-map
PYTHONDONTWRITEBYTECODE=1 python3 \
  research/experiments/g104-necessity-map/build_results.py \
  --output /tmp/g104-necessity-map-results-through-round12.json \
  --summary-output research/experiments/g104-necessity-map/results-summary.json
PYTHONDONTWRITEBYTECODE=1 python3 \
  research/experiments/g104-necessity-map/build_stop_b_results.py \
  --output /tmp/g104-necessity-map-stop-b-results.json \
  --summary-output research/experiments/g104-necessity-map/results-stop-b-summary.json
shasum -a 256 \
  research/experiments/g104-necessity-map/results-summary.json \
  /tmp/g104-necessity-map-results-through-round12.json \
  research/experiments/g104-necessity-map/results-stop-b-summary.json \
  /tmp/g104-necessity-map-stop-b-results.json
```

期待 SHA-256（current artifacts再生成・外部登録後に固定する）:

```text
556c7279626a4395bc2446bc2f2a1f9af725c24e3ce6aacddfe59cc8ab11ee3e  results-summary.json (95635 bytes; current parent through Round 12)
7d01eb3a8fb22334644f6a8c6cef1f7cde235e9f17e4607da85969a17109eede  regenerated current parent full results.json (3446023 bytes)
77d34471daae5743ad095ad1a90845aee758ced3075b00afbf021c0f08be1cd3  results-stop-b-summary.json (15908 bytes)
e889f527efbc2bf1b495d047b08dd156b6dd9fe8bab92d38dc4ff45f183e204b  regenerated full Stop-B results.json (4851553 bytes)
```

最終 full regressionは `125 tests / 1506.494s / OK`。Stop-B full / summaryは別パス再生成で
byte-for-byte一致した。

Round 13が実際にadmitした旧parent full
`cabfbcae7075280a6d10de3c819c25ca2396a21deaed2099bafdd71daa252306` と旧summary
`afa334056b52938044c0acad9b693a0c437300382b855f32450af5750020caa5` は、Git commit
`ded12203d2f95fa8f83aadfd3a1e453f6e7efa06` のopaque historical provenanceとしてだけ保持する。
current parentは同じRound 12数学payloadをlifecycle-free schemaで再生成し、旧bytesの再構築を
主張しない。このmigrationは探索上の進展ではない。

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

current external registration ledgerはIssue comment `5248074852`
(`2026-08-11T01:43:10Z`, created=updated)で事前登録された。これは
pure contractのSHA/bytes、sanitized Round-12 parent full/summaryのSHA/bytes、Round-12 payload、
Issue comment/timeを一つのrecordで結ぶ。Issue provenanceはbuilderだけが保持し、parent JSONや
checker sourceへ埋め込まない。
pre-registration contract candidateは
`5a14faf44049b8906200d5dbd052bc9fd5669ff84dfb6452e6137e98dfbd51c8` / `314114` bytesである。
このcontractの `immutable_round15_label_ledger.sha256` はledger自体のcanonical SHA、
`round15_immutable_ledger_provenance.sha256` はwitness projectionを認証したRound 15
registered manifestのSHAであり、ledger SHAではない。
固定順序は `parent full生成 → parent full hash pin → parent summary calibration → pure contract
candidate生成 → Issue external registration → contract SHAだけをsourceへ固定 → checker実行 →
checker regression同期 → builder admission/projection` である。checker regressionは
Issue comment `5248116625` (`2026-08-11T01:51:03Z`, created=updated)に別domainとして
登録した。current checkerは compact SHA-256
`645d4ca27215bcd6687734bf2abff87a3a7bb0e778134c051b546937e7ebfde9` / `56881` bytesである。

旧permanent contract `955b75d7…a7531af` / `314821` bytes / comment `5246699114` と、
旧current checker `834d9754…9ebca` / `56940` bytes / regression comment `5246749681` は、
Git commit `c3a6bada111978a08d82bff5fceffbbea2aa0f51` の、旧 `32e5…/0d644…`
execution bridgeとは別のopaque historical migration recordとして保持する。いずれもcurrent
sourceからの再構築を主張しない。
checkerは先に `TERNARY-CYCLE-3` と `TERNARY-CYCLE-6` の `Obs_G` をcomponent-wiseかつ
最終canonical bytesまで一致させる。続いて両serializationがhistorical common `Obs_G` の
SHA-256 / bytesへexact一致するbridgeを検査し、その後にだけimmutable Round 15 ledgerから
uniformity `true / false` を読む。新しいv5 candidate classification、global / A-block H¹、
population queryは0であり、実行する構造評価はこの2件の `Obs_G` だけである。
artifactの `verification_invariants` は、このcommon observation bridgeとRound 15 label分離の
実一致、3種のqueryのexact zero、旧manifest/checkerをcurrent sourceから再構築しないことだけを
固定し、全入力に対する観測意味の不変性は主張しない。

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
- current checker: `645d4ca27215bcd6687734bf2abff87a3a7bb0e778134c051b546937e7ebfde9`
  / `56881` bytes; regression comment `5248116625`
- common `Obs_G`: compact canonical bytes `53279`、SHA-256
  `742e6395bb21221fcac070975cbe9505d49d0c75f826289984288776836aa7dc`

停止 B は `G_local-v1` に相対的な非表現可能性である。任意graph size、任意非局所
certificate、無制限のface multiplicity / chart数 / support分配を読む別grammarまで排除しない。
