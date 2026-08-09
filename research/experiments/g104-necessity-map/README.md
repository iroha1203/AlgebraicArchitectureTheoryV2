# G-104 necessity map checkpoint

> **これは off-loop 探索 artifact であり、GOAL 完了の証拠ではない。**

Issue #3948 の C0–C6 必要性地図と C* 候補探索を exact rational engine で再現する。
終端は PRD の停止条件 C であり、task完了ではない。Issue は open、PRD は保持する。

## 成果物

- `necessity_map.py`: R0 calibration、A-subnerve還元、R1必要性地図
- `r2_hunt.py`: 事前登録済みR2候補・二方向query・12 round
- `build_results.py`: canonical full `results.json` / slim summary generator
- `test_necessity_map.py` / `test_r2_hunt.py` / `test_build_results.py`: regression tests
- `hunt-report.md`: 一般手証明、verdict、round履歴、blocker、coverage
- `results-summary.json`: commit対象の deterministic slim audit summary

フル `results.json` はrepoには置かず、canonical generatorから得る導出物とする。

## 再現

```bash
cd research/experiments/g104-necessity-map
PYTHONDONTWRITEBYTECODE=1 python3 -m unittest test_necessity_map.py test_r2_hunt.py test_build_results.py
PYTHONDONTWRITEBYTECODE=1 python3 build_results.py \
  --output /tmp/g104-necessity-map-results.json \
  --summary-output results-summary.json
shasum -a 256 results-summary.json /tmp/g104-necessity-map-results.json
```

期待 SHA-256(summary / regenerated full):

```text
afa334056b52938044c0acad9b693a0c437300382b855f32450af5750020caa5  results-summary.json
cabfbcae7075280a6d10de3c819c25ca2396a21deaed2099bafdd71daa252306  regenerated full results.json
```

Issue #3948 comment `5231857267` の人間裁定により、旧repo fileのSHA
`cabfbcae…2306` は regenerated full JSON の期待値へ役割を変更した。この配置補正は
PRD上の進展ではなく、Stop C streakを変更しない。

統合回帰: `47 tests / 633.323s / OK`。査読後のprojection強化に対するfocused再検証:
`3 tests / 316.488s / OK`。

Python standard libraryのみを用い、rank計算は `fractions.Fraction` 上で行う。
乱数は使わない。JSONは UTF-8 / LF / `indent=2` / `sort_keys=True` / 末尾改行で固定する。

## 判定

- R0(a)–(e): 独立global/block経路と現行canonical firing oracleの完全固定dataでpass。
  post-PUnit payloadは
  `37873129ed7d2d6fc0375b721e6e95bd213966836ed8b29484224fd88321d3cf`、
  最後の進展はIssue #3948 comment `5231149474`
- R1: C0–C6 全て `not-necessary`
- R2: `Law=PUnit` provenance calibrationを進展としてstreakをresetしたため、旧Round 9/10
  Stop Cは撤回してhistoricalに移した。post-PUnitのRound 11（Issue #3948
  prereg `5231154236` / result `5231263023`）とRound 12（prereg `5231270132` /
  result `5231343121`）が、同じ blockerで2 round連続のvalid no-progressとなった
- terminal: A=false、B=false、C=true（checkpoint）
- blocker: `PB-R2-NONFREE-GLOBAL-FACE-CHAIN`
- state: task=false、Issue #3948 open、PRD retained、PR draft

有限1,918 semantic caseのzero-resultは証明ではなく、`CERTIFIED-v3` を必要十分条件とは
主張しない。coverageはlift数6以下の固定fixtureまでで、chart間のnonloop edge / face、
任意graph size・certificate coloring・face multiplicity・chart数・compatible support分配は
未被覆である。
