# G-104 necessity map checkpoint

> **これは off-loop 探索 artifact であり、GOAL 完了の証拠ではない。**

Issue #3948 の C0–C6 必要性地図と C* 候補探索を exact rational engine で再現する。
終端は PRD の停止条件 C であり、task完了ではない。Issue は open、PRD は保持する。

## 成果物

- `necessity_map.py`: R0 calibration、A-subnerve還元、R1必要性地図
- `r2_hunt.py`: 事前登録済みR2候補・二方向query・7 round
- `build_results.py`: canonical `results.json` generator
- `test_necessity_map.py` / `test_r2_hunt.py`: regression tests
- `hunt-report.md`: 一般手証明、verdict、round履歴、blocker、coverage
- `results.json`: deterministic canonical result

## 再現

```bash
cd research/experiments/g104-necessity-map
PYTHONDONTWRITEBYTECODE=1 python3 -m unittest test_necessity_map.py test_r2_hunt.py
PYTHONDONTWRITEBYTECODE=1 python3 build_results.py --output results.json
shasum -a 256 results.json
```

期待 SHA-256:

```text
d55b2f2650e6b799ba3a0bf00324ea274c9bcef6760838f51565606a8d6532dd
```

Python standard libraryのみを用い、rank計算は `fractions.Fraction` 上で行う。
乱数は使わない。JSONは UTF-8 / LF / `indent=2` / `sort_keys=True` / 末尾改行で固定する。

## 判定

- R0(a)–(e): pass
- R1: C0–C6 全て `not-necessary`
- R2: 独立監査による初回C判定撤回後、nonidentity face-chainを使うRound 6/7で
  同一 blockerの2 round連続 no-progress
- terminal: C(checkpoint)
- blocker: `PB-R2-NONFREE-GLOBAL-FACE-CHAIN`

有限zero-resultは証明ではなく、`CERTIFIED-v3` を必要十分条件とは主張しない。
