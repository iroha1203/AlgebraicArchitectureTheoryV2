# Research 成果索引(research evidence index)

Research 側(`research/lean/ResearchLean/`)で受理された成果の1行台帳。
本体実装・レビューが「Research 側にすでに到達点があるか」を、巨大 Lean
ファイルの実読なしに grep で検索するための索引であり、Research 下限原則
(`docs/aat/guideline.md` の Lean status discipline)の検索基盤である。

## 記載契約

- 1行 = 1受理成果。受理時に追記し、後から書き換えるのは
  `移植状況` 列と `本体対応` 列のみ(受理内容の遡及修正はしない。
  誤記の訂正は可)。
- `research-loop` / `target-theorem-loop` は、成果の受理
  (accepted / target-theorem-proved)時にこの索引への登録を**出力義務**
  として負う(各 SKILL の ledger 手順を参照)。
- 列の意味:
  - `theorem`: Research 側の宣言名(コードブロック表記)
  - `file`: `research/lean/ResearchLean/` 配下のファイル
  - `本文ラベル`: 対応する数学本文の部・定理番号(無ければ `-`)
  - `conjuncts 要旨`: 結論一覧の要約。移植時の下限照合で結論の
    数え漏れが出ない粒度で書く
  - `未放電仮定`: 受理時点の material premise 三分類
    (`docs/aat/lean_quality_standard.md` §1.1)で未放電に分類された
    仮定の一覧。無ければ `なし`。受理済みであることと未放電仮定が
    無いことは別であり、蒸留・下限照合時はこの欄を必ず読む
  - `受理`: GOAL / cycle / PR などの受理点
  - `移植状況`: `ported` / `unported` / `not-for-porting`。
    列値 `unported` は guideline の status `unported (Research-proved)` の
    略記であり同義。`not-for-porting` は scaffolding・探索残骸など
    本体化を意図しないもので、理由を `本体対応` に書く。
    **`unported` → `not-for-porting` への書き換えは下限原則の解除を
    意味するため、ユーザー承認またはレビュー承認済みの根拠を
    `本体対応` に必ず残す**(乱用すると Research 下限原則が空洞化する)
  - `本体対応`: `ported` なら本体側の宣言名、`unported` なら追跡 Issue、
    `not-for-porting` なら理由
- 検索の作法(実装・レビュー側): まずこの索引を `rg` で検索し、
  該当が無ければ `research/lean/ResearchLean/` を直接 `rg` する。索引に無いことは
  「Research に無い」ことを意味しない。

## 索引

| theorem | file | 本文ラベル | conjuncts 要旨 | 未放電仮定 | 受理 | 移植状況 | 本体対応 |
| --- | --- | --- | --- | --- | --- | --- | --- |
| `ShortExactLiftProblem.connectingClass_zero_iff_exists_globalLift` | `AG/QualitySurface/LawGeneratedConormalDescent.lean` | - | selected sieveから二重・三重refinement complexとlocal-lift cocycleを構成し、choice-independentなconnecting classの零とactual global liftの存在を同値化。非空lift fiberにはkernel-section `AddTorsor`を構成 | law-generated `N/E/Q`、kernel comparison、objectwise exactness、cover provenance、`E/Q` sheaf conditions | G-07 Cycle 1 / Issue #3246 | unported | Issue #3246 |

<!--
既存の受理成果の遡及登録(初期整備)は別 PRD で実施する
(docs/note/codex_skill_audit_redesign_note.md B-3、2026-07-07 ユーザー決定)。
初期整備までは空欄の索引が正であり、空欄は「Research に成果が無い」ことを
意味しない。
-->
