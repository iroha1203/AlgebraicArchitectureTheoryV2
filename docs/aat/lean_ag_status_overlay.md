# AG Lean status overlay

この台帳は、Lean declaration や構成の存在を theorem-grade completion evidence に
数えるかどうかについて、現行の例外・降格判定だけを保持する。

- declaration と通常の status は [AG Lean API 索引](lean_theorem_index_ag_aat.md)
- proof obligation と旧acceptance criteria再判定は
  [AG Lean proof obligation台帳](proof_obligations_ag_aat.md)

を参照する。本台帳は監査の実行履歴を複製せず、現在も完了判定を変える行だけを
正本として持つ。

## Status vocabulary

| Tag | 読み |
| --- | --- |
| `proved` | 実証明。結論そのものを仮定packageのfieldから取り出していないもの。 |
| `packaged (assumption-relative)` | 仮定record、certificate、selected packageのfield合成から得る帰結。無条件`proved`には数えない。 |
| `statement-only` | 型・candidate surfaceはあるが、証明済みtheoremとして数えないもの。 |

`defined only`、future proof obligation、empirical hypothesis、explicit non-goalは
この三分化の対象外である。

## Completion-evidence exceptions

| Item | 現行判定 | 理由 |
| --- | --- | --- |
| I-4 | `packaged (assumption-relative)` | `LawUniverse.coverageAssumptions` / `exactnessAssumptions` はselected assumption slotであり、concrete three-reading theoremの完了根拠には数えない。 |
| II-2 | `未達・降格記録` | quotient finite-meet poset constructionは存在するが、旧命題4.2のempty-theorem / over-promotion懸念を閉じるtheorem-grade evidenceではない。 |
| IV-8 | `defined only` / `packaged (assumption-relative)` | Type値obstruction sheaf / module sheafはcarrierまたは明示仮定相対のsurfaceであり、無条件なadditive/module soundnessとして数えない。 |
| V.R11 | `未達・降格記録` | repair synthesis fixtureには `emitsOnlySoundStepsOrNoSolutionCertificate := True` / `_holds := trivial` が残るため、定理13.4のtheorem-grade sound-step emission evidenceに数えない。 |
| VI-5 | `packaged (assumption-relative)` | decomposition gerbe / non-abelian soundnessはsupplied dataに相対化され、banded abelian bridgeもconditionalである。 |
| VII-1 | `未達・降格記録` | `AATSynthesisPackage`はfinite singleton/PUnit-style fixtureでのみ発火し、`costToDistanceValue _ := measured 0`も残るためtheorem-grade synthesis evidenceに数えない。 |
| VII-3 / VII-4 / VII-6 | `部分昇格` | coboundary invariance、adequacy、actual GLB、length-one edge-fiberは実装済みだが、一般length-n cardinality theoremは未証明であり、束ねた全体を完了扱いしない。 |
| IX-3 legacy firing | `完了根拠ではない` | 既存cohomology-level inverse firingのPUnit singleton係数wrapperはnondegenerate completion evidenceに数えない。現行の肯定的根拠はZMod 2 product-incidence route側に置く。 |

新しい降格・条件付き判定を追加するときは、対象宣言、完了要求、完了根拠に
数えない理由、監査証拠を1行で追加する。実装済み項目の一般的な一覧やcycle履歴は
この台帳へ複製しない。
