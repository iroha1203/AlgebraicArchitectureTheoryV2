# Tool Docs

`docs/tool/` は ArchMap / LawPolicy / law-equation-surface /
MeasurementProfile / ArchSig / ArchView / FieldSig の現行 tooling contract を扱う。
AAT の数学的主張は定義せず、各toolが supplied artifact から何を読み、何を生成するかを固定する。

## Product map

| Product | Responsibility | Primary input / output |
| --- | --- | --- |
| ArchMap | source-groundedなAtom evidence、Context、Cover、source refsを記録する | `archmap/v0.5.4` |
| LawPolicy | evaluator、law、basis、scope、severityを選択する | `law-policy/v0.5.4` |
| law-equation-surface | 選択可能なlaw universeとwitness variablesを宣言する | `law-equation-surface/v0.5.4` |
| MeasurementProfile | finite measurement regimeを選択する | `measurement-profile/v0.5.4` |
| ArchSig | 選択済みcontract内でmeasurement、comparison、gate decisionを計算する | measurement packet / summary / insight / compare / gate / viewer data |
| ArchView | ArchMapのAtom geometryを可視化し、ArchSig analysisを同じgeometry上へ重ね、sourceへ接続する | ArchMap + optional ArchSig run artifacts |
| FieldSig | ArchSig measurement packetとworkflow evidenceをSFTのevolution measurement inputとして読む | serialized ArchSig handoff |

## ArchView

ArchViewはArchSig reportの付属viewerではない。ArchMapだけでコードベース理解を成立させる
Atom-native Architecture Atlasであり、次の3責務を持つ。

1. ArchMapのAtom / Context / Coverからarchitecture structureを理解できる形にする。
2. ArchSigが供給したanalysisを同じgeometry上のoverlayとして表示する。
3. findingのsupport Atomからsupplied source refを解決し、file / symbol / lineへ到達させる。

ArchViewはstructural verdict、relation、source symbol、repair recommendationを生成しない。
direct evidence、boundary participant、candidate change point、validated repairを区別し、
描画要素と視覚チャネルの由来をsupplied artifactへ追跡可能にする。

現在checked inされている`tools/archview/archview.html`は再構築前のviewer-data readerである。
現行実装と再構築後の契約の差は[ArchView README](../../tools/archview/README.md)に記録する。

## Sources of truth

| Concern | Source of truth |
| --- | --- |
| Tooling編集規律と検証経路 | [guideline.md](guideline.md) |
| ArchMap authoring | [Atom handoff](atom_handoff.md)とschema / validator / fixture |
| LawPolicy authoring | [law_policy.md](law_policy.md) |
| ArchSig runtime | `tools/archsig/src/`、schema catalog、CLI docs、runtime tests |
| ArchSig artifact reading | [Artifacts and boundaries](../../tools/archsig/docs/artifacts-and-boundaries.md) |
| ArchView product・runtime・fidelity | [tools/archview/README.md](../../tools/archview/README.md)とUI / E2E tests |
| FieldSig runtime | `tools/fieldsig/README.md`、serialized schema、tests |

PRDや設計ノートを恒久仕様として参照しない。実装済みcontractは現行仕様、schema、source、test、fixtureへ置く。

## Entry points

- [ArchSig Analyze E2E Workflow](llm_native_e2e_workflow.md)
- [ArchSig measurement view model](archsig_view_model_contract.md)
- [ArchSig gate policy](archsig_gate_policy.md)
- [ArchSig compare report](archsig_compare.md)
- [ArchMapStore](archmap_store.md)
- [Golden corpus](golden_corpus.md)
- [AG measurement evidence](ag_measurement_evidence_contract.md)
- [ArchSig skills](../../tools/archsig/skills/)
- [ArchView](../../tools/archview/README.md)

過去の設計・退役contractは`docs/archive/`の履歴であり、現行source of truthとして扱わない。
