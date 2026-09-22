# Rising Sea 付録A ResearchLean 実行検証記録

検証日：2026-09-22

対象：[付録A Lean形式化との対応](ja/15-appendix-a-lean-correspondence.md) に記載された AAT 側の `ResearchLean` 宣言。Formal 側は CI で確認済みという依頼に従い、この記録の対象外とした。

## 判定

付録Aから抽出した `research/lean/ResearchLean/` の一意なリンク先は **173件**。依存関係を含む単一ターゲットの `lake build` を順に実行し、全173件に対応する `.olean` が生成され、**173/173件が Lean の構文・型検査・elaboration を通過**した。

実際の Lean elaboration error、依存 artifact 不足による未完了、ビルド停止は確認されなかった。したがって、今回の限定された判定（「Leanとして動くか」）は **ResearchLean 173/173 成功**である。

これは宣言が本文の数学的主張と同じ強さであること、本文との対応が成立すること、また依存閉包全体の公理・健全性を判定する記録ではない。

## 検証方法

1. 付録Aの GitHub 固定リンクから `research/lean/ResearchLean/` のパスを抽出し、重複を除いた。
2. 各パスを Lean モジュール名 `ResearchLean.AG....` に変換した。
3. Research の全面ビルドは行わず、依存順に単一ターゲットの `lake build` を実行した。重いターゲットは終了コードが得られるまで待機した。
4. 最終状態で各リンク先に対応する `research/lean/.lake/build/lib/lean/ResearchLean/.../*.olean` の存在を確認した。

基本形は次のとおり。

```sh
cd research/lean
lake build ResearchLean.AG.<module>
```

ソース変更は行っていない。

## グループ別結果

| ResearchLean グループ | 成功 / 対象 |
| --- | ---: |
| AtomFoundation | 5 / 5 |
| CanonicalResolution | 6 / 6 |
| ComparisonInformationLoss | 5 / 5 |
| CrossStageCoherence | 7 / 7 |
| DiagnosticConservativity | 5 / 5 |
| DoctrineFiberProduct | 32 / 32 |
| FiniteDecoderRepresentability | 11 / 11 |
| FullGeometryNormalization | 8 / 8 |
| GeometryTransport | 5 / 5 |
| LocalSemanticReconstruction | 14 / 14 |
| ObstructionDiagnosticBridge | 18 / 18 |
| RealizationComparisonIdempotents | 7 / 7 |
| RealizationReconstruction | 28 / 28 |
| ResolutionInvariance | 8 / 8 |
| StructuralCover | 2 / 2 |
| TransportCoherence | 3 / 3 |
| TwoPhase | 3 / 3 |
| UniformInvariance | 6 / 6 |
| **合計** | **173 / 173** |

## 重いターゲット

重い依存グラフも途中で未確認扱いにせず、終了コードを取得してから判定した。

- `ResearchLean.AG.ComparisonInformationLoss.PresentationTransport`：4188ジョブ、ターゲット完了まで688秒。
- `ResearchLean.AG.FullGeometryNormalization.ExactBarBetaFiniteWitness`：依存の `ExactDerivedBarAlphaTriangle` が356秒。最終ターゲットは成功。
- `ResearchLean.AG.LocalSemanticReconstruction.IndependentAATPrimitiveReconstruction`：4593ジョブ。最終ターゲットは成功。
- `ResearchLean.AG.ComparisonInformationLoss.EndpointKernelClassification`：4174ジョブ。最終ターゲットは成功。

途中で表示された tactic 提案等の warning はあり得たが、失敗終了や elaboration error はなかった。

## Manifest の登録状態

付録Aの173パスのうち168パスは `research/lean/research-modules.txt` に登録されている。次の5パスは manifest には未登録だが、直接 `lake build` を実行して成功した。

- `ResearchLean.AG.DoctrineFiberProduct.IndexedBaseChangeTwoCellNoGo`
- `ResearchLean.AG.DoctrineFiberProduct.LaxDiagnosticProjectorModificationBlocker`
- `ResearchLean.AG.DoctrineFiberProduct.UpperGeometryCompatibleSourcePresentationNaturalityF0`
- `ResearchLean.AG.DoctrineFiberProduct.UpperGeometryCompatibleSourcePresentationNaturalityF3`
- `ResearchLean.AG.ObstructionDiagnosticBridge.ExistingObstructionBridge`

したがって、これは Lean の実行失敗ではなく、登録型の focused checker をこれら5件へ適用できないという manifest 上の差分である。manifest自体は今回変更していない。

## 固定版と main の確認

- 付録Aの固定参照：`719f81f47d410701fd82c2bc88613cc140c59377`
- 検証 worktree の `HEAD`：`49f9ffabdbfc383db767c9fa01561ac6a9ff295f`（PR #4849 merge）
- 確認時の `origin/main`：`31f316429c3f041690b06d9511ea60b9ac2c1e4f`（PR #4850 merge）
- 固定参照と `HEAD` の `Formal/`・`research/lean/` に差分なし。
- `HEAD` と `origin/main` の `Formal/`・`research/lean/`・付録A本文にも差分なし。

従って、今回の ResearchLean 判定は付録Aの固定リンクが指す Lean source と、確認時の main 系列で一致している。
