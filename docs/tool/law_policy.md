# LawPolicy

LawPolicy is the selected evaluator contract for the current ArchSig
measurement workflow. It is intentionally separate from ArchMap evidence.

Current ArchSig `analyze` reads:

```text
ArchMap finite-poset-site evidence
  + LawPolicy evaluator selection
  + law-equation-surface declaration
  + MeasurementProfile selected regime
  -> archsig-measurement-packet/v0.5.4
```

LawPolicy JSON selects explicit law / lawPair entries, evaluator ids, basis refs, scope, severity, and a
`measurementProfileRef`. `lawSurfaceRef` is required and must match the supplied
`law-equation-surface/v0.5.4` id. The selected profiles are supplied as separate
`measurement-profile/v0.5.4` artifacts through repeated `--measurement-profile`
flags; each `policies[].profileRef` selects one supplied profile at execution
time. LawPolicy does not embed `measurementProfiles[]`.

`basisLedger[]` declares the basis ids used by `policies[].basis`. ArchSig checks
that policy basis refs resolve inside the ledger, but it does not check that
ledger paths exist. Each `policies[].law` or `policies[].lawPair[]` entry must
resolve to a law declared by the supplied law surface, and its
evaluator/condition/axis combination must match the registry mapping. The
`ag.law-conflict-tor` evaluator uses an explicit `policies[].lawPair` containing
exactly two distinct law ids; law-id naming conventions do not select Tor
participants.

MeasurementProfile owns the selected cover, coefficient, predicates, certificate
selector, verdict discipline, and `finiteBounds`. Witness variables belong to
the law surface and are projected into the execution plan only after validation.
`finiteBounds` may lower ArchSig registry hard caps; cap exceedance is a
validation failure. LawPolicy does not embed witness rules, distance profiles,
operation costs, coverage DSLs, repair recipes, or Lean proof assumptions.
Those calculation rules belong to ArchSig evaluator registry code and the
external MeasurementProfile.

`policy-bundle` can fix these three component artifacts with canonical JSON
SHA-256 fingerprints. `analyze --policy-bundle` resolves the components from
the bundle and records the same `componentFingerprints` in the measurement
packet and run manifest; individual component flags are exclusive with the
bundle flag.

## 第VIII部の定義との対応

現行のselector形は、第VIII部の `定義 2.1 AAT Measurement Profile` と
`定義 4.1 Finite Measurement Regime` を次のように実装へ対応させる。

| 第VIII部のデータ | 現行artifact / field | validator上の扱い |
| --- | --- | --- |
| selected site `X_M` | `MeasurementProfile.siteRef` | 非空文字列を要求する。参照先の内容はArchMap側で扱う。 |
| selected cover `U_M` | `MeasurementProfile.coverRef` | 非空文字列を要求し、ArchMapのsite/cover digestとともにrun契約へ入れる。 |
| coefficient / effective coefficient | `MeasurementProfile.coefficient`, `effCoeff` | 非空文字列を要求する。有限計算に使う実装はevaluator registryが所有する。 |
| selected witness variables / predicates | `law-equation-surface.witnessVariables[]`, `zeroPredicate`, `nonZeroPredicate` | witness変数は供給済みlaw surfaceから解決し、profileは計測手段と判定predicateだけを持つ。 |
| verdict discipline | `verdictDiscipline` | `five-valued-structural-verdict@1`を要求し、`measured_zero`等を他の語へ縮約しない。 |
| finite site / cover / effective computation | `finiteBounds` と `MeasurementProfile`全体 | 各boundを正数かつregistry hard cap以下に制限する。 |
| law universe と選択されたreading | `LawPolicy.policies[]` の `law` / `lawPair`, `evaluator`, `basis`, `scope`, `severity` | LawPolicyは選択だけを持ち、predicateや計算結果を入力に埋め込まない。Torのlaw pairは明示列挙する。 |

この対応表は、profileが指定した有限site・cover・係数計算の範囲でのみ
measurementを読むという契約を固定する。`basisLedger[].path`や`siteRef` /
`coverRef`の実体存在は、このvalidatorの宣言検査には含めない。

## `analyze --out-dir` 再利用契約

`--out-dir` は既存ディレクトリを再利用できる。入力JSONの読み込みとrun契約の
組み立てまで到達したrunでは、ArchSigは既知の生成artifactを先に削除し、その後に
validation reportまたはmeasurement artifactを書き出す。したがって、同じ出力先を
validation成功・失敗の間で再利用しても、既知の前run成功artifactを今回runの成果として
読み続けることはない。既知のartifact一覧外のファイルは削除しない。

入力ファイルのopen / JSON parse / schema decodeがpreflight到達前に失敗した場合は、
out-dirを変更せず、失敗manifestも出力しない。この場合、出力先に残る前run artifactは
今回runの成果ではなく、呼び出し側はrun manifestを確認できるまで読み込んではならない。

compareのR8契約では、contextsまたはcoversに差分がある場合、profile行をrun全体で
`other_transition`として扱う。差分のある行だけに限定する実装変更は行わず、
「差分があるprofile行」という要件は、この保守的なrun全体分類を許す注記として読む。

SAGA の H¹ comparison は LawPolicy の selector ではなく RepairPlan 側の finite data である。
`kind: "explicit"` は `h1ComparisonData.cochainMap` の次数0/1/2有限写像表と次数2の
`zeroImage` を入力し、ArchSig が差保存・零保存・微分可換性を再計算する。
`kind: "presentation-generated"` は semantic / equation presentation と restriction 行列を入力し、
independently authored な equation local-lift atlas も入力する。ArchSig は exactness、local `Φ`、
cochain map、semantic / equation residual、各商上の residual witness と source / target class を導出する。
適合条件を宣言するbooleanは採用しない。

R8 の class-zero reading は、`--refinement` で
`refinement-comparison/v0.5.4` を供給し、その coarse-to-fine と
`zeroTransport.checked`、および coarse/fine `complexFingerprint` と base/head の
`inputDigests.siteCoverDigest.sha256` の一致を検査した場合だけ追加される。
refactor transport は
`--refactor-morphism refactor-morphism/v0.5.4` と matching witness の両方を必要とする。

The current handoff to FieldSig is the serialized measurement packet. FieldSig
does not accept old raw analysis packets as the current boundary.

Historical LawPolicy and packet forms are archived under
`docs/archive/2026-07-05-archsig-v1-retirement/`.
