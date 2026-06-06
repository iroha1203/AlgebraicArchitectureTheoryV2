# Domain Review Profiles

`local-review` で使う分野別4観点。各分野は、リポジトリ固有ルール 2観点と一般的レビュー観点 2観点で構成する。

## AAT / Lean

1. Repo-specific: AAT / Lean / ArchSig boundary
   - AAT を source observation、measurement、tooling validation と混同していないか確認する。
   - Lean 形式化が、全 runtime、全 semantic universe、全未来予測のような無制限 claim を背負っていないか確認する。
   - ArchSig を Lean 証明器として扱う説明や、Rust と Lean の対応を要求する claim が混入していないか確認する。

2. Repo-specific: theorem status and ledger consistency
   - `proved`, `defined only`, `future proof obligation`, `empirical hypothesis` が docs、registry、Lean theorem index、proof obligations と一致するか確認する。
   - checkpoint PR や部分パッケージを、計画全体の完了として書いていないか確認する。
   - `docs/aat/mathematical_theory/` を明示依頼なしに変更していないか確認する。

3. General: Lean API and dependency quality
   - import、namespace、定義・定理の依存、命名、局所性が coherent か確認する。
   - 定義が過度に抽象化されていないか、既存 pattern と合っているか確認する。
   - theorem statement が使いやすい形で、不要に強い仮定や弱すぎる結論になっていないか確認する。

4. General: Lean verification and regression risk
   - `lake build` が必要か確認し、実行結果または未実行理由を報告する。
   - `axiom`, `admit`, `sorry`, `unsafe` の新規混入を確認する。
   - docs index、classification、proof obligation の更新漏れを確認する。

## Tooling / ArchSig / FieldSig

1. Repo-specific: evidence contract boundary
   - ArchSig が `ArchMap + LawPolicy + evidence contract` に相対化されているか確認する。
   - 選ばれた語彙内の肯定的 diagnostic conclusion を出しており、未観測領域を長い non-conclusion 一覧として主役化していないか確認する。
   - FieldSig が workflow evidence / governance input として読まれており、raw ArchMap を forecast truth として扱っていないか確認する。

2. Repo-specific: witness-driven semantics
   - witness、materialization、score computation が proxy 的 label 代入に戻っていないか確認する。
   - `SAFE_WITHIN_POLICY`, `NO_SELECTED_OBSTRUCTION`, `ACCEPTABLE_UNDER_EVIDENCE_CONTRACT` などの結論が、実際の evaluator と evidence path に支えられているか確認する。
   - output / viewer / release skill / docs の contract が同じ読み方をしているか確認する。

3. General: practical Rust CLI safety
   - 入力検証、path handling、出力先 handling、既存ファイル上書き、filesystem side effect が安全か確認する。
   - exit code、stderr / stdout、diagnostics、error message が automation と人間の両方に実用的か確認する。
   - panic、`unwrap` / `expect`、secret / private data leak、過剰な raw artifact 出力、巨大出力の扱いを確認する。

4. General: Rust code quality and test coverage
   - 責務分割、`Result` / error design、serde schema、versioned artifact、fixture ownership が coherent か確認する。
   - CLI tests、fixture coverage、golden output、schema compatibility、E2E workflow が変更範囲を覆うか確認する。
   - `cargo test --manifest-path tools/archsig/Cargo.toml` または `cargo test --manifest-path tools/fieldsig/Cargo.toml` の必要性と結果を確認する。

## Website / Manual

1. Repo-specific: public reading surface
   - Website が docs の複製ではなく、AAT / SFT / ArchSig を公開向けに読む web-native surface として機能しているか確認する。
   - brand / product / place / object に相当する主題が first viewport で明確か確認する。
   - docs source of truth と website navigation / sitemap の対応が破綻していないか確認する。

2. Repo-specific: claim boundary and public scrub
   - AAT / SFT / ArchSig の claim boundary を越える product claim、proof claim、forecast claim がないか確認する。
   - private name、private path、内部作業名、未公開メモが public surface に混入していないか確認する。
   - ArchSig / FieldSig の境界が、否定的 non-goal 羅列ではなく肯定的責務として書かれているか確認する。

3. General: static site UX and accessibility
   - route、asset path、navigation、link、responsive layout、text overflow、focus state、accessibility が崩れていないか確認する。
   - first viewport で次 section の hint が見えるか、カードの入れ子や過剰装飾がないか確認する。
   - manual / command reference は scanning、comparison、repeated use に向いた密度か確認する。

4. General: website verification
   - local static server preview、Playwright checks、title / link / asset / layout checks の必要性と結果を確認する。
   - `sitemap.xml`, `robots.txt`, directory route、relative path の破綻を確認する。
   - mobile / desktop viewport で text overlap や clipping がないか確認する。

## Docs / SFT / Research Notes

1. Repo-specific: protected source and domain boundary
   - `docs/aat/mathematical_theory/`, `docs/sft/software_field_theory.md`, `docs/sft/aat_interface.md` を明示依頼なしに変更していないか確認する。
   - AAT、SFT、Tooling、Website の責務と完了条件を混同していないか確認する。
   - Archive を現行 source of truth として扱っていないか確認する。

2. Repo-specific: completion and claim discipline
   - Issue、PRD、計画書、acceptance test が要求している concrete condition だけを完了判定しているか確認する。
   - source extraction / ArchMap observation / tooling validation の完全性を AAT の残タスクとして持ち込んでいないか確認する。
   - checkpoint success を plan completion と混同していないか確認する。

3. General: docs consistency and task traceability
   - Issue、PRD、acceptance criteria、実装状態、docs ledger の間に docs drift がないか確認する。
   - status table、リンク、参照先、用語、章構成が現在の実装やタスク状態と一致するか確認する。
   - readers が次に取るべき action を誤解しないか確認する。

4. General: publication quality and privacy
   - 読者向けの構成、根拠、用語、説明順が自然か確認する。
   - public-facing text では private name、private path、内部事情を scrub しているか確認する。
   - 主張が強すぎる場合は弱め、必要以上に defensive な非主張リストになっている場合は肯定的責務へ戻す。
