## 概要

<!-- 対応した Issue、目的、設計判断を短く書く。例: Closes #N -->

## 証明した定理

<!-- 追加・更新した theorem 名を書く。定理追加がない場合は「なし」のままにする。 -->

- なし

## 編集したドキュメント

<!-- README / docs / proof_obligations.md など、更新した文書を書く。文書更新がない場合は「なし」のままにする。 -->

- なし

## 実施したテスト

<!-- 実行したコマンドと結果を書く。未実施の場合は理由を書く。 -->

- [ ] `lake build`
- [ ] `git diff --check`
- [ ] hidden / bidirectional Unicode scan
- [ ] `axiom` / `admit` / `sorry` / `unsafe` scan

## チェックリスト

- [ ] 対象 Issue を `Closes #N` 形式で本文に記載した
- [ ] Lean status を `proved`, `defined only`, `future proof obligation`, `empirical hypothesis` のいずれかで明確にした
- [ ] `docs` の研究主張と Lean status が矛盾していない
- [ ] 明示的な相談なしに `axiom`, `admit`, `sorry`, `unsafe` を導入していない
- [ ] Architecture Signature を単一スコアではなく多軸診断として扱っている
