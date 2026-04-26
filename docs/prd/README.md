# PRD

このディレクトリには、実装前または検討中の product requirement document を置く。

PRD は、研究主張そのものではなく、CLI、dataset、CI、AI reviewer などの tooling に落とすための要求仕様として扱う。Lean status は PRD 内で確定させず、実装・証明・実証仮説に反映する段階で `docs/proof_obligations.md` や個別 design document に移す。

## 現在のPRD

- [Algebraic Signature Extension for sig0-extractor](<Algebraic Signature Extension for sig0-extractor.md>):
  依存グラフベースの計測に、設計法則・状態遷移・履歴再構成性・表現変換の別軸を追加する全体構想。
- [Algebraic Law Signature MVP for sig0-extractor](<Algebraic Law Signature MVP for sig0-extractor.md>):
  `architecture-laws/v0` と `law-evidence/v0` から `algebraic-signature-v0` を生成し、`algebraic-validate` で検査する Phase 0 の実装仕様。
