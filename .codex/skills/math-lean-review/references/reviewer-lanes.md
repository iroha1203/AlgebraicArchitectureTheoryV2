# Math Lean Review lanes

数学査読 A/B と Lean 査読 A/B の4本を、同じ合格基準を持つ重複独立査読として
実行する。A/Bを主査と補助に分けない。他laneの出力や親の期待を渡さない。

## Lane定義

### 数学査読 A / B

- 本文 / GOAL のtheorem claimと必要仮定を全体から読む。
- 主張の強さ、量化、係数、site / topology、反例方向、欠けた仮定、
  claim scope外の要求混入を独立に判定する。
- 固定statementとの弱化、未放電仮定、定義不足を探す。

### Lean査読 A / B

- Lean declaration、statement、定義、型、universe、instance、仮定、proof term、
  依存補題、`#print axioms`、placeholder scan、focused buildを追う。
- 数学claimの弱化、結論相当のtheorem argument / typeclass / certificate field /
  structure fieldへの移動、未放電obligationを探す。
- material premiseのcertificate provenance、proof-use、field-contentを追う。
  explicit certificateを放電済みと即断しない。

## 追加出力

共有review protocolの出力に加え、各laneは次を返す。

1. 対象数学claimと候補Lean declaration。
2. Claim mapping。
3. Material premise分類と放電状況。
4. Certificate provenance / proof-use / field-content findings。
5. Anti-weakening verdict。
6. Axiom / dependency checksと未実行項目。

## 親の統合出力

1. 判定:
   `Reject / 証明として不十分` / `Major revisions` / `Minor issues` /
   `No major findings` / `Blocked / cannot determine`。
2. Findings。数学claim、Lean declaration、根拠、影響、必要な修正方針を含める。
3. Claim mapping。
4. Material premise audit。
5. Certificate provenance audit。
6. Proof-use / field-content audit。
7. Premise discharge status。
8. Anti-weakening verdict。
9. Undischarged obligations。
10. Axiom / dependency audit。
11. 査読別の結論と不一致。
12. 実行した検証。
13. Coverage limitsと残リスク。

`No major findings`はrare passとする。中心claimに関わる未確認、弱化、未放電、
台帳不一致が残る場合、またはcertificate provenance / proof-use /
field-content auditが閉じていない場合は使わない。
