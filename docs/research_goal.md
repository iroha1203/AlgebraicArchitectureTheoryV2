# 研究の全体目標

AAT v2 が目指すのは、ソフトウェアアーキテクチャを「良い設計か悪い設計か」という
印象で語るのではなく、何が保存され、何が破れ、どの未来へ流れやすくなったのかを
診断できる言葉にすることである。

設計原則は、スローガンではなく操作である。
ある変更が境界を守るのか、依存を閉じ込めるのか、状態遷移を明確にするのか、
あるいは別の場所へ複雑さを押し出しているだけなのかを問う。
AAT はこの問いを、アーキテクチャ不変量、operation、obstruction witness、
ArchitectureSignature として定式化する。

SFT は、その局所的な診断を時間の中へ置く。
要求、仕様、Issue、PR、review、CI、組織判断、AI agent の提案は、
コードベースを一度だけ変えるのではない。次に選ばれやすい変更、見落とされやすい破れ、
レビューで減衰される shortcut、蓄積する field memory を作る。
SFT は、その流れを forecast、trajectory、governance feedback として扱う。

## 中心ビジョン

この研究の中心命題は次である。

```text
Design principles are operations on architecture invariants.
Architecture quality is observed as a multi-axis signature of invariant breakage.
Software evolution is a computable field-shaped process.
```

目標は、アーキテクチャレビューを「感想」から「診断」へ近づけることである。
ただし、診断とは単一スコアを出すことではない。
どの軸で破れているのか、どの前提の下で安全と言えるのか、
どの観測が欠けているために結論できないのかを分けて表示することである。

## 見たいもの

この研究では、次のような問いを一つの連続した対象として扱う。

- この変更は、選択された architecture invariant を保存しているか。
- 保存していないなら、どの obstruction witness がそれを示しているか。
- その破れはどの ArchitectureSignature axis に現れるか。
- その変更は future architecture を広げるのか、狭めるのか、危険な方向へ偏らせるのか。
- Review、CI、policy は shortcut をどこで拒否し、どこで減衰し、どこで見逃すのか。
- AI agent の proposal は、bounded theorem boundary と governance boundary の中に収まるのか。

ここで重要なのは、証明、測定、推定、実証仮説を混同しないことである。
Lean theorem は経験的成功を保証しない。
tool output は Lean theorem ではない。
empirical correlation は architecture lawfulness ではない。
この分離を保ったまま、それでも実際の開発判断に届く診断語彙を作る。

## AAT と SFT

AAT は、ソフトウェアアーキテクチャの局所代数を与える。
component、relation、operation、invariant、witness、signature を使い、
ある変更がどの前提の下で lawful か、どの obstruction によって split できないかを扱う。

SFT は、AAT の局所主張をソフトウェア進化の場へ写す。
PRD、Spec、Issue、PR、review、CI、organization、AI、lifecycle decision を
field、force、trajectory、control として読み、到達可能な architecture future を扱う。

ArchSig と tooling は、その間の観測層である。
実 artifact から signature axis、witness、theorem boundary status、forecast boundary を抽出する。
ただし、観測できたものだけを根拠にし、観測できていない軸を安全とみなさない。

## 何を作るか

この研究が最終的に作りたいものは、次のようなレビューと設計支援である。

- PR がどの invariant を保存し、どの invariant を破っているかを示す。
- obstruction witness を、修復候補や設計判断に接続する。
- ArchitectureSignature を、多軸の診断結果として提示する。
- Lean theorem boundary、tooling evidence、empirical hypothesis を同じ画面で混同せずに扱う。
- PRD や Issue が誘導する future architecture の範囲を forecast する。
- AI-generated shortcut を、policy と theorem boundary の中で拒否・射影・減衰する。

この方向では、SOLID、Layered / Clean Architecture、Event Sourcing、Saga、
Circuit Breaker、Replicated Log などを万能な設計格言として並べない。
それぞれを、どの層のどの invariant や operation に関係するのかで読む。

## 詳細文書

この文書はビジョンを述べる入口であり、詳細な定義や台帳は持たない。
第一級本文は次の 3 文書に固定する。

1. [AAT 数学理論](aat/mathematical_theory.md)
2. [AAT / SFT Interface](sft/aat_interface.md)
3. [ソフトウェアの場の理論](sft/software_field_theory.md)

Lean status、proof obligation、empirical hypothesis は
[証明義務と実証仮説](aat/proof_obligations.md) と
[Lean 定義・定理索引](aat/lean_theorem_index.md) に分離する。
tooling の詳細は [AAT Tooling Documentation](tool/README.md) に置く。

読む順序は、AAT の局所代数を理解してから、AAT / SFT の境界を確認し、
最後に SFT の software evolution model へ進むのがよい。
