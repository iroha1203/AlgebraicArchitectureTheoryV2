# 研究の全体目標

この研究の大きなビジョンは、ソフトウェアアーキテクチャを
「静的な形」だけでなく、「変化し続ける対象」として扱うことである。

ここでいう AAT は **Algebraic Architecture Theory**、
SFT は **Software Field Theory** を指す。
AAT はアーキテクチャの局所代数を扱い、
SFT はその上でソフトウェア進化の場を扱う。

設計は一度決めて終わるものではない。
要求、仕様、Issue、PR、review、CI、運用、組織判断、AI agent の提案が、
コードベースの次の状態を絶えず作っている。
その流れの中で、何が保存され、何が破れ、どの未来へ進みやすくなったのかを
記述できる理論を作りたい。

AAT は、そのための局所的な代数を与える。
SFT は、その局所的な代数をソフトウェア進化の時間的・組織的な場へ置く。
tooling は、実際の artifact から観測できる範囲を取り出し、レビューや CI の判断に接続する。

```text
AAT asks what a change preserves or breaks.
SFT asks how changes shape future evolution.
Tooling asks what can be observed and governed in practice.
```

## AAT

AAT の目標は、アーキテクチャレビューを「感想」から「診断」へ近づけることである。

ここでいう診断とは、単一の品質スコアを出すことではない。
ある変更がどの architecture invariant を保存しているのか、
どの invariant を破っているのか、
破れがどの obstruction witness として現れるのか、
どの ArchitectureSignature axis に観測されるのかを分けて見ることである。

設計原則は、スローガンではなく operation として読む。
SOLID、Layered / Clean Architecture、Event Sourcing、Saga、Circuit Breaker、
Replicated Log などを万能な格言として並べるのではなく、
それぞれがどの invariant、operation、observation、theorem boundary に関係するのかを問う。

AAT が欲しい診断語彙は、たとえば次のような問いに答えるためのものである。

- この変更は、選択された architecture invariant を保存しているか。
- 保存していないなら、どの obstruction witness がそれを示しているか。
- その破れはどの ArchitectureSignature axis に現れるか。
- どの前提の下で lawful と言えるのか。
- どの観測が欠けているために non-conclusion として残すべきなのか。

この範囲では、Lean theorem、tool output、empirical hypothesis を混同しないことが重要である。
Lean theorem は経験的成功を保証しない。
tool output は Lean theorem ではない。
empirical correlation は architecture lawfulness ではない。
AAT は、何を証明でき、何を証明していないかを明確にするための理論でもある。

## SFT

SFT の目標は、ソフトウェア進化を計算可能な対象として扱うことである。

コードベースは、変更を受け取って終わる静的な構造ではない。
PRD、Spec、Issue、PR、review、CI、organization、AI、lifecycle decision は、
次に起こりやすい変更、見落とされやすい破れ、蓄積する制約、減衰される shortcut を作る。
SFT はこれを、field、force、trajectory、forecast、governance feedback として読む。

AAT が局所的に「この変更は何を保存し、何を破ったか」を問うなら、
SFT は時間の中で「この変更は future architecture をどう変えたか」を問う。

SFT が見たいのは、たとえば次のような対象である。

- PRD や Issue が、どの operation support と policy を誘導するか。
- Review、CI、policy が shortcut をどこで拒否し、どこで減衰し、どこで見逃すか。
- ある変更が future architecture を広げるのか、狭めるのか、危険な方向へ偏らせるのか。
- AI agent の proposal が、bounded field model と theorem boundary の中に収まっているか。
- feedback が field memory をどう更新し、次の変更分布をどう変えるか。

SFT は AAT を置き換えない。
AAT の theorem を経験的予測へ変換するものでもない。
むしろ、AAT の局所主張をどこまで forecast や governance の前提として使えるかを、
片方向の境界を保ったまま扱う。

## Tooling

tooling の目標は、AAT と SFT の語彙を実際の開発 artifact に接続することである。

ArchSig は、コードベース、PR、report、policy から観測できるものを取り出す。
signature axis、obstruction witness、theorem boundary status、forecast boundary を抽出し、
レビューや CI が扱える evidence に変換する。

ただし、tooling は理論そのものではない。
観測できたものだけを根拠にし、観測できていない軸を安全とみなさない。
measured zero と unmeasured を混同しない。
tool pass を Lean theorem として読まない。

最終的に作りたいのは、次のような開発支援である。

- PR がどの invariant を保存し、どの invariant を破っているかを示す。
- obstruction witness を、修復候補や設計判断に接続する。
- ArchitectureSignature を、多軸の診断結果として提示する。
- Lean theorem boundary、tooling evidence、empirical hypothesis を混同せずに並べる。
- PRD や Issue が誘導する future architecture の範囲を forecast する。
- AI-generated shortcut を、policy と theorem boundary の中で拒否・射影・減衰する。

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
