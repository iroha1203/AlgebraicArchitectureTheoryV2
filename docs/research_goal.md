# 研究の全体目標

この研究の大きなビジョンは、ソフトウェアアーキテクチャを
「静的な形」だけでなく、「変化し続ける対象」として扱うことである。

ソフトウェアは、静的な完成品ではなく、動的に進化する対象である。
要求、仕様、Issue、PR、review、CI、運用、開発組織の判断、AI agent の提案が、
コードベースの次の状態を絶えず作っている。
その流れの中で、何が保存され、何が破れ、どの未来へ進みやすくなったのかを
記述できる理論を作りたい。

この視点には、M. M. Lehman のソフトウェア進化研究という偉大な先駆がある。
Lehman は、ソフトウェアが運用環境の中で継続的に変化し続ける対象であることを示した。
この研究はその系譜を受け継ぎ、アーキテクチャ不変量、観測可能な signature、
governance、AI 駆動開発を含む形で、ソフトウェア進化を計算可能な対象として扱いたい。

AI 駆動開発は、この系譜に新しい圧力を加える。
AI agent は短時間に多くの proposal を生成し、進化の速度と分岐を増幅する。
同時に、既存のレビュー感覚や暗黙知をすり抜ける shortcut も作りやすい。
だからこそ、変更が何を保存し、どの未来を開き、どこで governance すべきかを
明示できる理論が必要になる。

この研究は、三つの層でこの問題に取り組む。
Algebraic Architecture Theory（AAT / 代数的アーキテクチャ論）は、
変更をアーキテクチャ不変量に対する局所的な operation として捉える。
Software Field Theory（SFT / ソフトウェアの場の理論）は、
その operation が、要求、開発組織、tooling、AI、feedback を含む場の中で
どの future architecture を開くのかを扱う。
tooling は、理論が要求する観測量を実 artifact から取り出し、
レビューや CI の判断へ接続する。

- AAT は、変更が何を保存し、何を破るかを問う。
- SFT は、変更が未来の進化をどう形づくるかを問う。
- Tooling は、実際に何を観測し、どう制御できるかを問う。

## AAT（Algebraic Architecture Theory / 代数的アーキテクチャ論）

AAT の目標は、アーキテクチャレビューを「感想」から「診断」へ近づけることである。

その中心にあるのが、アーキテクチャ不変量である。
不変量は、コードベースが変化しても保ちたい構造、境界、依存方向、契約、状態遷移の規律を表す。
レビューで本当に見たいのは、変更がその不変量を保存したのか、改善したのか、
あるいはどこで破ったのかである。

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

## SFT（Software Field Theory / ソフトウェアの場の理論）

SFT の目標は、ソフトウェア進化を計算可能な対象として扱うことである。

コードベースは、変更を受け取って終わる静的な構造ではない。
PRD、Spec、Issue、PR、review、CI、organization、AI、lifecycle decision は、
次に起こりやすい変更、見落とされやすい破れ、蓄積する制約、減衰される shortcut を作る。
SFT はこれを、field、force、trajectory、forecast、governance feedback として読む。

AAT が局所的に「この変更は何を保存し、何を破ったか」を問うなら、
SFT は時間の中で「この変更は future architecture をどう変えたか」を問う。
未来を一点で予言するのではなく、明示された horizon、operation support、policy、
observation boundary の下で到達可能な architecture future の範囲を扱う。

SFT の中核は、開発場のうち計算可能な断面を `SoftwareField` として取り出すことにある。
そこには、architecture projection、観測された signature、履歴、operation support、
policy、constraint、observation model、governance intervention が含まれる。
PRD、Spec、Issue、PR、AI proposal は、field を一意に次状態へ写す命令ではなく、
複数の candidate update や path class を生む artifact-mediated change として読む。

この見方によって、SFT は次のような計算対象を作る。

- `ForecastCone`: 選択された support と horizon の下で到達可能な field path の集合。
- `ConsequenceEnvelope`: forecast を、影響領域、signature axis、obstruction candidate、missing boundary、review / CI recommendation として読める形にまとめたもの。
- `GovernanceIntervention`: review、CI、type checker、policy、runtime guard が operation support、selection policy、observation、feedback update をどう変えるか。
- `FieldUpdate`: forecast と実際の PR / review / CI / runtime outcome の差分を field memory に戻す closed-loop feedback。

SFT が見たいのは、たとえば次のような対象である。

- PRD や Issue が、どの operation support と policy を誘導するか。
- Review、CI、policy が shortcut をどこで拒否し、どこで減衰し、どこで見逃すか。
- ある変更が future architecture を広げるのか、狭めるのか、危険な方向へ偏らせるのか。
- ConsequenceEnvelope が、どの architecture region と signature axis にリスクや機会を示すか。
- AI agent の proposal が、bounded field model と theorem boundary の中に収まっているか。
- feedback が field memory をどう更新し、次の変更分布をどう変えるか。

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

1. [AAT 数学理論](aat/mathematical_theory/README.md)
2. [AAT / SFT Interface](sft/aat_interface.md)
3. [ソフトウェアの場の理論](sft/software_field_theory.md)

Lean status、proof obligation、empirical hypothesis は
[証明義務と実証仮説](aat/proof_obligations.md) と
[Lean 定義・定理索引](aat/lean_theorem_index.md) に分離する。
AAT と SFT の境界、Lean theorem / tool output / empirical hypothesis の区別は
[AAT / SFT Interface](sft/aat_interface.md) と各索引文書で扱う。
tooling の詳細は [AAT Tooling Documentation](tool/README.md) に置く。
