# GOALS — 研究目標

GOAL とは、研究で成し遂げたい能力や到達像である。証明したい定理の一覧ではない。定義と改訂は人間の判断による。`$research-loop` は、active な GOAL に対して候補を探索し、四審判、Lean 検証または証拠固定、SCORE 監査、PR レビューを通して、GOAL の能力がどれだけ増えたかを積み上げる。

ここは GOAL を状態ごとに並べた参照文書である。ただし状態の正本は GitHub の tracking Issue にあり、この文書はその写しにすぎない。active な GOAL は、サイクルの先頭で `$research-loop` が「goal 欠陥」を検査する。必要な項目は末尾の「GOAL カードの型」にまとめた。カードの中に現れる NT 番号や大定理 G1-G8 は、[docs/note の AG 版考察ノート](../docs/note/aat_ag_porting_bridges_grand_theorems.md) で定義している。

## active

### G-aat-quality-surface-01 — atom-supported quality geometry によるアーキテクチャ品質の幾何化

- `id`: `G-aat-quality-surface-01`
- `status`: `active`
- `source note`: [docs/note/aat_quality_surface.md](../docs/note/aat_quality_surface.md)
- `research aim`: AAT 代数幾何版に atom-supported quality geometry を導入する。固定した architecture `A` に対し、profile 圏 `Prof_A`、profile ごとの certificate space `C_A(p)`、profile change に沿う comparison map `Phi_u` を置き、その Grothendieck construction を品質の数学的本体として扱う。Quality Surface はその二次元 profile slice として定義し、アーキテクチャ品質を単一スカラーではなく、multi-axis quality signature、obstruction certificate、minimal atom support family、repair direction、verdict、trace information を持つ certificate geometry として語れるようにする。
- `core tension`: intrinsic obstruction、profile-dependent observation、repair reachability、reading projection artifact を、一つの追跡可能な品質 certificate geometry として統合できるか。profile change によって certificate transport が保存される、ridge / discriminant が現れる、profile curvature が生じる、reading fold で異なる certificate が同じ数値に潰れる、といった現象を区別して扱えるか。さらに、各 certificate が supporting atom family を持ち、利用可能な ArchMap source reference へ trace できるか。
- `rival`: primary rival は ADL / architecture description language 解析器である。ADL は、architecture の構成要素、接続、制約、view、declared architecture との一致、設計意図の記述、解析 surface を高機能に与える。AAT Quality Geometry は、ADL が得意な構造記述と conformance analysis を正面から受け止めたうえで、同じ観測面を finite atom vocabulary と source-reference field に相対化し、certificate tuple、minimal atom support family、profile-indexed comparison map、transport / curvature / fold / obstruction、repair frontier を一つの計算可能な幾何対象として扱うことで ADL を超えることを重視する。secondary rivals は静的解析器、architecture conformance checker、品質 metric dashboard であり、これらは rule violation、dependency / component graph、thresholded score、CI gate を与える。候補は、ADL / secondary rivals が得意な検出・構造解析・適合性判定を尊重したうえで、ADL では保持しにくい support、trace、transport、obstruction、repair necessity、reading loss、profile-dependent nonfaithfulness のどれを AAT だから扱えるのかを明示する。
- `novelty hypothesis`: 既存研究は、品質軸、ソフトウェア景観、多目的最適化、アーキテクチャ適合性、形式 certificate、局所大域整合性をそれぞれ扱ってきた。AAT Quality Geometry の主張は、それらを profile-indexed comparison maps と atom-supported certificates によって同一の計算可能な対象へ統合し、multi-axis quality、local-to-global obstruction、profile transport、minimal atom support、repair reachability、source traceability、loss-aware visualization を同時に保つことである。狙いは新しい品質メトリクスではなく、品質の基本単位を数値から追跡可能な幾何的 certificate へ移すことにある。
- `research lift`: 直接の品質スコアや局所違反検出では届かない設計判断を、certificate geometry、profile transport、obstruction、support、repair reachability の構造問題へ持ち上げることで判定可能にする。古典代数学で方程式そのものから解の配置と対称性へ視点を移したように、AAT では品質問題そのものから certificate の配置、transport、特異性、repair 到達可能性へ視点を移す。
- `claim boundary`: 有限 AAT geometry、選ばれた Atom vocabulary、law universe、coverage topology、coefficient sheaf、witness family、representation family、measurement threshold、certificate selector、verdict discipline 上で語る。AAT 側の certificate は supporting atom family と trace field を持つ。atom から source reference への対応は ArchMap / observation layer が供給する参照を使う。source extraction completeness、observation completeness、コード全体の品質判定は ArchMap / tooling 側の contract として扱う。
- `capability categories`: atom-supported-quality-geometry、quality-surface、certificate-transport、profile-curvature、multi-axis-signature、singularity、ridge-fold、obstruction、traceability、repair-potential、computability、invariance。
- `score threshold`: `5000`。ロングショットとして、単一セッションの小フェーズではなく、複数フェーズにまたがる大きな研究プログラムを形成する。定義、certificate、theorem、finite example、counterexample、trace example、related-work separation、paper seed が連動し、atom-supported quality geometry を独立した研究面として立ち上げる水準のまとまりを要求する。
- `portfolio constraint`: 4 カテゴリ以上で正の SCORE を持つこと。少なくとも 1 件は `proved-in-research`、少なくとも 1 件は atom support / traceability を主成果に含むこと、少なくとも 1 件は certificate transport / profile curvature / ridge-fold のいずれかを主題にすること。最初のフェーズでは、scalar-collapse counterexample、support-local repair theorem、finite trace example のうち少なくとも 2 つを含むこと。最終 SCORE の 60% 以上を scalar reading や補助定義だけで占めてはならない。
- `phase boundary criteria`: `research/reports/G-aat-quality-surface-01.md` が coherent な report section / paper seed として読めること。atom-supported quality geometry の基礎定義、Quality Surface を二次元 profile slice として読む定義、certificate tuple `Cert_A(p) = (sigma_p, omega_p, S_p, R_p, nu_p, T_p)` の意味、comparison map / transport の役割、少なくとも一つの finite profile grid 上の ridge / curvature / fold / obstruction 例、既存の品質モデル・景観可視化・多目的最適化・architecture conformance・formal certificate・sheaf consistency 研究との違い、primary rival である ADL に対する phase delta、secondary rivals である静的解析器 / conformance checker / metric dashboard に対する phase delta、次フェーズで狙うべき theorem frontier が揃っていること。
- `reward rubric`: base score は GOAL への能力増分と ADL に対する優位性で決める。`0`: 単なる scalar score、既存 violation count の言い換え、atom support を持たない抽象量、ADL の構造記述や conformance check の二番煎じ。`10-20`: certificate tuple、profile、reading、surface view の補助定義や記法整理。`30-40`: quality certificate、minimal support family、finite profile grid、source-ref trace field、comparison map の一部を与える結果。`50-70`: certificate transport、profile ridge、reading fold、repair potential、multi-axis signature、atom support を一つの枠で接続し、ADL の model / view / conformance surface では失われる構造を示す結果。`80-100`: atom-supported quality geometry の見方を変える主定理候補、profile curvature 例、scalar-collapse counterexample、support-local repair theorem、finite codebase trace example、support / repair / obstruction の新しい不変量、または ADL では表現しにくい nonfaithfulness / repair necessity / obstruction transport を AAT の theorem として固定する結果。evidence multiplier は `$research-loop` の規則に従う。penalty は、`-30`: 品質を一つの aggregate score に潰して成功扱いした、`-30`: support が atom family まで戻らない、`-30`: ADL に対する優位性を示さず、DAG / component graph / conformance check を AAT 語彙で言い換えただけだった、`-40`: comparison map なしに profile ごとの測定値一覧を geometry と呼んだ、`-40`: 既存分野の概念を並べただけで同一の計算可能対象を与えない、`-40`: AAT 内で source extraction / observation completeness を主張した、`-50`: claim boundary を越えて実コード全体の品質を断定した。
- `dullness filter`: ADL の component / connector / view / constraint / conformance analysis を AAT 語彙で言い換えただけの候補、既存の静的解析 violation count の名前替え、単一スコア化、定義展開だけの surface、comparison map を持たない dashboard、supporting atom family を持たない metric、source ref へ戻れない抽象 obstruction、reading projection artifact と intrinsic obstruction を混同する候補、既存研究の用語を横並びにしただけで新しい certificate geometry を作らない候補、既存 theorem の即時系だけの候補を弾く。
- `frontier`: atom-supported quality geometry、profile-indexed certificate space、Grothendieck construction、quality surface as 2D profile slice、certificate sheaf / certificate diagram、quality trajectory、regular cell、ridge edge、curvature cell、fold pair、obstruction locus、repair basin、minimal atom support family、chosen support vs minimal support family、hitting-set repair theorem、source-ref trace certificate、finite codebase trace example、loss-aware visualization、finite product poset `P_law x P_cover` 上の 3x3 profile grid。
- `spine`: profile 圏 `Prof_A` と certificate space `C_A(p)` を定める。次に certificate tuple と atom support / trace field を定める。続いて profile change の comparison map と coherence を定め、Grothendieck construction とその二次元 slice として Quality Surface を定義する。有限 `P_law x P_cover` grid 上で scalar-collapse counterexample、atom-support repair theorem、profile ridge theorem、profile curvature example を狙う。最後に finite codebase trace example と related-work separation を report にまとめる。この spine は固定計画ではなく、強い反例や新しい不変量が出たら置き換える。

## draft(人間の確認待ち)

(なし)

## inactive

(なし)

---

## GOAL カードの型

active な GOAL は、次の項目をすべて備えていなければならない。draft はここへ昇格する前にすべて埋める。足りない場合、`$research-loop` は `goal defect` として止まる。

- `id` と `status: active`。
- `research aim`: 研究で成し遂げたい能力や到達像。
- `core tension`: 何が分かれば本当に非自明で、何が解ければ理論の景色が変わるか。
- `rival`: 比較対象にする既存概念、手法、tooling、理論枠組み。候補の価値は、GOAL 内部の面白さだけでなく、この rival に対してどの能力で有効かでも評価する。
- `claim boundary`: どの語彙、law universe、coverage topology、係数、profile の上で語るか。
- `capability categories`: SCORE を配分する能力カテゴリ。例: quantity、invariance、computability、interpretation、obstruction、unification。
- `score threshold`: ひとつの研究フェーズを区切るために必要な合計 SCORE。
- `portfolio constraint`: ひとつの方向だけで点を稼いでフェーズを区切らないための条件。
- `phase boundary criteria`: 研究としてキリが良いと判定する条件。
- `reward rubric`: SCORE の採点規則。base score、evidence multiplier、penalty を分けて読めること。
- `dullness filter`: 定義展開、既存定理の即時系、名前替え、小補題量産を弾く基準。
- `frontier`: 探索してよい周辺領域。反例、obstruction、予想の強化、新しい不変量、別領域との橋を含めてよい。
- 任意の `spine`: 現時点の仮説的な道筋。固定計画ではなく、壊す、鋭くする、置き換える対象として扱う。
