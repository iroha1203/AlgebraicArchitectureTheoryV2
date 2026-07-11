# AAT代数幾何版 本文ブラッシュアップ提案(文体・文言)

- 対象: `docs/aat/algebraic_geometric_theory/` 全9部 + 付録A・B(+README)
- 観点: 文体の統一 / 冗長な言葉 / 蛇足 / 防衛的・念押し・メタ記述
- 数学内容・コードブロック内の形式記述には触れない。
- 行番号はコミット `9f6d54bf` 時点。適用時は原文断片で検索して位置を確認すること。
- 分類タグ: [A]=文体不統一 [B]=冗長 [C]=蛇足 [D]=防衛的・念押し・メタ。「任意」は好みが分かれる項目。

## 0. 総評

基礎品質は高い。全12ファイルで「である」調が完全に統一され(です・ます混入ゼロ)、
漢字/かな(すべて・したがって・とき・ただし)もほぼ揃い、全角記号の混入もない。
したがって提案の中心は「書き換える」より「削る」である。

直すべきは次の4系統に集約される。

1. **防衛的念押しの反復**: 同一趣旨の disclaimer が部内で2〜5回、部をまたいでさらに再演される。
   「〜を主張しない」系は地の文だけで32行あり、特に第VIII部(5回)・第IX部(297行中5回)で密度が高い。
   相対化の規律自体は理論の設計であり維持する。問題は規律の「宣言場所」が定まらず毎回言い直している点。
2. **「(単なる)Xではない。Yである」型の先回り否定**: 「単なる」27行を筆頭に、
   新情報を足さない否定文が肯定文の前に置かれるパターンが全部に分布する。
3. **部参照表記の3系統混在**: 地の文の「第N部」(約84行)/見出し・一部地の文の「PartN」(約37行)/
   第VIII部周辺だけの「Part VIII」ローマ数字(16行)。同一文内混在もある(第III部 L1718、第VI部 L1439)。
4. **後発部(VIII・IX)と付録の表記漂流**: ローマ数字、英語複数形の生埋め込み、訳語ゆれ
   (Čech/Cech、計測/測定、通常の/ordinary)、「定理候補」見出し直後の「これは theorem candidate である」再宣言(7箇所)。

### 維持するハウスイディオム(「修正」しないこと)

- 「〜として読む」「読み」「〜が立ち上がる」「次を混同しない」「証明の読み」「基礎階」「定理候補」
- 「語る」「沈黙する」(第II部 L155・第IX部 L23・付録A L135。ウィトゲンシュタイン的モチーフとして一貫)
- 相対化の規律そのもの(README「主張の読み方」が正本)
- 見出し慣行「## 1. PartN から PartN+1 へ」「## M. PartN の結論」(全部共通)
- README は規律の正本であり、本提案では変更しない。

---

## 1. 全体ルール(シリーズ一括適用)

### R1 部参照の統一

- 地の文は「第N部」に統一。見出しの「PartN から PartN+1 へ」「PartN の結論」慣行は維持。
- ローマ数字「Part VIII / Part VII / Part III / IV」は全廃:
  第VIII部 14行(L24, 100, 112, 444, 651, 1020, 1057, 1073, 1094, 1096, 1125 ほかコードブロック内 L103, 1099, 1102)、
  第IX部 L215、付録B L35。
- 見出しの逸脱: 第VIII部 L1057「## 12. Part VIII Synthesis」→「## 12. Part8 の結論」。
- 同一文内混在の解消: 第III部 L1718、第IV部 L1636、第VI部 L1439、第VII部 L1340/L1366 前後。
- 地の文の置換対象(見出しを除く): 第III部・第IV部・第V部・第VI部・第VII部の「PartN」各3〜6行。

### R2 「これは theorem candidate である」再宣言の削除

見出し「### 定理候補 X.Y」が既に宣言しているため、直後の地の文での再宣言は削る。
第VIII部 L364, L444, L494, L845, L963, L1013(6箇所)、第IX部 L270。
L444「この主張は、Part VIII では theorem candidate である。」のような行は全削除し、
続く「〜を固定して初めて定理になる」だけ残す。

### R3 相対化 disclaimer の置き場規律

正本は README「主張の読み方」+ 各部の Principle 節 + 付録B。これを前提に:

- 各部で「選ばれていない/未選択の〜について主張しない」を述べてよいのは、
  原則(Principle)節と部の結論の **2箇所まで**。定理・定義の末尾に機械的に付く反復は削る。
- 定理の相対化はコードブロックの仮定リストに語らせ、地の文では繰り返さない。
- 部をまたぐ重複は正本を1つ決めて他を参照化する。代表例:
  - 「この相対性は AAT の弱さではない」: 正本=付録A L61-62。第II部 L154「この相対性は弱さではない。」を削除。
  - 「Spec_AAT は新しい対象ではなく decoration」: 正本=付録A A.4。第III部の4回(L1216, L1226-1227, L1462, L1468)を定義箇所1回に集約。
  - 「law/coordinate/観測は Atom を生成しない」: 正本=公理A5・A6(第I部)+第III部原則4.6。
    第II部 L210, L272、第III部 L129, L195, L221 の先回りを削除。
  - 「unmeasured ≠ zero」: 正本=第VIII部原則3.2。第VII部 L850, L970、第VIII部 L89, L94-96, L176-177 の重複を間引く。

部内の具体的な削減行は §2 の部別リストに挙げる。

### R4 「単なる X ではない」型の整理

「単なる」27行(第V部7、第II部5、第III部・第VI部4、第IV部3、ほか)。
直後の肯定文が同内容を述べている場合は否定文を削除し、肯定文一本にする。
個別行は部別リスト参照。目安として半減以上を狙う。

### R5 コードブロックと地の文の二重表示の解消

同一内容を「地の文で述べ、直後のコードブロックでも書き、さらに地の文で言い直す」箇所が散発する。
原則: 形式はコードブロック1回、含意の説明は地の文1回。
代表例: 第II部 L393-399(zero claim ではない×3)、第VII部 L849-850(`unmeasured != zero` 二重)、
第V部 L916-933(原則9.1内で同一主張3連)、第VIII部 L55-57。

### R6 「読むことができる」→「読める」

3箇所: 第IV部 L255、第VIII部 L763、付録B L165。

### R7 表記ゆれ統一表

| 項目 | 統一先 | 修正箇所 |
| --- | --- | --- |
| 例えば/たとえば | たとえば(12行 vs 4行) | 第I部 L161, L360, L711、付録B L86 |
| Čech/Cech | 地の文・見出しは「Čech」、コード・識別子は ASCII「Cech」のまま | 第IV部 L1289, L1495, L1512/第VIII部 L215, L368, L399, L422, L526/付録B L101, L286, L396 |
| ひとつ/一つ | 一つ | 第IV部 L63、第V部 L49、第VII部 L175 |
| に対し、/に対して、 | に対して、 | 第IV部 L1479、第VI部 L718、第VII部 L1038 |
| 張り合/貼り合 | 貼り合(20行 vs 1行) | 第IV部 L955 |
| あり得る/ありうる | ありうる(かな) | 第III部 L156 |
| 〜だが/〜であるが | であるが(「だが、」単独は「しかし、」) | 第IV部 L784、第V部 L487、第VII部 L711 |
| zero/零(地の文) | 零・非零 | 第VI部 L964, L1406 |
| 測定されていない/未測定 | 未測定 | 第VII部 L970 |
| 言語ゲーム/language game | language game(初出の第I部 L262 のみ「language game(言語ゲーム)」と注記) | 第I部 L262、第III部 L268 |
| ordinary/通常の | 通常の | 第VIII部 L418 |
| 比較 map/comparison map | comparison map | 第VIII部 L494 |
| 移送/transport | transport | 第VIII部 L521 |
| 計測/測定 | 測定(README「測る」・第IX部「測定可能」に合わせる) | 第VIII部 L1106「計測理論」→「測定理論」 |
| coverage family/covering family | coverage family(定義見出しに合わせる) | 第II部 L434, L474 |
| 導来的/derived | derived | 第V部 L281 |
| derived-nontransverse | derived non-transverse | 第V部 L547 |
| local chart/局所 chart | 局所 chart | 第V部 L426 |
| 局所調整/local adjustment | local adjustment | 第IV部 L957 |
| 境界 mismatch/boundary mismatch | boundary mismatch | 第IV部 L1541, L1676 |
| 非可換 torsor/non-abelian | non-abelian | 第IV部 L1296 |
| threefold・三重 overlap/triple overlap | triple overlap | 第IV部 L1141, L1389, L1446 |
| 集約族/aggregation family | aggregation family | 第IV部 L1626 |
| H2/H^2(見出し) | H^2 | 第IV部 L1137, L1166 |
| 未選択の/選ばれていない | 任意(統一するなら連体は「未選択の」、述語は「選ばれていない」)| 全体に分布。要方針決定 |

### R8 自己参照は「第N部では」に統一

「この章」4箇所: 第VII部 L69、第VIII部 L1126、第IX部 L22, L296(本書の単位は「部」)。
「本文では」のうち部スコープを指すもの(第III部 L330, L374, L875, L964)も「第III部では」または削除。

### R9 証明提示の形式統一

確立形は「### 証明の読み」見出し、または短い場合のインライン「証明の読みは〜である。」の2形。
- 第VIII部 L246「理由は次である。」→「証明の読みは次である。」
- 第V部 L1451「証明は well-foundedness の定義による。」→「証明の読みは〜」
- 第VI部 L961、第IV部 L1414, L1469, L1519 など、部内で見出し型とインライン型が混在する箇所は
  「長い証明=見出し型、1〜2文=インライン型」の規約を決めて揃える。

### R10 [Certified bounded inference] ラベルの付与基準を明文化

ラベルなしの定理: 第IV部 定理7.1・9.2、第V部 定理6.1・7.3・10.6、第VI部 定理6.2・11.1・16.2。
仮定の種類(coverage/exactness 系仮定の有無)で付与を分けているなら、その基準を付録B B.2 に一行追加する。
意図的でないなら付与して統一する。※数学的判断を含むため著者判断事項。

### R11 sheaf 訳語と衝突する「層」「束」の比喩転用を回避

- 第V部 L1548「その集中点、層、経路依存性を読むために」→「成層」「階層構造」等へ
- 第VII部 L1361「representation / period / analysis の層は閉じる」→「階層は閉じる」等へ
- 第VIII部 L1166「比較するための束である」→「比較を束ねる interface である」等へ

### R12 英語複数形・英語句の生埋め込みの解消

地の文の英語術語は単数形・日本語助詞接続が基準(第I部準拠)。
- 第IV部 L707「selected witnesses and axes に対して」→「選ばれた witness と axis に対して」
- 第IV部 L1046「1-cocycles はすべての `C^1` であり」→「1-cocycle は `C^1` 全体であり」
- 第VI部 L854「selected finite-dimensional reading of it を」→「その selected finite-dimensional reading を」
- 第VIII部 L536「trace map、or selected aggregation rule などの」→ or を読点に
- 第VIII部 L941「all transfer residues を検出する」→「すべての transfer residue を検出する」
- 第VIII部 L215「Cech cochain groups、differentials、obstruction ideals」→ 単数形へ
- 付録A L17「sites は small」→「site は small」、L226「通常の affine schemes」→「affine scheme」

---

## 2. 部別の修正提案

### README

変更不要。相対化規律の正本としてそのまま維持する。

### 第I部 Atom・対象・法則

癖: §1〜§2 で「Atom の一意性 vs 観測の粗さ」の念押しが4系統(例1.4末尾・公理A8・命題A9・coarse projection 弁明)
重複する。これが本部の冗長さの大半を占める。

- L35-37 [D]「重要なのは、AAT の内部では Atom が生成元として扱われることである。」→「AAT の内部では、Atom は生成元として扱われる。」(「重要なのは〜」枠を外す)
- L41-44 [D] 例1.2 冒頭の弁明3文「これは閉じた完全列挙ではない。今後の研究や実コード解析によって、…新しい Atom family を追加しうる。」→「ここに挙げる Atom schema は現在の core family であり、閉じた列挙ではない。」の一文へ圧縮
- L59 [B]「これらはすべて、AAT の中では primitive architectural fact として扱える。」→ 削除(L41 と重複)
- L307-309 [D]「意味は開発者の心理的意図や自然言語ラベルだけでは定まらない。」→ 直後の肯定文(「固定された language game と use-rule の下で〜が定まる」)に統合
- L311-312 [D]「これは意味の非一意性ではなく、semantic fact の重なりである。」→ 「ではなく」型はこの節ではここ1箇所に絞る
- L329-330 [D]「それは semantic Atom の曖昧さではなく、coarse semantic observation である。」→「それは coarse semantic observation である。」
- L377 [C]「基本 Atom は単独でも意味を持つが、AAT の力は組み合わせで現れる。」→「基本 Atom は、組み合わせて初めて law と obstruction を生む。」(「AAT の力」を削る)
- L498-503 [D] 例1.4 末尾の一意性念押し(「semantic Atom も例外ではない。…projection または truncation である。」)→ 公理A8・命題A9 と三重複。2文程度へ圧縮
- L525-529 [D]「抽出器や観測手段が coarse projection しか返さないことはある。その場合に失われるのは Atom の一意性ではなく、観測精度である。」→ 削除し、最後の「coarse projection 上の結論は、その projection が保存する axis に限って読む。」のみ残す
- L612-615 [D]「これは一意性の失敗ではなく、一意性の相対化である。」→ 任意(残すなら A8 の対比はここだけに)
- L627-674 [D] 命題A9 前半は A8 の再演。L639-641 の物理アナロジー(「物理的な対象について、測定が対象の全情報を完全には与えないことがある。…AAT の Atom も同じである。」)を削除し、L664-671 の四区分(existence / observation / projection / reconstruction)を主体に再構成
- L844-846 [B]「この命題は AAT の生成原理である。AAT の対象は Atom を忘れて現れるのではなく、Atom によって支えられた architecture object として現れる。」→ 前半一文のみ
- L913 [D]「これらは単独の quality score ではない。」→ 削除可(次文「各 invariant は異なる law と obstruction に対応する」で十分)
- L929-930 [D]「この分類の意義は、SOLID を万能原理として扱わないことにある。」→ 削除し「局所契約層の invariant は、…自動的には含意しない。」から始める
- L975 [B]「lawfulness は obstruction absence と最初から同一視しない。」→「最初から」を削除
- L1190-1191 [D] 定理9.3 末尾「この同値は、選ばれた…に相対化される。選ばれていない Atom や軸について zero を主張しない。」→ L1174-1177 の同旨 disclaimer と二重。後段を削除

### 第II部 Architecture Geometry・Site・Sheaf

癖: 否定先行の二文構成(「ではない」9回・「ではなく」7回・「単なる」5回)。
「Atom 非生成」(4回)と「law universe と selected reading に相対化される」(L444・L643 ほぼ同文)の反復。

反復の集約: Atom 非生成は原則4.4 を正本に L210・L272・L412 を削除。
zero 不主張は L393-399 の三重表示を一文+コード1回に。スコープ宣言は L130-132 を残し L760-761 を削除。

- L23 [D]「これは経験的な複雑性ではなく、次の構造である。」→「これは次の構造である。」(任意)
- L54 [D]「しかし AAT が扱いたい対象は、単なる object ではない。」→ 削除して次文に統合
- L85 [D]「`X_S^{V,U,J}` は、裸の source ではない。」→ 次文と統合し「〜に相対化された…である。」のみに
- L154 [D]「この相対性は弱さではない。」→ 削除(付録A L61-62 が正本。R3)
- L155 [C]「AAT は語れることだけを確かに語る。」→「確かに」を削除(「語る」モチーフ自体は維持)
- L210 [D]「context は Atom を生成しない。」→ 削除(原則4.4 へ集約)
- L261 [B]「射は次のような操作として現れる。」→「射は次の操作として現れる。」
- L272 [D]「射も Atom を生成しない。」→ 削除
- L339 [D]「この命題は、一般の `ArchCtx(A)` が常に finite-meet category であるという主張ではない。」→ 肯定形「この命題は、後続の Čech complex と chart gluing を支える最小構成モデルを与える。」
- L382 [B] L374「局所データを制限する」と述語重複。一文に統合
- L393-394 [D/A]「projection は zero claim ではない。」「zero になったのではなく、忘れられたのである。」→ 一文に圧縮し、「忘れられたのである」(本書唯一の「のである」強調)は「忘れられただけである。」へ
- L412 [D]「refinement は隠れていた Atom を生成するのではなく、」→ 肯定形のみに(非生成3度目)
- L434, L474 [A] covering family → coverage family(R7)
- L443-444 [D]「coverage family は単なる file list や module list ではない。何が「覆われた」と言えるかは、law universe と selected reading に相対化される。」→ 一文化し、L643 のほぼ同文と統合(原則7.3 側を正本に)
- L511 [B]「すなわち、`J_U` は次を強制的に含む。」→「強制的に」削除
- L552 [B]「単なる cover ではなく、必要な witness と axis を保つ cover を使う。」→ 直前 L549-550 の言い直し。文ごと削除可
- L554 [A] 補題7.2A/7.2B/7.2C の英字付き番号は X.Y 形式から逸脱。7.3 以降へ振り直しを検討(参照箇所も連動)
- L579 [D]「この補題は、すべての cover が `U`-adequate であるとは言わない。」→ 削除(直後 L580 が肯定形で同内容)
- L584-587 [B] 定義7.2B・命題7.2C の非公式な先取り段落。7.2B の導入へ移すか削除
- L668 [B]「省略して、architecture object `A` が固定されているとき、」→「architecture object `A` が固定されているときは、省略して」
- L745 [A]「### 定義 10.2 Architecture Sheaves」→ 節題 L728「Architecture Sheaf」と単複統一
- L761 [D] 第II部スコープ宣言の重複(L130-132 と)。削除
- L860 [D]「Sheafification gap は、ただちに obstruction cohomology そのものではない。」→ 次文と統合し肯定形一文に

### 第III部 Law Algebra・Obstruction Ideal・Lawful Locus

癖: disclaimer 4系統(unselected≠zero ×5、Atom 非生成 ×4、Spec_AAT=decoration ×4、no-cancellation ×3)と、
sheafification 構成の3回再掲。「無条件」5回。

反復の集約: unselected≠zero は原則5.7(L825)を正本に L241・L1193 を削減。
Atom 非生成は原則4.6 を正本に L129・L195・L221 を削除。
Spec_AAT=decoration は定義8.1 周辺1回に集約し L1226・L1462・L1468 を削除。
no-cancellation は原則5.6 を正本に L531・L605 を参照化。
sheafification 構成は §1(L77-83)を正本に L109・L384 を「構成は §1 の sheafification による」へ短縮。

- L91 [B] ringed AAT topos の二重定義(定義9.1 と)。ここは予告に弱める
- L149/L156 [A]「変わりうる」と「あり得る」が隣接混在 → 「ありうる」へ(R7)
- L155 [D]「これは、すべての architecture operation が可換であるという主張ではない。」→ 削除(直後が肯定形で同内容)
- L251 [A]「Semantic coordinate は、」→「semantic coordinate は、」(文頭でも小文字)
- L365 [D]「重要なのは、`O_raw^U(W)` の段階では」→ 強調枠を外し「`O_raw^U(W)` の段階では、selected law witness ideal を zero にしない。」
- L739 [A]「記法:」→ 地の文唯一の裸コロン行。「記法は次である。」
- L778 [A] 単独行「このとき」→「このとき、」(L720・L1085・L1255 に合わせる)
- L875 [D]「したがって本文の slogan は次のように読む。」→「したがって、この slogan は次のように読む。」
- L889 [D]「この分類は law-as-equation の核を弱めるものではない。」→ 削除(後続の claim boundary 文で足りる)
- L964 [D]「本文で local sum の表示を使うときは、」→「以降で local sum の表示を使うときは、」
- L969 [B] 原則6.3 は定義6.1(L907-924)の再掲。地の文+コードブロックを削除可
- L1032 [D]「この条件は、selected law universe に相対化された lawful condition である。」→ 原則7.3 の先取り。削除候補
- L1091 [A] 「ただし `f_i` は `I_U(W)` と `B_W` の chosen generators である、を」→ 構文破綻。「(`f_i` は `I_U(W)` と `B_W` の chosen generators)を unlawfulness certificate と呼ぶ。」等に再構成
- L1162 [A] 単独行「なら」→「ならば」
- L1190 [C]「これは、すべての可能な law、すべての未来の振る舞い、すべての意味論的 universe に対する完全正当性ではない。」→ 三連「すべての」を一項に圧縮し、L1653 の同旨と統合
- L1226-1227 [D]「したがって、`Spec_AAT` の点は AAT 固有の新しい点ではなく、」→ 削除(L1216-1224 の言い直し)
- L1291 [B]「追加の presentation-preservation」→ 条件4.5 の presentation-stability への参照に
- L1321 [D]「したがって、…無条件に raw moduli functor を表現するのではない。」→ 削除(L1303「この仮定の下でのみ」と同旨)
- L1397 [D]「これは scheme を弱めた代替物ではなく、」→ 肯定形のみに
- L1465 [C]「`|X|` は裸の source 空間ではない。」→「`|X|` は source の空間そのものではない。」
- L1520 [A]「ただ restriction された環の中で読まれなくなる。」→「単に〜だけである。」
- L1535 [D]「それは defect が消えたことを意味しない。」→ コードブロック(`unread defect != zero defect`)に語らせ、地の文は一方を削る
- L1593/L1758 [A]「大域的 lawful section」と「大域的な lawful section」→「な」の有無を統一
- L1653 [D]「これは「すべての architecture が絶対的に正しい」という定理ではない。」→ 削除(L1190 と同旨2回目)
- L1654 [A]「sound and complete に law failure を表現するなら、」→「sound かつ complete に」
- L1718 [A] 同一文内「第III部」+「Part2」混在 → R1

### 第IV部 Obstruction Cohomology

癖: §12(Topological Debt)以降で表記の質が落ち、和訳ゆれ・口語(「なので」)が後半に集中。
定義2.4 が最冗長(「ただし」3連発、同一 package の呼称4通り)。「第VI部で扱う」繰り延べ3回。

反復の集約: 「第VI部の stack/gerbe で扱う」は L155 を残し L178・L1194 を削除。
「core/feature 内部は lawful だが境界に残る」は L822 を正本に L851-852・L992-993 を圧縮。
「群の非零≠具体 class」は原則4.4(L465-466)を正本に L1366-1367・L1427-1428 を参照化。

- L41, L50, L52, L65, L312, L1634, L1636 [A] Part4 → 第IV部(R1。見出し L50「Part4 の中心定理」も)
- L154 [C]「は重要であるが、」→ 削り「〜は第VI部の stack 的構造で扱う。」に直結
- L184-185 [B]「ただし」連続2文 → 前者を「なお」にするか統合
- L197 [B] 標準 obstruction package の呼称4通り(標準 obstruction hierarchy / 標準的な obstruction package / 標準係数体系 / canonical reference package)→ 1つに統一
- L229 [B]「どちらの圏で扱うかを固定せずに cohomology group を書かない。」→「cohomology group を書く前に、どちらの圏で扱うかを固定する。」
- L264 [D]「これは `Ob_U` を一種類に固定する定義ではない。」→ 削除(L183 と重複)
- L379 [A]「chosen topology」→「選ばれた topology」
- L407-409 [D] cover-relative と `X` 上の cohomology の区別の再説明(定義3.3 で確立済み)→ 簡約
- L455-456 [D] 原則4.3 内の同旨2回+コード2回 → 後半を削減
- L466 [B]「それが言うのは、…ということである。」→「言えるのは…の存在可能性までである。」
- L629 [A]「fixed local adjustment structure の下で」→「固定された local adjustment structure の下で」
- L694 [D]「hidden coupling は、単に観測されていない defect ではない。」→ 次文と統合
- L784 [A]「lawful であることは重要だが、」→「重要であるが、」(R7)
- L915 [A] 定理9.2・定理7.1 のラベルなし → R10
- L953 [B]「それぞれ」連続 → 後者を「各 local section は」
- L955 [A]「張り合わせ」→「貼り合わせ」(R7)
- L1012/L1432 [A]「定数 sheaf `Z`」vs「定数層 `k`」→「定数 sheaf」に統一
- L1105 [A]「Čech nerve with boundary components の chain complex」→「boundary component 付き Čech nerve の chain complex」
- L1414-1415 [A]「証明の読みは有限次元線形代数である。`H^1 = ker d_1 / im d_0` なので」→「〜であるから」(口語「なので」)。提示形式は R9
- L1489 [A]「負債が消えたことではなく」→「debt が消えたことではなく」
- L1495 [B]「orientation を固定し、cochain と chain の pairing を固定する。」→「orientation と cochain-chain pairing を固定する。」
- L1565 [B]「加法性を次の形で固定する。」→「加法性を次で固定する。」

### 第V部 Derived Law Geometry と Repair

癖: 「単なる」7回(全部で最多)。profile 固定 boilerplate「〜を固定しない限り theorem は立てない」4回、
「`LawConflict_1 != 0` だけでは具体的 transfer を結論しない」4回。結論章が本文の防衛文を字句再掲。

反復の集約: profile 固定規律は §8 冒頭(または原則8.x)で一度規約として宣言し、L785・L831・L866・L1160 は省略or参照化。
transfer 注意は定義10.4(L1130)を正本に L940-944・L1026-1031・L1189-1196 を参照化。
「単なる repair の副作用ではない」は L339 を残し L1539(結論)を削除。

- L47, L1484 [A] 見出し「Part4 から Part5 へ」「Part5 の結論」はシリーズ慣行どおり維持。地の文 L49, L59, L107, L1323 の PartN → 第N部(R1)
- L49 [A]「ひとつの law universe」→「一つの」(R7)。「貼り合うかであった」→「貼り合うかどうかであった」
- L87 [B]「どのように交わるか、すなわち law constraints が横断的に交わるかどうかが重要である」→「交わるか」の重複を解消
- L107 [A]「ここでは簡潔のため」→「簡単のため」(数学慣用)
- L250 [B]「classical intersection は、交差する結果を表す。」→「交差の結果を表す。」
- L329 [A]「### 例 4.3 非横断的 Law」→ 見出しタイトルは英語に統一(「Non-Transverse Laws」等)
- L375-383 [B] 定義5.1 冒頭式の字句再掲ブロック → 削除
- L411-412 [D]「単なる defect count ではない。また、`U` と `V` の両方に違反があるというだけでもない。」→ 二重否定の後段を削除
- L422 [B]「first law conflict sheaf は、lawful loci の交差構造から生じる。」→ 削除(原則5.3 冒頭の言い直し)
- L577-578/L644-645 [D]「classical joint lawful locus の存在を否定しない」系2回 → 一文に圧縮
- L668 [D]「非横断性は、失敗の数ではない。」→ 削除(L411 の反復。原則7.5 は転送の論点に絞る)
- L677 [C]「architecture geometry 上では深い制約に触れている」→「大域的な制約に触れている」
- L916-933 [D] 原則9.1 内の同一主張3連(地の文+コード対比2本)→ L925-933 を削除
- L935 [D]「これは「証明書がないことから偽を証明する」定理ではない。」→ 削除(直後の規律文で足りる)
- L946 [A]「### 読み」→ 全コーパス唯一の単独見出し。「### 原則 9.1 の読み」等へ
- L966 [A]「§10 の support-localized pairing」→「§」は全コーパスでここのみ。「定義 10.4 の」へ
- L1028-1029 [B] 結論の言い直し → 直前のただし書きに統合
- L1096 [D]「選ばれていない law axis について、obstruction の増減を主張しない。」→ 削除(L1089・L1095 で足りる。R3)
- L1301 [D]「したがって、良い refactoring は単なる code cleanup ではない。」→ 次行の肯定文のみに
- L1314-1316 [B] 系11.3 の地の文は原則11.2 とほぼ同内容 → 新規部分のみに
- L1323 [D]「このため、refactoring は Part5 の自然な対象である。」→ 削除
- L1443/L1452 [A]「無限 repair sequence」vs「無限列」→ どちらかに統一
- L1548 [A]「層」の比喩転用 → R11

### 第VI部 Singularity・Monodromy・Stack

癖: 「ではない。」文末15回(うち7回は "Is Not" 型原則と連動した意図的なもの、8回は先回り防衛)。
§4〜6 で「warning であって主定義の結論ではない」が4箇所連続。

反復の集約: warning 系は定義5.1 直後(L313-314)を正本に L325-327・L398・L410-415 を集約。
「endpoint comparison では見えない」は定義10.3(L906)を正本に L831 の先出しを削除。
God object の定義再述(L570-581/L601-602)は定義7.1 に一本化。
quotient stack 宣言の重複(L1227/L1254)は前者に。

- L84 [D]「これらは別々の比喩ではない。」→ 削除して肯定文に直結
- L113 [C]「stratum は単なる file list ではない。」→ 次文と統合
- L192 [A] 主述ねじれ →「cohomological grading には、…convention を採用する。」
- L196 [B]「操作メニューの一覧ではない」→「操作の一覧ではない」
- L262 [D]「これらは主定義の別名ではなく、」→ 念押し部を削る
- L302 [B]「を仮定すると、これは、…ことを表す。」→「を仮定すると、`S` の近傍に実際の selected lifting failure が存在する。」
- L360-361 [B] 二文目の主語反復を削除し「そうではなく、〜」と接続
- L398 [A]「定義5.1の意味での」→「定義 5.1 の意味での」(半角スペース)
- L413 [A] 主述ねじれ →「滑らかな lifting が存在しない可能性がある。」
- L581 [B]「すなわち、God object とは、…singular stratum である。」→ 直前コードブロックの言い直し。一方に
- L854 [A] 英語句の生埋め込み → R12
- L946 [A]「十分必要条件」→「必要十分条件」(シリーズ全体で唯一の逆順)
- L964, L1406 [A] zero →「零」(R7)
- L1006-1007 [D] 定理10.7 末尾の「主張しない」+相対化の二文 → 主張文に織り込み一文化
- L1032 [B]「endpoint comparison では見えない hidden architecture debt」→ hidden と「見えない」の重複解消
- L1084 [C]「単なる関数ではなく」→「関数ではなく」
- L1096 [B]「この違いを潰さずに保持するため」→「この違いを保持するため」
- L1140-1141 [D] 三連「すべての」境界宣言 → 原則9.6(L783-784)と同型。短縮または相互参照
- L1220-1221 [D]「〜を混同しない。」念押し → 削除(直前 L1210-1218 の規約宣言と同内容)
- L1254 [B]「このとき、codebase essence は quotient stack として定義される。」→「このとき、上の定義が成立する。」
- L1273 [C]「また、単なる graph isomorphism でもない。」→「また、graph isomorphism でもない。」
- L1367 [B]「もし gerbe が…場合は、」→「もし」を削除
- L1374 [A]「cohomology group の元というより、」→「元ではなく、」
- L1387 [B] 単独行「もし、」→ 削除
- L1421 [A]「大域的な canonical decomposition」→「global canonical decomposition」(同節3回と統一)
- L1439 [A/B] 一文内「第VI部/Part5」混在+「現れた/現れるか」反復 → R1 と合わせ書き換え
- L1477-1478 [D] 結論の「単なる実務上の困難ではない」→ L1425-1426 とほぼ同文。一方を簡略化

### 第VII部 Representation・Periods・Analysis

癖: 短い地の文+コードブロックの交互反復で、地の文がコードを前後で言い直す(特に §6 で同一内容3〜4回)。
「次で表す/定義する。」と式の間に限定条件の段落が割り込む構成の乱れが2箇所。

- L46, L59, L741-742, L913, L1140, L1340 [A] Part6/Part7 → 第VI部/第VII部(R1)
- L69 [A/D]「この章では、」→「第VII部では、」(R8)
- L121 [B]「保存または指定された形で制限する」→「保存し、または指定どおりに制限する」
- L175 [A]「ひとつの geometry」→「一つの」(R7)
- L264-265 [D]「semantic flatness を主張しない。」→ 原則3.7(L269-270)と重複。一方に集約
- L407-413 [A]「次で表す。」と式の間に段落割込み → 式を直後に移し「ここで〜」を式の後へ
- L413 [D]「固定せずに strict period pairing は主張しない。」→ 肯定形「この homology model と係数評価を固定した場合に限り定義する。」
- L581 [A/D]「したがって、本文では次を区別する。」→「以下では次の三つを区別する。」(接続も帰結でない)
- L652, L661 [B] 定理6.1 の主張の言い直し2回 → 削除(コードブロックが同内容)
- L711 [A] 単独行「だが、」→「しかし、」(全9部唯一の口語逆接。R7)
- L777-778 [B/D]「curvature は lawfulness を置き換えない。」→ 次文と一文化
- L832-833 [B/D]「distance value は実数だけではない。」→ 次文と一文化
- L849-850 [B]「`unmeasured` は zero ではない。」→ 直後のコード `unmeasured != zero` と二重。一方に(R5)
- L892-894 [A/B]「次で定義する。」と式の間への割込み → 式の後へ。「相対化する」→「相対化される」(受動形に統一)
- L902 [B]「どれだけ近いかを読む metric reading である。」→「lawful locus への近さの metric reading である。」
- L921-922 [B] 言い直し2文 → 前段に統合
- L970 [A]「測定されていない region や axis を zero mass とみなさない。」→「未測定の region や axis を」(R7)
- L1038 [A]「に対し、」→「に対して、」(R7)
- L1066 [D/A] 定理の主張と証明の間に disclaimer 割込み → 証明の後へ移動
- L1076 [A]「Architectural Dehn function」→「architectural Dehn function」(Dehn のみ大文字維持)
- L1103 [A]「この結論は使えない。」→「この結論は適用できない。」
- L1140 [B]「〜で読むものである。」→「〜で読む。」(部内唯一の「ものである」)
- L1197 [C]「AAT geometry の外へ過剰に飛び出さず、」→「逸脱せず、」
- L1216 [A]「semantic reading / broad period」→「broad period / reading」(語順統一)
- L1255-1256 [B] 係り受けのねじれ →「…などを representation `R` で読んだ値である。」
- L1260 [B/D]「単一 representation ではなく representation family に対して置く。」→ L1221 の繰り返し。短縮
- L1299 [A]「この theorem は、」→「この定理は、」
- L1361 [A]「層は閉じる」→ R11
- L1364 [C] 列挙末尾の「そして」→ 削除
- L1366 [B]「次の第VIII部では、」→「第VIII部では、」

### 第VIII部 Measurement Theory

癖: 後発部ゆえの漂流が最多。ローマ数字 Part VIII(14行)、theorem candidate 再宣言(6回)、
「主張しない」系9回+「に相対化される」5回+「の中でだけ」3回が定理末尾に機械的に付く。
「unmeasured ≠ zero」「analytic に小さい ≠ structural zero」がコードと地の文の双方で各4〜5回。

反復の集約: 部の守備範囲宣言は L112 と L1125-1126 が首尾重複 → 結論側(原則12.5 近傍)を残し簡略化。
「unmeasured ≠ zero」は原則3.2 を正本に L89・L94-96 を削減。
「analytic ≠ structural」は原則(L191-192)を正本に L638-639・L727 を参照化。

- L24 ほか [A] ローマ数字 Part VIII/VII/III → R1(14行一括)
- L55-57 [B/D] 否定+肯定の二重表明 →「計算可能なのは…範囲だけである。」一文に
- L91 [D]「`Verdict_M` は、単なる label 集合ではない。」→ 肯定文のみに
- L132 [A]「より型を明確に書けば、」→「型を明確に書けば、」
- L167 [A]「これらの verdict は互いに混同しない。」→「これらの verdict を互いに混同しない。」(助詞のみ修正。「混同しない」はハウスイディオムとして維持)
- L246 [A]「理由は次である。」→「証明の読みは次である。」(R9)
- L269-270 [A]「任意 site、…任意の finitely generated module」→「任意の」に統一
- L331-332 [D] 原則5.3(L336-337)と同内容 → 一方に
- L364, L444, L494, L845, L963, L1013 [B] theorem candidate 再宣言 → R2
- L418 [A]「ordinary persistence module」→「通常の persistence module」(R7)
- L442 [B]「という形の安定性を期待する。」→「という安定性を期待する。」
- L445-446 [B]「意味するのは、…ということである。」→「これは、…証明対象を明示する。」
- L447-448 [B] 定義6.2 の反復 → 削除
- L474/L482 [A]「次を期待する。」+式+「として読む。」の構文ねじれ → L482 を削除するか L474 を「次の bound を読む。」に
- L492 [A]「となると読む。」→「と読む。」
- L494 [A]「比較 map」→「comparison map」(R7)
- L536 [A] 読点列への英語 or 混入 → R12
- L563-564 [D] 否定+肯定の二重表明 → 後者一文に
- L707/L712 [A]「したがって」連続 → 後者の文頭を「この分解により」等へ(「ゆえに」は導入しない)
- L717 [A]「大域 lawful state へ行く任意の repair route」→「へ到達する」
- L763 [B]「として読むことができる。」→「として読める。」(R6)
- L858 [C] 「の中でだけ語る。」→「の中でだけ比較する。」(任意。「語る」モチーフとして残す選択も可)
- L896 [B]「が非自明に成り立つことをいう。」→「が成り立つことをいう。」
- L941 [A]「all transfer residues」→ R12
- L1057 [A]「## 12. Part VIII Synthesis」→「## 12. Part8 の結論」(R1)
- L1092 [D] synthesis の「主張しない」再掲 → 削除(L1125-1126 側に一本化)
- L1096/L1106 [A]「測定可能」/「計測理論」→「測定」に統一(R7)
- L1125-1126 [D/A] L112 との首尾重複を解消し、「この章」→「この部」(R8)
- L1128 [A] 見出し内括弧「(AAT-GAGA)」→ 名前へ組み込み「AAT-GAGA Finite Measurement Comparison」
- L1165-1167 [A]「この theorem は」→「この定理は」(2箇所)。「比較するための束である」→ R11

### 第IX部 Evolution Geometry

癖: 297行の短い部に「主張しない/沈黙する/意味しない」系が8箇所。原則2.2 と結論が正本としてあるのに、
§1・定理4.2・定理5.3 でも都度言い直している。

反復の集約: 原則2.2(L62)と結論(L296-297)を残し、他を間引く。

- L6-7 [D/B]「architecture は一つの静的対象としてだけ現れるのではない。selected operation、…の列として現れる。」→ 一文化
- L10 [D]「ここで扱うのは、時間方向の全事象ではない。」→ 削除(L22-23 と重複)
- L22, L296 [A]「この章」→「第IX部」(R8)
- L22-23 [D] §1 末尾と結論 L296-297 の首尾重複 → §1 側を簡略化
- L50-51 [D]「trace category は、実ログの完全性を主張しない。」→ 原則2.2 に統合
- L87 [A]「state transition sheaf と呼んでよい。」→「と呼ぶ。」(付録B B.1 の記述と揃える)
- L98 [D]「`TempCoeff_A` は state transition presheaf 全体ではない。」→ 肯定形一文化
- L167 [D]「これは、全時間列の再構成を主張しない。」→ 削除し、続く肯定文(「固定された〜の中で、…貼れることを読む。」)のみに
- L214-215 [D/A]「これは、terminal state が lawful であることを意味しない。」→ 内容があるため維持可だが肯定形推奨。「Part III / IV」→「第III部・第IV部」(R1)
- L270 [B]「この主張は theorem candidate である。」→ 削除(R2)

### 付録A Mathematical Ambient and Standard AG Embedding

付録Aは「decoration 原則」「相対性は弱さではない」等の **正本** として機能させる(R3)。
その上で次を調整する。

- L4 [D]「本文の主系列は Atom から始まるため、この付録は Part 0 ではない。」→「本文の主系列は Atom から始まる。この付録は、必要なときに参照する標準化レイヤである。」(「Part 0 ではない」の防衛を外す)
- L17 [A]「sites は small」→「site は small」(R12)
- L85 [D]「relative parameter は単なる注記ではなく、」→「relative parameter は、条件がそろう場合には比較射を持つ。」(任意)
- L226 [A]「通常の affine schemes」→「affine scheme」(R12)
- L262 [A/D]「注意として、affine AAT charts を貼り合わせて〜」→「注意として、」を削除して文を直接始める(全コーパスで唯一の「注意として」)
- L274-275 [D]「この本文で `ArchitectureScheme` と呼ぶのは、…「glued scheme is automatically affine」という主張ではない。」→ 直前 L262-273 で十分。圧縮または削除
- L297 [B]「law を無理にすべて closed ideal へ押し込めない。」→「無理に」削除(任意)
- L358-359 [D]「この構成は、open、temporal、descent、stacky な law を消すものではない。それらは〜として扱う。」→ 後文のみ残す

### 付録B Claim Status and Finite Worked Example

台帳としての反復は構造的なので許容。次のみ調整する。

- L29, L32, L34 [B] 「中央 Lean obligation ではなく、本文命題と対応する `Formal/` declaration を直接確認する。」が3セルで同文 → 表の直前に一度書き、セルからは削除
- L86 [A]「例えば」→「たとえば」(R7)
- L101, L286, L396 [A] 地の文・見出しの Cech → Čech(R7。表内の識別子 `Cech stability` は ASCII のまま)
- L164-165 [B]「として読むことができる。」→「として読める。」(R6)
- L218-220 [D] B.6 末尾の「未選択の data source や外部 defect を直接主張しない。」→ 削除(B.7 の総括 L236-237 と重複。B.8.5 Verdict Boundary は節の目的なので維持)

---

## 3. 適用の進め方(提案)

差分のレビューしやすさのため、3段階の PR に分けることを推奨する。

1. **機械的置換**(R1, R6, R7, R8, R12 と各部の [A] 項目): 判断不要の表記統一のみ。diff は大きいが機械的。
2. **反復 disclaimer の間引き**(R2, R3, R4, R5 と各部の [D] 項目): 正本を決めて削る。部ごとにコミットを分ける。
3. **文単位の書き換え**(各部の [B]/[C] 項目と構成の手直し): 一文ずつ著者判断を要するもの。

R10([Certified bounded inference] の付与基準)と R7 の「未選択/選ばれていない」統一は著者の方針決定が先。
適用後、README・付録Bの規律記述は無変更であることを確認する(規律の正本を動かさない)。
