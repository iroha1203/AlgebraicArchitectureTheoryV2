# Software Architecture as a Field: ソフトウェアの進化とは何か

## はじめに: 正しい PR が残した謎

金曜日の夕方、`SAVE10` coupon の PR が merge されました。

悪い PR ではありませんでした。むしろ、よくある、普通に正しい PR でした。

checkout 画面に promo code input を足す。backend で 10% discount を計算する。payment amount を少し変える。テストは通りました。review でも大きな問題は見つかりませんでした。Black Friday campaign は間に合いました。

要求は、こういうものでした。

```text
Black Friday 用に SAVE10 coupon を追加したい。
対象商品は一部だけ。
一人一回まで。
送料割引とは併用不可。
invoice と refund でも同じ割引額になる必要がある。
```

一見すると、小さな feature です。しかし、この feature には複数の実装 path がありました。

一つ目の path では、`PromotionPolicy` を追加し、pricing service が declared interface 経由で discount を計算します。payment は最終的な price quote だけを受け取り、invoice と refund は同じ pricing decision を参照します。

二つ目の path では、`PromotionService` が必要な情報を得るために `StripePaymentAdapter` を直接呼びます。今は早いですが、promotion logic が payment provider の内部事情に依存し始めます。

三つ目の path では、UI 側だけで discount を表示します。checkout 画面では安く見えますが、invoice、refund、admin report では別の金額が出るかもしれません。

四つ目の path では、rounding や tax の順序が場所によってずれます。テストは通るかもしれません。けれど、返金時に 1 円、1 セント、あるいは tax calculation がずれるかもしれません。

これらは、どれも同じ Issue を閉じるかもしれません。しかし、変更後に残る architecture は同じではありません。

最初の PR は小さかった。二週間後、refund team が同じ rule を必要とします。実装者は checkout 側の helper を見つけ、それを再利用します。一か月後、invoice team が同じ promotion rule を必要とします。しかし rule は pricing domain ではなく、checkout helper と UI logic に分散しています。

三か月後、refund の金額が invoice と一致しない bug が出ました。さらに、新しい campaign feature を実装した AI agent が、過去の shortcut を見つけ、それをこの repository の自然な流儀として再利用しました。

ここで、私たちはいつもの問いを立てたくなります。

どの PR が悪かったのか。

でも、おそらくその問いが間違っています。

本当に問うべきなのは、もう少し大きなことです。

ソフトウェアの進化とは何か。

正しい PR が積み重なり、テストが通り、review もされている。それでも、なぜシステムは負債を溜め込み、次の正しい変更を難しくしていくのか。

この問いを扱うために、AAT、ArchSig、SFT という三つの道具を使います。どれも、ソフトウェア進化を観測し、記録し、比較し、部分的に計算可能な対象へ近づけるための概念です。

## AAT: diff ではなく、保存されたものを見る

最初の手がかりは、diff ではありません。

diff を見れば、何が追加されたかは分かります。どの file が変わったのか、どの function が増えたのか、どの test が追加されたのかも分かります。

でも、それだけでは、何が保存されたかは分かりません。

promotion pricing を追加したあとも、payment provider の境界は保たれているのか。invoice と refund は、同じ pricing decision から説明できるのか。domain model は、Stripe の内部事情を知らないままでいられるのか。

ここで出てくるのが AAT、Algebraic Architecture Theory です。

AAT は、ソフトウェア変更を単なる diff ではなく、architecture に作用する `ArchitectureOperation` として見ます。operation があるなら、その前後で保存されるべき性質があります。それを `InvariantFamily` と呼びます。

promotion pricing の例なら、invariant は次のようなものです。

- promotion rule は payment adapter の内部事情を知らない
- payment provider は最終的な authorized amount だけを見る
- UI、invoice、refund が同じ pricing decision から説明できる
- rounding と tax の順序が一貫している

ここで重要なのは、設計原則を slogan として扱わないことです。

「Clean Architecture だから良い」「SOLID だから安全」とは言いません。AAT では、それぞれの設計判断を「どの invariant を保存しようとしているのか」で読みます。

Layered Architecture なら依存方向を保存したい。Clean Architecture なら境界と inward dependency を保存したい。Event Sourcing なら event log から projection を再構成できることを保存したい。Saga なら step と compensation の対応を保存したい。

設計原則は万能札ではありません。保存したい性質を選ぶための語彙です。

Invariant があるなら、それが破れた証拠も必要です。AAT では、それを `ObstructionWitness` と呼びます。

たとえば、次のようなものが witness になります。

- `PromotionService` が `StripePaymentAdapter` を直接 import している
- UI 側だけで promotion logic が適用され、pricing domain がそれを知らない
- refund calculation だけ rounding order が違う
- event log から同じ projection を再構成できない

ここで少しだけ見方が変わります。

設計レビューで知りたいのは、「なんとなく悪い」ではありません。どの invariant に対する破れが、どの witness として現れているかです。

AAT は、architecture 全体を一気に良し悪し判定する道具ではありません。対象範囲を切った `ArchitectureObject` に対して、どの operation が、どの invariant を保存し、どの witness を残したのかを読むための道具です。

正しい変更とは、Issue を閉じた変更というだけではありません。選んだ boundary の中で、守るべき invariant を保存した変更です。同じ feature を届けても、保存された invariant が違えば、ソフトウェアは違う方向へ進化しています。

## ArchSig: 違和感を、あとで使える証拠にする

次の問題は、AAT の言葉だけでは実 repository を読めないことです。

実際の review では、アーキテクチャ上の指摘は自然言語で書かれます。

- 「責務が増えています」
- 「境界を越えています」
- 「この抽象は漏れています」
- 「この module が知りすぎています」

どれも大事な指摘です。しかし、そのままだと PR ごとの会話として流れていきます。

三か月後に同じ boundary がまた破れたとき、私たちはそれを同じ問題として認識できるでしょうか。別の reviewer が別の言葉で「ここは危ない」と書いたとき、それは前回の warning とつながるでしょうか。AI agent が過去の shortcut を真似したとき、その shortcut が以前にも witness として現れていたことを検出できるでしょうか。

ここで出てくるのが ArchSig、Architecture Signature です。

ArchSig は、PR diff、dependency graph、CI result、review comment、design memo などから、観測できる signature axis と obstruction witness を取り出す観測層です。

たとえば、review comment が次のようなものだったとします。

```text
PromotionService should not call StripePaymentAdapter directly.
```

ArchSig では、これを次のような diagnostic record として扱えます。

```yaml
axis: module_boundary_violation
boundary: promotion -> payment_provider
invariant: promotion rules must not depend on payment provider internals
witness:
  type: forbidden_import
  source: PromotionService
  target: StripePaymentAdapter
measurement_status: measured_nonzero
theorem_boundary:
  conclusion: static dependency violation detected
  non_conclusions:
    - final price correctness is not proven
    - refund semantics are not analyzed
    - tax calculation order is not analyzed
```

ここで大事なのは、ArchSig が reviewer's intuition を置き換えるものではないことです。reviewer が見つけた違和感を、次の PR、次の incident、次の AI proposal でも参照できる形に残すものです。

`ArchitectureSignature` は、選ばれた obstruction family を axis ごとに記録する多軸の診断表です。単一の品質スコアではありません。

「この system は 80 点」と言ってしまうと、何が保存され、何が破れ、何が未測定かが見えにくくなります。ArchSig では axis ごとに状態を分けます。

- measured zero
- measured nonzero
- unmeasured
- out of scope
- private / unavailable evidence
- not applicable

「検出されなかった」は「存在しない」ではありません。「測っていない」は「安全」と同じではありません。

だから ArchSig には `TheoremBoundary` が必要になります。ある check から何を言ってよく、何を言ってはいけないかを明示する境界です。

たとえば dependency graph 上で循環がないことを確認しても、それは runtime interaction の安全性を証明しません。static boundary violation が検出されなかったとしても、refund semantics や tax calculation order が正しいとは限りません。

ArchSig の魅力は、この慎重さにあります。強く言えることは強く言う。言えないことは non-conclusion として残す。これによって、レビューの違和感は、あとで比較できる diagnostic record になります。

負債が繰り返されるのは、warning が一度も出なかったからとは限りません。warning が会話として流れ、field に記憶されなかったからです。ArchSig は、その warning を次の PR でも参照できる形に変えます。

## SFT: ソフトウェア進化を計算可能な対象にする

ここで、問いは一段深くなります。

問題は、一度 shortcut が入ったことだけではありません。その shortcut が、次の実装者にとって見つけやすい場所に残り、次に到達しやすい architecture future を変えることです。

人間も AI agent も、既存コードを読みます。命名、型、test、README、過去の PR、近くにある実装例から、この repository では何が自然かを学びます。

だから、codebase は単なる保存場所ではありません。未来の変更に対する記憶です。

ここで出てくるのが SFT、Software Field Theory です。

SFT は、field-shaped software evolution の計算理論です。要求、artifact、実践、ツール、AI agent、review、CI/CD、運用 feedback、lifecycle decision が、コードベースの到達可能な architecture future をどう変えるかを扱います。

```text
SFT は、ソフトウェア進化を計算可能な対象にする。
```

ここでいう computable は、実際の開発が完全に決定可能だという意味ではありません。明示された modeling boundary、operation support、policy、observation boundary、horizon の下で、選択された問いを bounded な計算問題へ落とせるという意味です。

「codebase は次の変更を中立に受け取らない」という直感は、SFT の入口です。SFT そのものは、その直感を `SoftwareField`、operation support、selection policy、ForecastCone、governance feedback として計算対象にする枠組みです。

過去の設計判断は、未来の変更が何を自然に見えるかを変えます。direct adapter call がたくさんある project では、次の direct adapter call も自然に見えます。port と test がきれいに用意されている project では、新しい port を追加する方が自然に見えます。

SFT では、development field のうち計算可能な断面として扱う state を `SoftwareField` と呼びます。ただし、開発組織全体を完全に model 化しようとはしません。対象となる architecture question に関係する bounded slice を取ります。これを `SoftwareFieldEstimate` と呼びます。

その slice には、たとえば次のものが入ります。

- codebase
- recent PRs
- review rules
- CI signals
- incidents
- ownership
- documentation
- AI agent policies

重要なのは、model が完全であることではありません。どこまでを見たのか、どこが unknown / unmodeled remainder として残っているのかを明示することです。

この記事で特に使う計算可能な断面は、未来の変更を `OperationSupport` と `OperationPolicy` で見る部分です。

`OperationSupport` は、その field で可能または許容されている operation の集合です。`OperationPolicy` は、その中でどの operation が自然、低コスト、高コスト、禁止、review 必須に見えるかを表す選択関係です。

良い architecture は、悪い変更を禁止するだけではありません。変更のコスト地形を変えます。

良い interface は lawful path を簡単にします。良い test harness は、安全な path の確認コストを下げます。CI rule は shortcut を高コストにします。分かりやすい example は、AI agent が正しい pattern を模倣しやすくします。

だから、architecture は構造だけではありません。default の設計でもあります。

codebase は、次の変更を中立には受け取りません。過去の shortcut、review、CI、incident、例外判断は field memory になり、次に何が自然で、何が高コストで、何が禁止されるかを変えます。

## ForecastCone: 未来を一点予測しない

SFT は未来を一つに当てようとはしません。

PRD が来たとき、それは一つの future を決めるわけではありません。複数の candidate update を開きます。

promotion pricing なら、少なくとも次の path がありえます。

- lawful promotion policy path
- hidden payment provider dependency path
- UI-only pricing drift path
- rounding mismatch path
- unknown / unmodeled path

この、ある field から一定の horizon 内に開きうる future の束を `ForecastCone` と呼びます。

ForecastCone は予言ではありません。到達可能な future の形を見るための道具です。PRD や Issue が入ると、candidate update ごとに ForecastCone が変わります。review rule や CI rule が追加されると operation support が変わり、shortcut path が減ることがあります。

ただし、ForecastCone をそのまま見ても、reviewer や tech lead は使いにくい。そこで、実務で読める report に畳み直したものが `ConsequenceEnvelope` です。

promotion pricing PRD から ConsequenceEnvelope を作るなら、たとえば次のような形になります。

| path class | 開きやすい future | missing invariant | intervention |
| --- | --- | --- | --- |
| lawful promotion policy | pricing / invoice / refund が同じ decision を参照する | promotion composition law | `PromotionPolicy` と acceptance criteria を追加 |
| payment shortcut | promotion が payment provider 内部に依存する | promotion / payment boundary | forbidden import を CI で検出 |
| UI-only drift | 画面表示と invoice / refund がずれる | single source of pricing decision | UI-only pricing calculation を禁止 |
| rounding mismatch | refund や tax が微妙にずれる | rounding order | shared rounding policy を定義 |
| unknown remainder | 見えていない影響が残る | observation boundary | unmeasured として記録 |

この report から、PRD の段階で不足している invariant が分かります。rounding order、promotion composition law、promotion / payment boundary、refund / cancellation semantics を acceptance criteria に入れるべきかもしれません。

ここで、ソフトウェア進化を計算可能にするという目標の輪郭が見えてきます。

それは未来を一つに予言することではありません。PRD、Issue、PR、review、CI、incident、AI proposal の流れを、観測可能な field transition として扱い、どの future が開きやすくなっているかを計算できる形に近づけることです。

## Attractor Engineering: 良い future が選ばれやすい field を作る

ここまで来ると、問いは実務へ戻ります。

なぜ負債が溜まるのか、だけでは足りません。もし codebase が未来の変更の選ばれ方を変えるなら、逆向きの問いも立てられるはずです。

良い future が選ばれやすい field を、どう設計できるのか。

これが `Attractor Engineering` です。

アトラクターとは、変更が繰り返される中で寄っていきやすい場所や状態です。巨大な `common`、便利すぎる helper、責務が曖昧な service、直接呼べてしまう adapter は、悪い変更を何度も引き寄せます。

一方で、良い責務境界、分かりやすい API、近くにある良い実装例、適切な test harness、明確な ownership は、良い変更を自然に選びやすくします。

Attractor Engineering は、この「未来の変更がどこへ向かいやすいか」を設計対象にします。

具体的には、次のような介入を設計します。

- lawful path を見つけやすくする
- lawful path を真似しやすくする
- lawful path の検証コストを下げる
- unsafe shortcut を高コストにする
- unsafe shortcut が使われたら観測できるようにする
- 繰り返される exception を field memory に保存する

SFT では、review、CI、type checker、architecture rule、runtime guard を `GovernanceIntervention` として扱います。これらは単なる gate ではありません。future operation support と selection policy を変える仕組みです。

さらに、SFT は closed-loop です。PRD や Issue から ConsequenceEnvelope を作り、実際の PR、review、CI、runtime outcome を観測し、差分を posterior field に保存します。

```text
forecast
  + observed transition
  + forecast error
  + unexpected witness
  + review / CI outcome
  -> posterior field
```

更新すれば必ず予測精度が上がる、という強い主張は置きません。SFT がまず主張するのは、指定された update rule の下で、観測された差分が field memory に保存されることです。そこから先の forecast quality は、dataset と calibration の問題になります。

AI-assisted development では、この性質がさらに効きます。

AI agent は instruction だけを読んでいるわけではありません。既存コード、命名、型、テスト、README、設計ドキュメント、過去の実装例を文脈として変更案を生成します。コードベース全体を example として読んでいます。

shortcut だらけの codebase では、shortcut が context になります。境界が明確な codebase では、境界が context になります。

ここで問題になるのは、AI model の性能だけではありません。AI が参加する field の形です。

良い architecture とは、現在の構造がきれいなことだけではありません。良い変更が見つけやすく、真似しやすく、検証しやすく、危険な shortcut が見えやすく高コストになる field を作ることでもあります。

## Gotanda Style: field を運用に落とす

ここまでの話は、抽象的に聞こえるかもしれません。

Gotanda Style は、Attractor Engineering を実際の開発運用へ落とした例です。対象は、約 20 万行規模の Python codebase です。

中心にあるのは、agent 同士を単に会話させるのではなく、それぞれの worker が共有環境に構造化された signal を残して協調するという考え方です。

Sentry worker、Datadog worker、Quality worker、archsig-worker などが、それぞれ runtime error、slow request、test gap、layering violation、architecture signature axis の変化を観測し、field に signal を置きます。archsig-worker は ArchSig の測定を担当し、依存方向、境界違反、抽象化漏れ、未測定軸などを field に戻します。

観測 agent は直接 GitHub Issue を量産しません。Integrator が複数の signal、既存 issue、過去の won't-fix 判断、ArchSig report をまとめて、issue にするか、人間に回すか、今は追わないかを決めます。Code worker に渡すのは、意図が明確で、blast radius が小さく、reviewer が根拠を追える作業だけです。

SFT の言葉で読むと、Gotanda Style は multi-agent system によって operation support と selection policy を継続的に更新する仕組みです。

AI agent を増やすだけでは、進化は良くなりません。観測する agent、統合する場、Issue 化の基準、PR に渡す境界がそろって初めて、変更速度を field の改善に変えられます。

## Claim Boundary: 証明・観測・仮説を混ぜない

最後に、もう一つだけ重要な問いがあります。

どこまでが証明で、どこからが観測で、どこからが仮説なのか。

ソフトウェア進化を計算可能な対象に近づけるなら、この境界を曖昧にできません。形式化された定理、tool が観測した事実、review から得た signal、将来検証すべき empirical hypothesis を混ぜると、強い言葉は作れても、信頼できる研究にはなりません。

この研究での Lean の役割は、すべての architecture claim を形式証明することではありません。それは現実的ではありません。

Lean の役割は、種類の違う claim を混ぜないことです。

| claim | status |
| --- | --- |
| selected graph has no cycle | structural theorem |
| ArchSig detected no boundary violation on selected axis | tool observation |
| this reduces review cost | empirical hypothesis |
| runtime behavior is safe | not concluded |

例として、finite unweighted universe 上で、acyclicity、closed walk absence、adjacency nilpotence が対応する。これは数学的に扱える structural theorem です。

一方で、その構造が実際のレビューコストを下げるか、incident 率を下げるか、AI proposal の質を上げるかは、empirical hypothesis です。

この二つを混同すると、研究も tooling も弱くなります。

計算可能性は、強く言うことではなく、境界を正しく引くことで強くなります。

## まとめ: 技術的負債とは field の状態である

最初の問いに戻ります。

ソフトウェアの進化とは何か。

そして、正しい PR が積み重なってきたはずのソフトウェアが、なぜ負債を溜め込むのか。

この記事の答えは、まだ仮説を含んでいます。それでも、こう言えます。

ソフトウェア進化とは、コード差分の履歴だけではありません。変更操作が構造を変え、invariant を保存したり破ったりし、観測可能な signature を残し、field memory に沈着し、次の operation support と selection policy を変えていく過程です。

正しい PR の積み重ねが負債を溜め込むのは、PR が単に機能を追加するだけではないからです。PR は、未来の変更にとっての example になります。ある shortcut が一度入ると、それは次の実装者や AI agent にとって「この repository では自然な path」に見えます。境界を守る実装もまた、未来の example になります。

AAT は、変更後に何が保存され、何が破れたかを見る語彙を与えます。ArchSig は、その破れを review comment ではなく diagnostic record として残します。SFT は、その記録が次の変更の選ばれ方をどう変えるかを見る枠組みです。

だから、技術的負債とは、過去の悪いコードの集合だけではありません。

それは、未来の良い変更が選ばれにくくなった field の状態でもあります。

Software Architecture as a Field は、この進化を観測し、記録し、比較し、governance できる対象へ近づけるための研究プログラムです。
