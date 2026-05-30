---
name: tool-release
description: ArchSig / FieldSig など repository tooling の GitHub Release draft、release notes、asset workflow 検証を行う。Use when the user says "$tool-release vX.Y.Z", asks for a tooling release, ArchSig release, FieldSig release, release note draft, or release asset verification.
---

# Tool Release

ArchSig / FieldSig など repository tooling の release を準備する。
このリポジトリでは、ユーザーへの報告は日本語で行い、GitHub Release notes は原則として英語で書く。

## 入力

- ユーザーが `$tool-release vX.Y.Z` と言った場合、`vX.Y.Z` を release tag として扱う。
- `-rc.N` を含む tag は prerelease 候補として扱う。
- 明示がない限り、現行 release 対象は ArchSig とする。
- FieldSig は、FieldSig binary asset workflow / release asset が存在する場合だけ配布物として扱う。存在しない場合は release notes の関連変更・検証対象に留める。
- tag、対象 tool、draft / publish の意図が曖昧な場合は、作業前に短く確認する。

## 基本方針

- Release は GitHub Issue / PR の完了状態を根拠にする。
- Release notes は `.github/RELEASE_TEMPLATE.md` を起点に英語で作成する。
- ArchSig / FieldSig の claim boundary を混同しない。
- ArchSig は AAT structural telemetry / analysis packet / review artifact として扱う。
- FieldSig は forecast, governance, calibration, operational feedback を扱うが、forecast correctness、probability、causal correctness、global safety、CI/Test/human review の置換を主張しない。
- ArchSig release notes では、Architecture Signature を単一スコアではなく、多軸診断として扱う。
- Release を勝手に publish しない。公開は必ずユーザー確認後に行う。
- 既存の未コミット変更はユーザー変更として扱い、勝手に戻さない。

## 標準手順

1. 作業状態を確認する。
   - `git status --short --branch`
   - dirty worktree の場合は、release 作業に関係する変更か確認する。関係しない変更は触らない。
   - release は原則として `main` 上の merge 済み状態から作る。作業ツリーが clean なら `git switch main` と `git pull --ff-only` で最新化する。

2. release context を確認する。
   - `git fetch --tags origin` で remote tag を確認できる状態にする。
   - `gh release view <tag>` で既存 release の有無を見る。
   - `git tag --list '<tag>'` で local tag の有無を見る。
   - `git ls-remote --tags origin <tag>` で remote tag の有無を見る。
   - `gh release list --limit 10` などで前回 release tag を確認する。
   - 必要に応じて `gh pr list --state merged` や `gh api` で前回 tag 以降の PR / commit を調べる。
   - tag が未作成の場合は、対象 commit を確認し、ユーザー確認後に tag を作成・push する。勝手に release tag を作らない。

3. 対象 surface を分類する。
   - ArchSig: `tools/archsig/**`, `docs/tool/**`, `.github/workflows/archsig-release.yml`, `.github/RELEASE_TEMPLATE.md`
   - FieldSig: `tools/fieldsig/**`, FieldSig docs / workflow
   - Lean / docs claim: `Formal/**`, `docs/aat/**`, `docs/sft/**`
   - Website: `website/**`

4. release notes draft を作る。
   - `.github/RELEASE_TEMPLATE.md` をコピー元として使う。
   - `Downloads` は実際に workflow が出す asset 名だけを書く。
   - `Highlights` は PR の羅列ではなく、利用者に見える変更単位でまとめる。
   - `Compatibility And Migration` には breaking change、artifact schema、CLI surface、既存 workflow への影響を書く。
   - `Verification` は実際に通したコマンドだけを check 済みにする。未実施項目は理由を書く。
   - `Boundaries` は削らない。
   - 公開前に `vX.Y.Z`, `<...>`, `#...` などの placeholder が残っていないことを確認する。

5. 検証する。
   - ArchSig 変更あり: `cargo test --manifest-path tools/archsig/Cargo.toml`
   - FieldSig 変更あり: `cargo test --manifest-path tools/fieldsig/Cargo.toml`
   - Lean / docs claim 変更あり: `lake build`
   - website 変更あり: Playwright で静的ページを確認する。
   - release notes / workflow / docs 変更のみでも:
     - `git diff --check`
     - hidden / bidirectional Unicode scan
     - `.github/release.yml` を触った場合は YAML parse

6. draft release を作成または更新する。
   - 新規 draft:
     - `gh release create <tag> --verify-tag --draft --title "Tooling <tag>" --notes-file <notes-file>`
   - ArchSig 単独 release として出す場合:
     - title は `ArchSig <tag>` としてよい。
   - 既存 draft 更新:
     - `gh release edit <tag> --draft --title "<title>" --notes-file <notes-file>`
   - `-rc.N` tag は `--prerelease` を付ける。
   - publish はユーザー確認後にだけ実行する。

7. 公開後の asset workflow を確認する。
   - ArchSig asset build は `.github/workflows/archsig-release.yml` が release publish で走る。
   - draft 作成時点では release asset workflow は走らない。asset は publish 後に確認する。
   - `gh run list --workflow archsig-release.yml --limit 5` で workflow run を確認する。
   - 必要に応じて `gh run watch <run-id>` を使う。
   - release assets に expected archive と `SHA256SUMS.txt` があることを確認する。

## 報告

最後に日本語で次を報告する。

- release tag と draft / published URL
- 対象 tool: ArchSig / FieldSig / shared tooling
- release notes の要点
- 実行した検証と結果
- 未実施の検証と理由
- asset workflow / checksum の状態

## hidden Unicode scan

対象範囲を絞って実行する。

```bash
LC_ALL=C rg -n "[\x{200B}\x{200C}\x{200D}\x{200E}\x{200F}\x{202A}\x{202B}\x{202C}\x{202D}\x{202E}\x{2066}\x{2067}\x{2068}\x{2069}\x{FEFF}]" .github tools docs Formal README.md README.jp.md
```
