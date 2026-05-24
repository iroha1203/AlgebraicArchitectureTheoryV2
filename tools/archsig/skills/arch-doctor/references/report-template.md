# Arch Doctor Report Template

Use this template for non-trivial user-facing reports. In this repository, write the final report in Japanese unless the user asks otherwise.

## Standard Report

```text
現在の状態
- <measured observation with artifact/path/id>
- <semantic/policy/runtime coverage status>
- <important conflict or warning>

進化予測
- <bounded pressure direction or path-class signal>
- <consequence surface>
- <calibration need>

証拠ギャップ
- <missing evidence>
- <unmeasured axis>
- <private/unavailable ref>

推奨アクション
- <action>。根拠: <artifact/id>。境界: <assumption/non-conclusion>。
- <action>。根拠: <artifact/id>。境界: <assumption/non-conclusion>。

非結論
- <what the artifacts do not establish>
- <what remains outside the measured boundary>
```

## Short Report

Use when the user asks for a quick read:

```text
要点: <one or two sentences>

根拠: <artifact paths or ids>
不足: <main missing evidence>
次: <one or two bounded next actions>
```

## Issue Recommendation

Use when recommending issue creation:

```text
Issue候補: <title>
理由: <evidence and risk>
完了条件: <bounded acceptance criteria>
非結論: <what the issue should not claim>
```

## Language Rules

Prefer:

- "artifact は ... を報告しています"
- "... と読むのが妥当です"
- "... は未測定です"
- "... は review cue です"
- "... を結論しません"

Avoid:

- "証明されています" unless a proof artifact is actually supplied
- "原因です" unless causal evidence is supplied and bounded
- "安全です"
- "確実に起きます"
- "品質が高い/低い" as a global ranking

## Citation Rules

When possible, cite:

- artifact path
- schema version
- item id
- conflict id
- recommendation id
- source ref path

Do not paste large JSON blocks unless the user asks. Summarize fields and cite ids.
