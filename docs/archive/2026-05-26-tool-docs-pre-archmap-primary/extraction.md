# Extraction

Extraction は、repository、policy、runtime evidence、semantic evidence から tool artifact を
作る工程である。

## Extraction boundary

extractor output は observation であり、完全な architecture ではない。

```text
source repository
  -> extracted artifact
  -> validation report
  -> AIR / report
```

extractor は、unsupported constructs、ignored files、language boundary、framework adapter、
manual annotation を evidence として保持する。

## Static extraction

現行の static extraction は、Lean import graph と Python import graph を中心に扱う。
一般の call、inheritance、data dependency、package relation は、framework adapter、
custom rule plugin、manual annotation、または将来の extractor boundary として扱う。
実装済みの汎用 static extractor として読まない。

```text
current static extractor:
  source files
  + Lean / Python import parser
  + component policy
  + relation policy
  -> import edges

future / adapter boundary:
  call
  inheritance
  data dependency
  package relation
```

Thin category 的な reachability と、walk count / propagation metrics は分ける。

## Runtime evidence

runtime relation は、trace、configuration、manual evidence、runtime edge JSON などから入る。

```text
runtime evidence:
  http
  grpc
  queue
  db
  event
  batch
  manual
```

runtime edge がないことは runtime absence ではない。runtime layer は coverage boundary を
明示する。

## Semantic evidence

semantic evidence は、observation result、contract test、semantic diagram、
nonfillability witness を扱う。

```text
semantic evidence:
  diagram path
  observation result
  test counterexample
  contract evidence
  manual annotation
```

semantic diagram universe が不足している場合、semantic flatness を主張しない。

## Policy extraction

policy input は、law adoption と measured rule result を分ける。

```text
law-policy-v0 :=
  architectureId
  + laws[]
  + boundaries
  + allowed dependencies
  + forbidden dependencies
  + theorem refs
  + assumptions
  + nonConclusions
```

policy adoption は assumed claim になりうる。policy check result は measured claim になる。

## Validation

validation は次を検査する。

```text
schema version
required fields
evidence refs
claim boundary
measurement boundary
coverage / exactness assumptions
non-conclusions
formal claim promotion guardrail
```

validation success は architecture lawfulness を意味しない。
