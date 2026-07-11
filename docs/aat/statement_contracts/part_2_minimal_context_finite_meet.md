# Part II proposition 4.2 statement contract

Issue #3195 で固定する命題4.2の Lean statement。初回の existence-preorder
contract は4本の独立数学査読で actual morphism uniqueness と observable
pullback を弱めていると判定されたため、ユーザー承認の下で本contractへ
置換した。

## Material premises

- `A : ArchitectureObject U`: 本文の selected architecture object。
- `Axis`, `Observable`: 本文の selected axis / observable carrier。
- `W`, `V`, `base`, `left`, `right`: 上記carrier上の extensional minimal context profile。
- `hl`, `hr`: selected minimal-context categoryの actual homで与える cospan。

thinness、antisymmetry、top、binary meet、finite limits、pullback、legacy
`ContextMorphism` restrictionは外部packageから受け取らず構成する。

## Referenced definitions

```lean
structure MinimalContextProfile {U : AtomCarrier.{u}} (A : ArchitectureObject U)
    (Axis Observable : Type u) where
  support : Set U.Atom
  support_le_object : support ⊆ { atom | A.configuration.family.mem atom }
  axis : Set Axis
  observable : Set Observable

structure RawMinimalContextProfile {U : AtomCarrier.{u}}
    (A : ArchitectureObject U) (Axis Observable : Type u) where
  SupportIndex : Type u
  supportRead : SupportIndex -> U.Atom
  supportRead_objectFamily :
    ∀ support, A.configuration.family.mem (supportRead support)
  AxisIndex : Type u
  axisRead : AxisIndex -> Axis
  ObservableIndex : Type u
  observableRead : ObservableIndex -> Observable

instance : LE (MinimalContextProfile A Axis Observable) where
  le W V := W.support ⊆ V.support ∧ W.axis ⊆ V.axis ∧
    V.observable ⊆ W.observable

def MinimalContextProfile.inf
    (W V : MinimalContextProfile A Axis Observable) :
    MinimalContextProfile A Axis Observable

def MinimalContextProfile.top : MinimalContextProfile A Axis Observable

def MinimalContextProfile.toArchitectureContext
    (W : MinimalContextProfile A Axis Observable) : ArchitectureContext A

structure MinimalContextProfile.ReadableContextHom
    (W V : MinimalContextProfile A Axis Observable) :=
  supportMap : W.support -> V.support
  supportMap_val : ∀ support, (supportMap support).1 = support.1
  axisMap : W.axis -> V.axis
  axisMap_val : ∀ axis, (axisMap axis).1 = axis.1
  observableRestrict : V.observable -> W.observable
  observableRestrict_val :
    ∀ observable, (observableRestrict observable).1 = observable.1

def MinimalContextProfile.homEquivReadableContextHom
    (W V : MinimalContextProfile A Axis Observable) :
    (W ⟶ V) ≃ ReadableContextHom W V

def MinimalContextProfile.homToContextMorphism
    {W V : MinimalContextProfile A Axis Observable} (f : W ⟶ V) :
    ContextMorphism W.toArchitectureContext V.toArchitectureContext

def RawMinimalContextProfile.normalize
    (W : RawMinimalContextProfile A Axis Observable) :
    MinimalContextProfile A Axis Observable

def RawMinimalContextProfile.inf
    (W V : RawMinimalContextProfile A Axis Observable) :
    RawMinimalContextProfile A Axis Observable

def RawMinimalContextProfile.infBinaryFan
    (W V : RawMinimalContextProfile A Axis Observable) :
    BinaryFan W V

def RawMinimalContextProfile.readableSetoid :
    Setoid (RawMinimalContextProfile A Axis Observable)

abbrev RawMinimalContextProfile.QuotientProfile :=
  Quotient RawMinimalContextProfile.readableSetoid

def RawMinimalContextProfile.quotientOrderIso :
    RawMinimalContextProfile.QuotientProfile ≃o
      MinimalContextProfile A Axis Observable

def RawMinimalContextProfile.quotientNormalize :
    RawMinimalContextProfile.QuotientProfile ->
      MinimalContextProfile A Axis Observable

def RawMinimalContextProfile.quotientInf :
    RawMinimalContextProfile.QuotientProfile ->
      RawMinimalContextProfile.QuotientProfile ->
        RawMinimalContextProfile.QuotientProfile
```

`inf` は support / axis の intersection と observable の union、`top` は object
family 全体 / 全axis / empty observable とする。observable は restriction が反変なため
readable orderとmeetの向きが support / axis と逆になる。

## Target statements

```lean
theorem MinimalContextProfile.readableEquivalence_iff_eq
    (W V : MinimalContextProfile A Axis Observable) :
    (W ≤ V ∧ V ≤ W) ↔ W = V

theorem RawMinimalContextProfile.normalize_inf
    (W V : RawMinimalContextProfile A Axis Observable) :
    normalize (inf W V) = normalize W ⊓ normalize V

theorem RawMinimalContextProfile.readableEquivalent_iff_normalize_eq
    (W V : RawMinimalContextProfile A Axis Observable) :
    readableSetoid W V ↔ normalize W = normalize V

def RawMinimalContextProfile.infBinaryFanIsLimit
    (W V : RawMinimalContextProfile A Axis Observable) :
    IsLimit (infBinaryFan W V)

theorem RawMinimalContextProfile.hasFiniteLimits :
    HasFiniteLimits (RawMinimalContextProfile A Axis Observable)

theorem RawMinimalContextProfile.quotientNormalize_inf
    (W V : RawMinimalContextProfile.QuotientProfile) :
    quotientNormalize (quotientInf W V) =
      quotientNormalize W ⊓ quotientNormalize V

theorem RawMinimalContextProfile.quotient_hasFiniteLimits :
    HasFiniteLimits RawMinimalContextProfile.QuotientProfile

theorem MinimalContextProfile.hom_subsingleton
    (W V : MinimalContextProfile A Axis Observable) :
    Subsingleton (W ⟶ V)

theorem MinimalContextProfile.readableContextHom_subsingleton
    (W V : MinimalContextProfile A Axis Observable) :
    Subsingleton (ReadableContextHom W V)

theorem MinimalContextProfile.hasFiniteLimits :
    HasFiniteLimits (MinimalContextProfile A Axis Observable)

theorem MinimalContextProfile.pullback_eq_inf
    {base left right : MinimalContextProfile A Axis Observable}
    (hl : left ⟶ base) (hr : right ⟶ base) :
    pullback hl hr = left ⊓ right

theorem MinimalContextProfile.homToContextMorphism_isRestriction
    {W V : MinimalContextProfile A Axis Observable} (f : W ⟶ V) :
    (homToContextMorphism f).IsRestriction

theorem MinimalContextProfile.inf_eq_inf_of_mutual_readability
    {W W' V V' : MinimalContextProfile A Axis Observable}
    (hW : W ≤ W' ∧ W' ≤ W) (hV : V ≤ V' ∧ V' ≤ V) :
    W ⊓ V = W' ⊓ V'
```

## Premise classification

- `A`, `Axis`, `Observable`, selected profiles, `hl`, `hr`: 本文由来。
- `PartialOrder`, `SemilatticeInf`, `OrderTop`: componentwise definitionsから放電。
- raw preorder / quotient: index presentationのrange包含からpreorderを構成し、
  mutual readability quotientとextensional normal formのorder同値を証明する。
- raw categorical surface: raw `inf`をapexとするbinary product coneを証明し、
  finite diagramのextensional infimumをcanonical raw presentationへ戻すlimit coneから
  quotient前preorder categoryの`HasFiniteLimits`を構成する。
- quotient meet: raw index presentation上のintersection / sum構成をquotientへ
  降下させ、normalizationがmeetを保存することを証明する。
- actual hom thinness: selected subtype間の各mapがunderlying valueを保存することから
  function extensionalityで証明する。morphism全体がcanonicalであるというfieldは持たない。
- finite limits / categorical pullback: Mathlib `CategoryTheory.Limits.Lattice`から放電。
- legacy restriction: actual selected homのmapを既存`ContextMorphism`へ渡し、
  value preservationから`IsRestriction`を証明する。

新規の結論相当certificate fieldは導入しない。非退化発火は
`Formal/AG/Examples/FiniteModel.lean` の異なるPUnit / Bool index presentationが
rawでは非等号、quotientでは等号、そのdescended meetが一致することに加え、
相異なるnonempty profile、そのmeet、topへのcospanのpullback、actual selected hom、
legacy restriction comparisonで検査する。
