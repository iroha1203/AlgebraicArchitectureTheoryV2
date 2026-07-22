import Formal.AG.SemanticRepair.SiteCech

noncomputable section

namespace AAT.AG
namespace SemanticRepair

open CategoryTheory

universe u v w x y z r

/-! ## X.§7 theorem 7.2 semantic additive H1 / cover-relative H1 comparison -/

/--
X.定義7.1: finite-free additive semantic H1 surface used by theorem 7.2.

This is the comparison-level quotient surface.  It deliberately does not
require chart finiteness, cochain finiteness, finite-dimensionality, or a
semantic repair cover.  Finite cover data belongs to the bounded §4 surface
and concrete instances, not to the general H1 comparison theorem.

The additive regime covers all three displayed degrees: `C2` carries its
coefficient group and `delta1` is additive, so degree-one cocycles are closed
under the group operations and `H1` below is a genuine quotient group rather
than a bare quotient set.
-/
structure SemanticRepairAdditiveH1Surface where
  C0 : Type y
  C1 : Type x
  C2 : Type z
  zero1 : C1
  zero2 : C2
  delta0 : C0 -> C1
  delta1 : C1 -> C2
  residual : C1
  [c0AddCommGroup : AddCommGroup C0]
  [c1AddCommGroup : AddCommGroup C1]
  [c2AddCommGroup : AddCommGroup C2]
  zero1_eq_zero : zero1 = 0
  zero2_eq_zero : zero2 = 0
  delta0_zero : delta0 0 = 0
  delta0_add : forall left right, delta0 (left + right) = delta0 left + delta0 right
  delta0_neg : forall primitive, delta0 (-primitive) = -delta0 primitive
  delta1_add : forall left right, delta1 (left + right) = delta1 left + delta1 right
  delta1_neg : forall cochain, delta1 (-cochain) = -delta1 cochain
  zero1_cocycle : delta1 zero1 = zero2
  delta1_delta0_eq_zero : forall primitive, delta1 (delta0 primitive) = zero2
  residual_cocycle : delta1 residual = zero2

namespace SemanticRepairAdditiveH1Surface

attribute [instance] c0AddCommGroup c1AddCommGroup c2AddCommGroup

/-- X.定義7.1: the degree-one differential kills the group zero. -/
theorem delta1_zero (data : SemanticRepairAdditiveH1Surface) :
    data.delta1 0 = 0 := by
  have h := data.zero1_cocycle
  rw [data.zero1_eq_zero, data.zero2_eq_zero] at h
  exact h

/-- X.定理7.2: finite-free semantic 1-cocycles. -/
def Cocycle (data : SemanticRepairAdditiveH1Surface) :=
  { cochain : data.C1 // data.delta1 cochain = data.zero2 }

/-- X.定理7.2: finite-free semantic same-class relation. -/
def Cohomologous
    (data : SemanticRepairAdditiveH1Surface)
    (left right : data.Cocycle) : Prop :=
  letI := data.c1AddCommGroup
  exists primitive, left.1 - right.1 = data.delta0 primitive

/-- X.定理7.2: semantic same-class is reflexive. -/
theorem cohomologous_refl
    (data : SemanticRepairAdditiveH1Surface)
    (cochain : data.Cocycle) :
    data.Cohomologous cochain cochain := by
  letI := data.c0AddCommGroup
  letI := data.c1AddCommGroup
  refine ⟨0, ?_⟩
  change cochain.1 - cochain.1 = data.delta0 0
  rw [data.delta0_zero]
  simp

/-- X.定理7.2: semantic same-class is symmetric. -/
theorem cohomologous_symm
    (data : SemanticRepairAdditiveH1Surface)
    {left right : data.Cocycle} :
    data.Cohomologous left right -> data.Cohomologous right left := by
  letI := data.c0AddCommGroup
  letI := data.c1AddCommGroup
  intro h
  rcases h with ⟨primitive, hprimitive⟩
  refine ⟨-primitive, ?_⟩
  calc
    right.1 - left.1 = -(left.1 - right.1) := by abel
    _ = -(data.delta0 primitive) := by rw [hprimitive]
    _ = data.delta0 (-primitive) := by rw [← data.delta0_neg primitive]

/-- X.定理7.2: semantic same-class is transitive. -/
theorem cohomologous_trans
    (data : SemanticRepairAdditiveH1Surface)
    {left middle right : data.Cocycle} :
    data.Cohomologous left middle ->
      data.Cohomologous middle right ->
        data.Cohomologous left right := by
  letI := data.c0AddCommGroup
  letI := data.c1AddCommGroup
  intro hleft hright
  rcases hleft with ⟨leftPrimitive, hleftPrimitive⟩
  rcases hright with ⟨rightPrimitive, hrightPrimitive⟩
  refine ⟨leftPrimitive + rightPrimitive, ?_⟩
  calc
    left.1 - right.1 =
        (left.1 - middle.1) + (middle.1 - right.1) := by abel
    _ = data.delta0 leftPrimitive + data.delta0 rightPrimitive := by
      rw [hleftPrimitive, hrightPrimitive]
    _ = data.delta0 (leftPrimitive + rightPrimitive) := by
      rw [← data.delta0_add leftPrimitive rightPrimitive]

/-- X.定理7.2: setoid for the finite-free semantic additive H1 quotient. -/
def setoid (data : SemanticRepairAdditiveH1Surface) :
    Setoid data.Cocycle where
  r := data.Cohomologous
  iseqv := ⟨data.cohomologous_refl, data.cohomologous_symm,
    data.cohomologous_trans⟩

/-- X.定理7.2: finite-free semantic additive H1 quotient. -/
def H1 (data : SemanticRepairAdditiveH1Surface) :=
  Quotient data.setoid

/-- X.定理7.2: selected residual class in semantic additive H1. -/
def residualClass (data : SemanticRepairAdditiveH1Surface) :
    data.H1 :=
  Quotient.mk data.setoid ⟨data.residual, data.residual_cocycle⟩

/-- X.定理7.2: zero class in semantic additive H1. -/
def zeroClass (data : SemanticRepairAdditiveH1Surface) :
    data.H1 :=
  Quotient.mk data.setoid ⟨data.zero1, data.zero1_cocycle⟩

/-- X.定理7.2: selected residual class vanishes in semantic additive H1. -/
def H1Zero (data : SemanticRepairAdditiveH1Surface) : Prop :=
  data.residualClass = data.zeroClass

/-- X.定理7.2: `delta1` kills natural-number multiples of cocycle values. -/
theorem delta1_nsmul (data : SemanticRepairAdditiveH1Surface)
    (n : Nat) (cochain : data.C1)
    (hcochain : data.delta1 cochain = data.zero2) :
    data.delta1 (n • cochain) = data.zero2 := by
  induction n with
  | zero =>
      rw [zero_nsmul, data.delta1_zero, data.zero2_eq_zero]
  | succ n ih =>
      rw [succ_nsmul, data.delta1_add, ih, hcochain, data.zero2_eq_zero,
        add_zero]

/-- X.定理7.2: `delta1` kills integer multiples of cocycle values. -/
theorem delta1_zsmul (data : SemanticRepairAdditiveH1Surface)
    (n : Int) (cochain : data.C1)
    (hcochain : data.delta1 cochain = data.zero2) :
    data.delta1 (n • cochain) = data.zero2 := by
  cases n with
  | ofNat m =>
      rw [Int.ofNat_eq_natCast, natCast_zsmul]
      exact data.delta1_nsmul m cochain hcochain
  | negSucc m =>
      rw [negSucc_zsmul, data.delta1_neg,
        data.delta1_nsmul (m + 1) cochain hcochain, data.zero2_eq_zero,
        neg_zero]

/-- X.定理7.2: `delta0` commutes with natural-number multiples. -/
theorem delta0_nsmul (data : SemanticRepairAdditiveH1Surface)
    (n : Nat) (primitive : data.C0) :
    data.delta0 (n • primitive) = n • data.delta0 primitive := by
  induction n with
  | zero =>
      rw [zero_nsmul, zero_nsmul, data.delta0_zero]
  | succ n ih =>
      rw [succ_nsmul, succ_nsmul, data.delta0_add, ih]

/-- X.定理7.2: `delta0` commutes with integer multiples. -/
theorem delta0_zsmul (data : SemanticRepairAdditiveH1Surface)
    (n : Int) (primitive : data.C0) :
    data.delta0 (n • primitive) = n • data.delta0 primitive := by
  cases n with
  | ofNat m =>
      rw [Int.ofNat_eq_natCast, natCast_zsmul, natCast_zsmul,
        data.delta0_nsmul]
  | negSucc m =>
      rw [negSucc_zsmul, negSucc_zsmul, data.delta0_neg, data.delta0_nsmul]

/-- X.定理7.2: zero is a semantic 1-cocycle. -/
instance cocycleZero (data : SemanticRepairAdditiveH1Surface) :
    Zero data.Cocycle :=
  ⟨⟨0, by rw [data.delta1_zero, data.zero2_eq_zero]⟩⟩

/-- X.定理7.2: semantic 1-cocycles are closed under addition. -/
instance cocycleAdd (data : SemanticRepairAdditiveH1Surface) :
    Add data.Cocycle :=
  ⟨fun left right =>
    ⟨left.1 + right.1, by
      rw [data.delta1_add left.1 right.1, left.2, right.2, data.zero2_eq_zero,
        add_zero]⟩⟩

/-- X.定理7.2: semantic 1-cocycles are closed under negation. -/
instance cocycleNeg (data : SemanticRepairAdditiveH1Surface) :
    Neg data.Cocycle :=
  ⟨fun cochain =>
    ⟨-cochain.1, by
      rw [data.delta1_neg cochain.1, cochain.2, data.zero2_eq_zero,
        neg_zero]⟩⟩

/-- X.定理7.2: semantic 1-cocycles are closed under subtraction. -/
instance cocycleSub (data : SemanticRepairAdditiveH1Surface) :
    Sub data.Cocycle :=
  ⟨fun left right =>
    ⟨left.1 - right.1, by
      rw [sub_eq_add_neg, data.delta1_add, data.delta1_neg, left.2, right.2,
        data.zero2_eq_zero, neg_zero, add_zero]⟩⟩

/-- X.定理7.2: semantic 1-cocycles are closed under natural multiples. -/
instance cocycleSMulNat (data : SemanticRepairAdditiveH1Surface) :
    SMul Nat data.Cocycle :=
  ⟨fun n cochain => ⟨n • cochain.1, data.delta1_nsmul n cochain.1 cochain.2⟩⟩

/-- X.定理7.2: semantic 1-cocycles are closed under integer multiples. -/
instance cocycleSMulInt (data : SemanticRepairAdditiveH1Surface) :
    SMul Int data.Cocycle :=
  ⟨fun n cochain => ⟨n • cochain.1, data.delta1_zsmul n cochain.1 cochain.2⟩⟩

/--
X.定理7.2: semantic 1-cocycles form an abelian group because `delta1` is
additive and kills zero; the group laws transfer along the injective value
map.
-/
instance cocycleAddCommGroup (data : SemanticRepairAdditiveH1Surface) :
    AddCommGroup data.Cocycle :=
  Function.Injective.addCommGroup
    (fun cochain : data.Cocycle => cochain.1) Subtype.val_injective
    rfl (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl)

/-- X.定理7.2: the zero of semantic additive H1 is the selected zero class. -/
instance h1Zero (data : SemanticRepairAdditiveH1Surface) : Zero data.H1 :=
  ⟨data.zeroClass⟩

/-- X.定理7.2: addition descends to semantic additive H1. -/
instance h1Add (data : SemanticRepairAdditiveH1Surface) : Add data.H1 :=
  ⟨fun left right =>
    Quotient.liftOn₂ left right
      (fun x y => Quotient.mk data.setoid (x + y))
      (by
        intro x y x' y' hx hy
        rcases hx with ⟨p, hp⟩
        rcases hy with ⟨q, hq⟩
        apply Quotient.sound
        refine ⟨p + q, ?_⟩
        change (x.1 + y.1) - (x'.1 + y'.1) = data.delta0 (p + q)
        rw [data.delta0_add, ← hp, ← hq]
        abel)⟩

/-- X.定理7.2: negation descends to semantic additive H1. -/
instance h1Neg (data : SemanticRepairAdditiveH1Surface) : Neg data.H1 :=
  ⟨fun cocycleClass =>
    Quotient.liftOn cocycleClass
      (fun x => Quotient.mk data.setoid (-x))
      (by
        intro x x' hx
        rcases hx with ⟨p, hp⟩
        apply Quotient.sound
        refine ⟨-p, ?_⟩
        change -x.1 - -x'.1 = data.delta0 (-p)
        rw [data.delta0_neg, ← hp]
        abel)⟩

/-- X.定理7.2: subtraction on semantic additive H1. -/
instance h1Sub (data : SemanticRepairAdditiveH1Surface) : Sub data.H1 :=
  ⟨fun left right => left + -right⟩

/-- X.定理7.2: natural multiples descend to semantic additive H1. -/
instance h1SMulNat (data : SemanticRepairAdditiveH1Surface) :
    SMul Nat data.H1 :=
  ⟨fun n cocycleClass =>
    Quotient.liftOn cocycleClass
      (fun x => Quotient.mk data.setoid (n • x))
      (by
        intro x x' hx
        rcases hx with ⟨p, hp⟩
        apply Quotient.sound
        refine ⟨n • p, ?_⟩
        change n • x.1 - n • x'.1 = data.delta0 (n • p)
        rw [← smul_sub, hp, data.delta0_nsmul])⟩

/-- X.定理7.2: integer multiples descend to semantic additive H1. -/
instance h1SMulInt (data : SemanticRepairAdditiveH1Surface) :
    SMul Int data.H1 :=
  ⟨fun n cocycleClass =>
    Quotient.liftOn cocycleClass
      (fun x => Quotient.mk data.setoid (n • x))
      (by
        intro x x' hx
        rcases hx with ⟨p, hp⟩
        apply Quotient.sound
        refine ⟨n • p, ?_⟩
        change n • x.1 - n • x'.1 = data.delta0 (n • p)
        rw [← smul_sub, hp, data.delta0_zsmul])⟩

/--
X.定理7.2: semantic additive H1 is a quotient group.  The group laws transfer
along the surjective quotient map from the cocycle group, and the zero of the
group is the selected zero class.
-/
instance h1AddCommGroup (data : SemanticRepairAdditiveH1Surface) :
    AddCommGroup data.H1 :=
  Function.Surjective.addCommGroup (Quotient.mk data.setoid)
    (fun cocycleClass =>
      Quotient.inductionOn cocycleClass fun x => ⟨x, rfl⟩)
    (congrArg (Quotient.mk data.setoid)
      (Subtype.ext data.zero1_eq_zero.symm))
    (fun _ _ => rfl) (fun _ => rfl)
    (fun left right =>
      congrArg (Quotient.mk data.setoid)
        (Subtype.ext (sub_eq_add_neg left.1 right.1)))
    (fun _ _ => rfl) (fun _ _ => rfl)

/-- X.定理7.2: the selected zero class is the zero of the H1 group. -/
theorem zeroClass_eq_zero (data : SemanticRepairAdditiveH1Surface) :
    data.zeroClass = (0 : data.H1) :=
  rfl

/-- X.定理7.2: H1 vanishing is vanishing of the residual class in the group. -/
theorem h1Zero_iff_residualClass_eq_zero
    (data : SemanticRepairAdditiveH1Surface) :
    data.H1Zero <-> data.residualClass = (0 : data.H1) :=
  Iff.rfl

end SemanticRepairAdditiveH1Surface

/--
X.定義7.1: cochain-level comparison between semantic additive Cech data and a
selected cover-relative Cech complex.

The fields are degree-wise carrier equivalences and differential
compatibility.  The structure does not store quotient-level `H1` maps,
zero-class equality, global coherence, sheaf descent, or later law-grounded
conclusions.
-/
structure SemanticRepairCoverRelativeH1Comparison
    (additive : SemanticRepairAdditiveH1Surface.{y, x, z})
    {U : AtomCarrier.{r}} {A : ArchitectureObject U}
    {S : Site.AATSite A}
    {cover : Cohomology.CoverRelativeCechCover S}
    {Ob : Cohomology.ObstructionSheaf S}
    (K : Cohomology.CoverRelativeCechComplex cover Ob) where
  c0Equiv :
    letI := additive.c0AddCommGroup
    letI := K.cochainAddCommGroup 0
    additive.C0 ≃+ K.Cn 0
  c1Equiv :
    letI := additive.c1AddCommGroup
    letI := K.cochainAddCommGroup 1
    additive.C1 ≃+ K.Cn 1
  c2Equiv : additive.C2 ≃ K.Cn 2
  c2Equiv_zero :
    letI := K.cochainAddCommGroup 2
    c2Equiv additive.zero2 = 0
  c2Equiv_symm_zero :
    letI := K.cochainAddCommGroup 2
    c2Equiv.symm 0 = additive.zero2
  d0_to :
    letI := additive.c0AddCommGroup
    letI := additive.c1AddCommGroup
    letI := K.cochainAddCommGroup 0
    letI := K.cochainAddCommGroup 1
    forall primitive : additive.C0,
      K.d 0 (c0Equiv primitive) = c1Equiv (additive.delta0 primitive)
  d0_from :
    letI := additive.c0AddCommGroup
    letI := additive.c1AddCommGroup
    letI := K.cochainAddCommGroup 0
    letI := K.cochainAddCommGroup 1
    forall primitive : K.Cn 0,
      additive.delta0 (c0Equiv.symm primitive) =
        c1Equiv.symm (K.d 0 primitive)
  d1_to :
    letI := additive.c1AddCommGroup
    letI := K.cochainAddCommGroup 1
    forall cochain : additive.C1,
      K.d 1 (c1Equiv cochain) = c2Equiv (additive.delta1 cochain)
  d1_from :
    letI := additive.c1AddCommGroup
    letI := K.cochainAddCommGroup 1
    forall cochain : K.Cn 1,
      additive.delta1 (c1Equiv.symm cochain) =
        c2Equiv.symm (K.d 1 cochain)

/--
X.定義7.1: stronger cochain-realization provenance for the selected
semantic/cover-relative comparison.

This is lower than the `H1` comparison surface: it records only degree-wise
carrier realization and differential compatibility.  The `toH1Comparison`
definition below generates the theorem-level comparison; no quotient result is
stored in this structure.
-/
structure SemanticRepairCoverRelativeCochainRealization
    (additive : SemanticRepairAdditiveH1Surface.{y, x, z})
    {U : AtomCarrier.{r}} {A : ArchitectureObject U}
    {S : Site.AATSite A}
    {cover : Cohomology.CoverRelativeCechCover S}
    {Ob : Cohomology.ObstructionSheaf S}
    (K : Cohomology.CoverRelativeCechComplex cover Ob) where
  c0Equiv :
    letI := additive.c0AddCommGroup
    letI := K.cochainAddCommGroup 0
    additive.C0 ≃+ K.Cn 0
  c1Equiv :
    letI := additive.c1AddCommGroup
    letI := K.cochainAddCommGroup 1
    additive.C1 ≃+ K.Cn 1
  c2Equiv : additive.C2 ≃ K.Cn 2
  c2Equiv_zero :
    letI := K.cochainAddCommGroup 2
    c2Equiv additive.zero2 = 0
  c2Equiv_symm_zero :
    letI := K.cochainAddCommGroup 2
    c2Equiv.symm 0 = additive.zero2
  d0_to :
    letI := additive.c0AddCommGroup
    letI := additive.c1AddCommGroup
    letI := K.cochainAddCommGroup 0
    letI := K.cochainAddCommGroup 1
    forall primitive : additive.C0,
      K.d 0 (c0Equiv primitive) = c1Equiv (additive.delta0 primitive)
  d0_from :
    letI := additive.c0AddCommGroup
    letI := additive.c1AddCommGroup
    letI := K.cochainAddCommGroup 0
    letI := K.cochainAddCommGroup 1
    forall primitive : K.Cn 0,
      additive.delta0 (c0Equiv.symm primitive) =
        c1Equiv.symm (K.d 0 primitive)
  d1_to :
    letI := additive.c1AddCommGroup
    letI := K.cochainAddCommGroup 1
    forall cochain : additive.C1,
      K.d 1 (c1Equiv cochain) = c2Equiv (additive.delta1 cochain)
  d1_from :
    letI := additive.c1AddCommGroup
    letI := K.cochainAddCommGroup 1
    forall cochain : K.Cn 1,
      additive.delta1 (c1Equiv.symm cochain) =
        c2Equiv.symm (K.d 1 cochain)

namespace SemanticRepairCoverRelativeCochainRealization

variable {additive : SemanticRepairAdditiveH1Surface.{y, x, z}}
variable {U : AtomCarrier.{r}} {A : ArchitectureObject U}
variable {S : Site.AATSite A}
variable {cover : Cohomology.CoverRelativeCechCover S}
variable {Ob : Cohomology.ObstructionSheaf S}
variable {K : Cohomology.CoverRelativeCechComplex cover Ob}

/-- X.定義7.1: generate the H1 comparison surface from cochain realization. -/
def toH1Comparison
    (realization : SemanticRepairCoverRelativeCochainRealization additive K) :
    SemanticRepairCoverRelativeH1Comparison additive K where
  c0Equiv := realization.c0Equiv
  c1Equiv := realization.c1Equiv
  c2Equiv := realization.c2Equiv
  c2Equiv_zero := realization.c2Equiv_zero
  c2Equiv_symm_zero := realization.c2Equiv_symm_zero
  d0_to := realization.d0_to
  d0_from := realization.d0_from
  d1_to := realization.d1_to
  d1_from := realization.d1_from

end SemanticRepairCoverRelativeCochainRealization

namespace SemanticRepairCoverRelativeH1Comparison

variable {additive : SemanticRepairAdditiveH1Surface.{y, x, z}}
variable {U : AtomCarrier.{r}} {A : ArchitectureObject U}
variable {S : Site.AATSite A}
variable {cover : Cohomology.CoverRelativeCechCover S}
variable {Ob : Cohomology.ObstructionSheaf S}
variable {K : Cohomology.CoverRelativeCechComplex cover Ob}

/-- X.定理7.2: semantic cocycles map to cover-relative degree-one cocycles. -/
def toCoverRelativeCocycle
    (comparison : SemanticRepairCoverRelativeH1Comparison additive K)
    (cocycle : additive.Cocycle) :
    K.CechCocycle 1 := by
  refine ⟨comparison.c1Equiv cocycle.1, ?_⟩
  rw [comparison.d1_to cocycle.1, cocycle.2, comparison.c2Equiv_zero]

/-- X.定理7.2: cover-relative degree-one cocycles map back to semantic cocycles. -/
def fromCoverRelativeCocycle
    (comparison : SemanticRepairCoverRelativeH1Comparison additive K)
    (cocycle : K.CechCocycle 1) :
    additive.Cocycle := by
  letI := additive.c1AddCommGroup
  refine ⟨comparison.c1Equiv.symm cocycle.1, ?_⟩
  change additive.delta1 (comparison.c1Equiv.symm cocycle.1) = additive.zero2
  rw [comparison.d1_from cocycle.1, cocycle.2, comparison.c2Equiv_symm_zero]

/--
X.定理7.2: semantic same-class is equivalent to the selected cover-relative
coboundary relation in degree one.
-/
theorem semantic_sameClass_iff_coverRelative_sameClass
    (comparison : SemanticRepairCoverRelativeH1Comparison additive K)
    (left right : additive.Cocycle) :
    additive.Cohomologous left right <->
      (K.CechCoboundarySetoidSucc 0).r
        (comparison.toCoverRelativeCocycle left)
        (comparison.toCoverRelativeCocycle right) := by
  letI := additive.c0AddCommGroup
  letI := additive.c1AddCommGroup
  letI := K.cochainAddCommGroup 0
  letI := K.cochainAddCommGroup 1
  constructor
  · intro hsame
    rcases hsame with ⟨primitive, hprimitive⟩
    refine ⟨comparison.c0Equiv primitive, ?_⟩
    calc
      comparison.c1Equiv left.1 - comparison.c1Equiv right.1 =
          comparison.c1Equiv (left.1 - right.1) := by
            rw [map_sub]
      _ = comparison.c1Equiv (additive.delta0 primitive) := by
            rw [hprimitive]
      _ = K.d 0 (comparison.c0Equiv primitive) := by
            rw [comparison.d0_to]
  · intro hcover
    rcases hcover with ⟨primitive, hprimitive⟩
    refine ⟨comparison.c0Equiv.symm primitive, ?_⟩
    apply comparison.c1Equiv.injective
    calc
      comparison.c1Equiv (left.1 - right.1) =
          comparison.c1Equiv left.1 - comparison.c1Equiv right.1 := by
            rw [map_sub]
      _ = K.d 0 primitive := hprimitive
      _ = comparison.c1Equiv
            (comparison.c1Equiv.symm (K.d 0 primitive)) := by
            rw [comparison.c1Equiv.apply_symm_apply]
      _ = comparison.c1Equiv
            (additive.delta0 (comparison.c0Equiv.symm primitive)) := by
            rw [comparison.d0_from]

/-- X.定理7.2: generated map from semantic additive H1 to cover-relative H1. -/
def toCoverRelativeH1
    (comparison : SemanticRepairCoverRelativeH1Comparison additive K) :
    additive.H1 -> K.CechCohomologySucc 0 :=
  Quotient.lift
    (fun cocycle =>
      K.cohomologyClassSucc 0 (comparison.toCoverRelativeCocycle cocycle))
    (by
      intro left right hsame
      exact
        Quotient.sound
          ((comparison.semantic_sameClass_iff_coverRelative_sameClass
            left right).1 hsame))

/-- X.定理7.2: generated map from cover-relative H1 back to semantic additive H1. -/
def fromCoverRelativeH1
    (comparison : SemanticRepairCoverRelativeH1Comparison additive K) :
    K.CechCohomologySucc 0 -> additive.H1 :=
  Quotient.lift
    (fun cocycle =>
      letI := additive.c1AddCommGroup
      Quotient.mk additive.setoid (comparison.fromCoverRelativeCocycle cocycle))
    (by
      intro left right hsame
      letI := additive.c1AddCommGroup
      have hcover :
          (K.CechCoboundarySetoidSucc 0).r
            (comparison.toCoverRelativeCocycle
              (comparison.fromCoverRelativeCocycle left))
            (comparison.toCoverRelativeCocycle
              (comparison.fromCoverRelativeCocycle right)) := by
        letI := K.cochainAddCommGroup 1
        rcases hsame with ⟨primitive, hprimitive⟩
        refine ⟨primitive, ?_⟩
        change
          comparison.c1Equiv (comparison.c1Equiv.symm left.1) -
              comparison.c1Equiv (comparison.c1Equiv.symm right.1) =
            K.d 0 primitive
        rw [comparison.c1Equiv.apply_symm_apply left.1,
          comparison.c1Equiv.apply_symm_apply right.1]
        exact hprimitive
      exact
        Quotient.sound
          ((comparison.semantic_sameClass_iff_coverRelative_sameClass
            (comparison.fromCoverRelativeCocycle left)
            (comparison.fromCoverRelativeCocycle right)).2 hcover))

/--
X.定理7.2: the generated maps are inverse on the semantic additive H1 quotient.
-/
theorem from_to_semanticH1
    (comparison : SemanticRepairCoverRelativeH1Comparison additive K)
    (h : additive.H1) :
    comparison.fromCoverRelativeH1 (comparison.toCoverRelativeH1 h) = h := by
  refine Quotient.inductionOn h ?_
  intro cocycle
  letI := additive.c0AddCommGroup
  letI := additive.c1AddCommGroup
  apply Quotient.sound
  refine ⟨(0 : additive.C0), ?_⟩
  change
    comparison.c1Equiv.symm (comparison.c1Equiv cocycle.1) - cocycle.1 =
      additive.delta0 0
  rw [comparison.c1Equiv.symm_apply_apply, sub_self, additive.delta0_zero]

/--
X.定理7.2: the generated maps are inverse on the cover-relative H1 quotient.
-/
theorem to_from_coverRelativeH1
    (comparison : SemanticRepairCoverRelativeH1Comparison additive K)
    (h : K.CechCohomologySucc 0) :
    comparison.toCoverRelativeH1 (comparison.fromCoverRelativeH1 h) = h := by
  refine Quotient.inductionOn h ?_
  intro cocycle
  letI := additive.c1AddCommGroup
  apply Quotient.sound
  letI := K.cochainAddCommGroup 0
  letI := K.cochainAddCommGroup 1
  refine ⟨0, ?_⟩
  change
    comparison.c1Equiv (comparison.c1Equiv.symm cocycle.1) - cocycle.1 =
      K.d 0 0
  rw [comparison.c1Equiv.apply_symm_apply cocycle.1]
  simp

/--
X.定理7.2: generated equivalence between semantic additive H1 and
cover-relative Cech H1.
-/
def semanticRepairAdditiveH1_equiv_coverRelativeH1
    (comparison : SemanticRepairCoverRelativeH1Comparison additive K) :
    additive.H1 ≃ K.CechCohomologySucc 0 where
  toFun := comparison.toCoverRelativeH1
  invFun := comparison.fromCoverRelativeH1
  left_inv := comparison.from_to_semanticH1
  right_inv := comparison.to_from_coverRelativeH1

/--
X.定理7.2 結論3: the generated comparison respects addition, so the set-level
equivalence upgrades to an additive group isomorphism onto the additive group
reading of cover-relative Čech H1.
-/
def semanticRepairAdditiveH1_addEquiv_additiveCechH1
    (comparison : SemanticRepairCoverRelativeH1Comparison additive K) :
    additive.H1 ≃+ K.AdditiveCechH1 :=
  { comparison.semanticRepairAdditiveH1_equiv_coverRelativeH1.trans
      K.legacyCechH1EquivAdditiveCechH1 with
    map_add' := by
      intro left right
      refine Quotient.inductionOn₂ left right ?_
      intro x y
      show K.additiveH1Class (comparison.toCoverRelativeCocycle (x + y)) =
        K.additiveH1Class (comparison.toCoverRelativeCocycle x) +
          K.additiveH1Class (comparison.toCoverRelativeCocycle y)
      refine K.additiveH1Class_add_of_val ?_
      change comparison.c1Equiv (x.1 + y.1) =
        comparison.c1Equiv x.1 + comparison.c1Equiv y.1
      exact map_add comparison.c1Equiv x.1 y.1 }

/--
X.定理7.2: residual vanishing is vanishing of its image under the additive
comparison; this regenerates the zero correspondence from the group
isomorphism alone.
-/
theorem h1Zero_iff_addEquiv_residualClass_eq_zero
    (comparison : SemanticRepairCoverRelativeH1Comparison additive K) :
    additive.H1Zero <->
      comparison.semanticRepairAdditiveH1_addEquiv_additiveCechH1
        additive.residualClass = 0 := by
  rw [additive.h1Zero_iff_residualClass_eq_zero]
  constructor
  · intro h
    rw [h]
    exact map_zero _
  · intro h
    have h2 := congrArg
      (comparison.semanticRepairAdditiveH1_addEquiv_additiveCechH1).symm h
    rw [AddEquiv.symm_apply_apply, map_zero] at h2
    exact h2

/-- X.定理7.2: selected residual zero predicate in cover-relative H1. -/
def CoverRelativeResidualH1Zero
    (comparison : SemanticRepairCoverRelativeH1Comparison additive K) : Prop :=
  comparison.toCoverRelativeH1 additive.residualClass =
    comparison.toCoverRelativeH1 additive.zeroClass

/--
X.定理7.2: semantic additive H1 zero is equivalent to selected
cover-relative residual H1 zero.
-/
theorem semanticRepairAdditiveH1Zero_iff_coverRelativeH1Zero
    (comparison : SemanticRepairCoverRelativeH1Comparison additive K) :
    additive.H1Zero <-> comparison.CoverRelativeResidualH1Zero := by
  constructor
  · intro hzero
    exact congrArg comparison.toCoverRelativeH1 hzero
  · intro hzero
    calc
      additive.residualClass =
          comparison.fromCoverRelativeH1
            (comparison.toCoverRelativeH1 additive.residualClass) := by
            rw [comparison.from_to_semanticH1 additive.residualClass]
      _ = comparison.fromCoverRelativeH1
            (comparison.toCoverRelativeH1 additive.zeroClass) := by
            rw [hzero]
      _ = additive.zeroClass := comparison.from_to_semanticH1 additive.zeroClass

/--
X.定理7.2: the legacy zero correspondence is derivable from the additive
comparison: the group isomorphism is injective, so equality of images in the
legacy quotient transfers back to equality of the residual and zero classes.
-/
theorem semanticRepairAdditiveH1Zero_iff_coverRelativeH1Zero_of_addEquiv
    (comparison : SemanticRepairCoverRelativeH1Comparison additive K) :
    additive.H1Zero <-> comparison.CoverRelativeResidualH1Zero := by
  constructor
  · intro hzero
    exact congrArg comparison.toCoverRelativeH1 hzero
  · intro hzero
    have himage :
        comparison.semanticRepairAdditiveH1_addEquiv_additiveCechH1
            additive.residualClass =
          comparison.semanticRepairAdditiveH1_addEquiv_additiveCechH1
            additive.zeroClass := by
      show K.legacyCechH1EquivAdditiveCechH1
          (comparison.toCoverRelativeH1 additive.residualClass) =
        K.legacyCechH1EquivAdditiveCechH1
          (comparison.toCoverRelativeH1 additive.zeroClass)
      rw [hzero]
    exact
      (comparison.semanticRepairAdditiveH1_addEquiv_additiveCechH1).injective
        himage

/--
X.定理7.4: selected cover-relative nonzero residual transfers back to the
semantic additive H1 surface by contraposition of theorem 7.2.
-/
theorem semanticRepairAdditiveH1Nonzero_of_coverRelativeH1Nonzero
    (comparison : SemanticRepairCoverRelativeH1Comparison additive K) :
    ¬ comparison.CoverRelativeResidualH1Zero -> ¬ additive.H1Zero := by
  intro hcover hsemantic
  exact hcover ((comparison.semanticRepairAdditiveH1Zero_iff_coverRelativeH1Zero).1 hsemantic)

/--
X.定理7.4: selected semantic additive nonzero residual transfers to the
cover-relative H1 surface by contraposition of theorem 7.2.
-/
theorem coverRelativeH1Nonzero_of_semanticRepairAdditiveH1Nonzero
    (comparison : SemanticRepairCoverRelativeH1Comparison additive K) :
    ¬ additive.H1Zero -> ¬ comparison.CoverRelativeResidualH1Zero := by
  intro hsemantic hcover
  exact hsemantic ((comparison.semanticRepairAdditiveH1Zero_iff_coverRelativeH1Zero).2 hcover)

/--
X.定理7.2 package: the generated comparison maps, H1 equivalence, additive H1
group isomorphism, same-class equivalence, and zero-predicate equivalence.
-/
structure SemanticRepairAdditiveH1CoverRelativeH1ComparisonPackage
    (comparison : SemanticRepairCoverRelativeH1Comparison additive K) :
    Type (max u v w x y z r) where
  toCoverRelativeH1 : additive.H1 -> K.CechCohomologySucc 0
  fromCoverRelativeH1 : K.CechCohomologySucc 0 -> additive.H1
  h1Equiv : additive.H1 ≃ K.CechCohomologySucc 0
  /-- X.定理7.2 結論3: the additive group isomorphism onto the additive Čech
  H1 reading; this is the group-level upgrade of `h1Equiv`. -/
  h1AddEquiv : additive.H1 ≃+ K.AdditiveCechH1
  sameClass_iff_coverRelative :
    forall left right : additive.Cocycle,
      additive.Cohomologous left right <->
        (K.CechCoboundarySetoidSucc 0).r
          (comparison.toCoverRelativeCocycle left)
          (comparison.toCoverRelativeCocycle right)
  zero_iff_coverRelativeZero :
    additive.H1Zero <-> comparison.CoverRelativeResidualH1Zero

/-- X.定理7.2: construct the comparison package from cochain-level data. -/
def semanticRepairAdditiveH1_coverRelativeH1_comparison_packageData
    (comparison : SemanticRepairCoverRelativeH1Comparison additive K) :
    SemanticRepairAdditiveH1CoverRelativeH1ComparisonPackage comparison where
  toCoverRelativeH1 := comparison.toCoverRelativeH1
  fromCoverRelativeH1 := comparison.fromCoverRelativeH1
  h1Equiv := comparison.semanticRepairAdditiveH1_equiv_coverRelativeH1
  h1AddEquiv := comparison.semanticRepairAdditiveH1_addEquiv_additiveCechH1
  sameClass_iff_coverRelative := by
    intro left right
    exact comparison.semantic_sameClass_iff_coverRelative_sameClass left right
  zero_iff_coverRelativeZero :=
    comparison.semanticRepairAdditiveH1Zero_iff_coverRelativeH1Zero

/--
X.定理7.2: semantic additive H1 and cover-relative H1 agree under the selected
cochain-level comparison.
-/
theorem semanticRepairAdditiveH1_coverRelativeH1_comparison_package
    (comparison : SemanticRepairCoverRelativeH1Comparison additive K) :
    Nonempty (SemanticRepairAdditiveH1CoverRelativeH1ComparisonPackage comparison) :=
  ⟨comparison.semanticRepairAdditiveH1_coverRelativeH1_comparison_packageData⟩

end SemanticRepairCoverRelativeH1Comparison

end SemanticRepair
end AAT.AG
