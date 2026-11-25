import Formal.SHIGURE.Part2.Recovery.ConstantFormulas
import Formal.SHIGURE.Part2.AffineFoundations

/-!
# A disjunction satisfied locally on a product spectrum

The two labels of the point are assigned on the complementary clopen
pieces cut out by the idempotent `(1, 0)`. Each piece has a point as soon
as the original coefficient ring is nonzero.
-/

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
universe u

noncomputable section

namespace SHIGURE.Copying

/-- The two designated values live in the same universe as the coefficient ring. -/
def twoValueSignature : Signature.{u} where
  SortType := PUnit.{u + 1}
  Total := ULift.{u} Bool
  Rel := PEmpty
  Partial := PEmpty
  Quantity := PEmpty
  totalArity _ := ⟨[], PUnit.unit⟩
  relInputs r := nomatch r
  partialArity p := nomatch p
  quantityArity q := nomatch q

/-- The Boolean state set with the two original designated values. -/
def twoValueStructure : Structure twoValueSignature.{u} where
  carrier _ := ULift.{u} Bool
  total b _ := b
  relation r := nomatch r
  partialDomain p := nomatch p
  partialValue p := nomatch p
  quantity q := nomatch q

/-- The atom saying that the one input equals one of the designated values. -/
def equalDesignated (b : Bool) : Formula twoValueSignature.{u} [PUnit.unit] :=
  .atom (.graph (.total (ULift.up b)) (fun i => nomatch i) .here)

/-- The native and sheaf readings of the law that the state equals a designated value. -/
def twoValueLaw : Law twoValueSignature.{u} :=
  ⟨[PUnit.unit], .truth, (equalDesignated false).disj (equalDesignated true)⟩

/-- Every native Boolean state satisfies one of the two graph atoms. -/
theorem twoValueLaw_native : twoValueLaw.{u}.Holds twoValueStructure.{u} := by
  intro a _
  change (equalDesignated false).Holds twoValueStructure a ∨ (equalDesignated true).Holds twoValueStructure a
  simp only [equalDesignated, Formula.holds_atom, Atomic.holds_graph, Structure.graph_total_iff]
  change (ULift.up false : ULift.{u} Bool) = a.get Var.here ∨ ULift.up true = a.get Var.here
  rcases (a.get Var.here : ULift.{u} Bool) with ⟨b⟩
  cases b
  · exact Or.inl rfl
  · exact Or.inr rfl

variable (k : Type u) [CommRing k]

/-- The affine product spectrum of the local disjunction example. -/
abbrev productSpectrum := Spec (CommRingCat.of (k × k))

/-- The clopen component whose prime ideal does not contain `(1, 0)`. -/
private def firstComponent : Clopens (productSpectrum k) :=
  clopenOfIdempotent ⟨(1, 0), by show ((1, 0) : k × k) * (1, 0) = (1, 0); simp⟩

/-- The locally constant state chooses the true label exactly on the first component. -/
def productChoice : LocallyConstant (productSpectrum k) Bool where
  toFun x := by classical exact if x ∈ firstComponent k then true else false
  isLocallyConstant := by
    classical
    apply IsLocallyConstant.iff_isOpen_fiber.mpr
    intro b
    cases b
    · convert (firstComponent k).isClosed.isOpen_compl using 1
      ext x
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_compl_iff]
      by_cases h : x ∈ firstComponent k <;> simp [h]
    · convert (firstComponent k).isOpen using 1
      ext x
      simp only [Set.mem_preimage, Set.mem_singleton_iff]
      by_cases h : x ∈ firstComponent k <;> simp [h]

/-- The two fibers of the chosen state form an open cover. -/
def productChoiceOpens (b : Bool) : (productSpectrum k).Opens :=
  ⟨(productChoice k) ⁻¹' {b}, (productChoice k).isLocallyConstant {b}⟩

/-- The two open fibers cover the entire coefficient spectrum. -/
theorem productChoice_isOpenCover : IsOpenCover (productChoiceOpens k) := by
  apply top_unique
  intro x _
  exact Opens.mem_iSup.mpr ⟨productChoice k x, rfl⟩

/-- The section has the single indicated label on its open fiber. -/
theorem productChoice_onOpen (b : Bool) (x : (productChoiceOpens k b).toScheme) :
    productChoice k ((productChoiceOpens k b).ι x) = b :=
  x.property

/-- A native prime gives two primes that see the two different labels. -/
private theorem productChoice_two_labels [Nontrivial k] : ∃ x y : productSpectrum k,
    productChoice k x = true ∧ productChoice k y = false := by
  classical
  obtain ⟨z⟩ := (inferInstance : Nonempty (PrimeSpectrum k))
  let x := PrimeSpectrum.comap (RingHom.fst k k) z
  let y := PrimeSpectrum.comap (RingHom.snd k k) z
  have hx : x ∈ firstComponent k := by
    change x ∈ (firstComponent k : Set (productSpectrum k))
    rw [firstComponent, coe_clopenOfIdempotent]
    change (1 : k) ∉ z.asIdeal
    exact fun h => z.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ h isUnit_one)
  have hy : y ∉ firstComponent k := by
    change y ∉ (firstComponent k : Set (productSpectrum k))
    rw [firstComponent, coe_clopenOfIdempotent]
    change ¬ ((0 : k) ∉ z.asIdeal)
    exact fun h => h (Ideal.zero_mem _)
  exact ⟨x, y, if_pos hx, if_neg hy⟩

/-- The chosen point is different from both global constant points over a nonzero base. -/
theorem productChoice_notConstant [Nontrivial k] (b : Bool) :
    productChoice k ≠ LocallyConstant.const (productSpectrum k) b := by
  obtain ⟨x, y, hx, hy⟩ := productChoice_two_labels k
  intro h
  have h₁ : productChoice k x = b := DFunLike.congr_fun h x
  have h₂ : productChoice k y = b := DFunLike.congr_fun h y
  exact Bool.noConfusion (hx.symm.trans (h₁.trans (h₂.symm.trans hy)))

/-- The same theory Law holds in the actual relative sheaf semantics of the product spectrum. -/
theorem productChoice_law :
    (constantStructure (productSpectrum k) twoValueStructure).holdsLaw twoValueLaw :=
  constantStructure_holdsLaw twoValueStructure twoValueLaw twoValueLaw_native

/-- The chosen global section supplies a satisfying assignment for the local disjunction. -/
theorem productChoice_satisfies :
    let U : Over (productSpectrum k) := Over.mk (𝟙 (productSpectrum k))
    let A := constantStructure (productSpectrum k) twoValueStructure
    let a : (sheafTuple A.carrier [PUnit.unit]).val.obj (op U) := ⟨fun | .here => LocallyConstant.map ULift.up (productChoice k)⟩
    a ∈ (A.interpretFormula twoValueLaw.conclusion).carrier.obj (op U) := by
  intro U A a
  exact productChoice_law k (op U) (SheafPredicate.mem_truth _ _)

/-- Neither atom holds on the entire coefficient scheme at the chosen section. -/
theorem productChoice_no_global_disjunct [Nontrivial k] (b : Bool) :
    let U : Over (productSpectrum k) := Over.mk (𝟙 (productSpectrum k))
    let A := constantStructure (productSpectrum k) twoValueStructure
    let a : (sheafTuple A.carrier [PUnit.unit]).val.obj (op U) := ⟨fun | .here => LocallyConstant.map ULift.up (productChoice k)⟩
    a ∉ (A.interpretFormula (equalDesignated b)).carrier.obj (op U) := by
  intro U A a h
  apply productChoice_notConstant k b
  apply LocallyConstant.ext
  intro x
  have h' := (mem_constantFormula_iff twoValueStructure (equalDesignated b) a).mp h x
  simp only [equalDesignated, Formula.holds_atom, Atomic.holds_graph, Structure.graph_total_iff] at h'
  exact (congrArg ULift.down h').symm

/-- The disjunct selected by an open fiber holds on that entire open subscheme. -/
theorem productChoice_disjunct_onOpen (b : Bool) :
    let S := productSpectrum k
    let T : Over S := Over.mk (𝟙 S)
    let U : Over S := Over.mk ((productChoiceOpens k b).ι ≫ 𝟙 S)
    let f : U ⟶ T := Over.homMk (productChoiceOpens k b).ι
    let A := constantStructure S twoValueStructure
    let a : (sheafTuple A.carrier [PUnit.unit]).val.obj (op T) := ⟨fun | .here => LocallyConstant.map ULift.up (productChoice k)⟩
    (sheafTuple A.carrier [PUnit.unit]).val.map f.op a ∈
      (A.interpretFormula (equalDesignated b)).carrier.obj (op U) := by
  intro S T U f A a
  apply (mem_constantFormula_iff twoValueStructure (equalDesignated b) _).mpr
  intro x
  rw [nativeAssignmentAt_restrict]
  simp only [equalDesignated, Formula.holds_atom, Atomic.holds_graph, Structure.graph_total_iff]
  exact congrArg ULift.up (productChoice_onOpen k b x).symm

end SHIGURE.Copying
