import ResearchLean.AG.LocalSemanticReconstruction.IndependentGeometryHomExplicitRawPoints
import Formal.Util.AssertStandardAxioms

/-!
# Original explicit raw maps satisfy the primitive preservation laws

Implementation notes: the three reading equalities below are comparison
premises for a common reader. They include every candidate row and introduce
no extra condition on a native raw map. Carrier activation is recovered from
the original raw response laws; the native generator and restriction equations
then imply the sparse coefficient point rules. Testing only selected carrier
rows would leave the inactive clauses and dependent fibers unjustified.
-/

namespace AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.ExplicitRaw

noncomputable section

universe u v

open Site CategoryTheory AtomFoundation GeometryTransport LawAlgebra RealizationReconstruction

variable {U : AtomCarrier.{u}} {G H : GeometryPackage.{u, v} U}
variable (f : PackageTotalHom G.core H.core) (a : G.Coefficient →+* H.Coefficient)
variable (R : RawAmbientRestrictionSystemExactMapAgainst G.site H.site (coreContextInverse f) a G.raw H.raw)
variable (h : Table.{u, v} U .explicit) (hm : Maps f a h)
variable (hc : ∀ W V, readCoordinate R W V = InverseRows.coordinate h _ _ W V)
variable (hr : ∀ W V, readRelation R W V = InverseRows.relation h _ _ W V)
variable (hl : ∀ W V C D c d, readLocalData R W V C D c d = InverseRows.localData h _ _ W V C D c d)

include hc in
/-- Native coordinate reading supplies the independent inverse-graph laws on the actual carrier pair. -/
theorem coordinate_rows_of_read (V : ArchCtx H.core.object) :
    IndependentInverseGraph.IsLawful (G.raw.coordFamily ((coreContextInverse f).obj ⟨V⟩)).Coord
      (H.raw.coordFamily ⟨V⟩).Coord (InverseRows.coordinate h _ _ (inverse f V) V) := by
  rw [← hc, readCoordinate_active]
  exact IndependentInverseGraph.read_isLawful _ _ (R.coordinate ⟨V⟩).coordinateEquiv

include hr in
/-- Native relation reading supplies inverse rows on the declared generator carriers. -/
theorem relation_rows_of_read (V : ArchCtx H.core.object) :
    IndependentInverseGraph.IsLawful (G.raw.relationFamily ((coreContextInverse f).obj ⟨V⟩)).Relation
      (H.raw.relationFamily ⟨V⟩).Relation (InverseRows.relation h _ _ (inverse f V) V) := by
  rw [← hr, readRelation_active]
  exact IndependentInverseGraph.read_isLawful _ _ (R.relation ⟨V⟩).relationEquiv

include hc in
/-- Active coordinate points identify exactly the original native coordinate image. -/
theorem coordinate_point_iff_of_read (V : ArchCtx H.core.object)
    (c : (G.raw.coordFamily ((coreContextInverse f).obj ⟨V⟩)).Coord)
    (d : (H.raw.coordFamily ⟨V⟩).Coord) :
    coordinatePoint h (inverse f V) V _ _ c d = true ↔ (R.coordinate ⟨V⟩).coordinateEquiv c = d := by
  have he := congrFun ((readCoordinate_active R V).symm.trans (hc (inverse f V) V))
    (.forward (.edge _ _ c d))
  change _ = coordinatePoint h (inverse f V) V _ _ c d at he
  rw [← he]
  exact IndependentCarrierGraph.read_edge _ _ (R.coordinate ⟨V⟩).coordinateEquiv c d

include hr in
/-- Active relation points identify the original generator equivalence. -/
theorem relation_point_iff_of_read (V : ArchCtx H.core.object)
    (i : (G.raw.relationFamily ((coreContextInverse f).obj ⟨V⟩)).Relation)
    (j : (H.raw.relationFamily ⟨V⟩).Relation) :
    relationPoint h (inverse f V) V _ _ i j = true ↔ (R.relation ⟨V⟩).relationEquiv i = j := by
  have he := congrFun ((readRelation_active R V).symm.trans (hr (inverse f V) V))
    (.forward (.edge _ _ i j))
  change _ = relationPoint h (inverse f V) V _ _ i j at he
  rw [← he]
  exact IndependentCarrierGraph.read_edge _ _ (R.relation ⟨V⟩).relationEquiv i j

include hm hc hr hl in
/-- Every original native explicit raw map satisfies all primitive candidate-row and polynomial point laws. -/
theorem points_of_native : NativePoints G H h := by
  constructor
  · intro W V hv q
    have hn : inverse f V ≠ W := fun he => Bool.noConfusion (hv.symm.trans ((hm.context W V).2 he))
    rw [← hc W V, readCoordinate_inactive R W V hn]
  · intro W V hv
    obtain rfl := (hm.context W V).1 hv
    exact coordinate_rows_of_read f a R h hc V
  · intro W V hv q
    have hn : inverse f V ≠ W := fun he => Bool.noConfusion (hv.symm.trans ((hm.context W V).2 he))
    rw [← hr W V, readRelation_inactive R W V hn]
  · intro W V hv
    obtain rfl := (hm.context W V).1 hv
    exact relation_rows_of_read f a R h hr V
  · intro W V C D c d hinactive q
    rw [← hl W V C D c d]
    rcases hinactive with hv | hd
    · have hn : inverse f V ≠ W := fun he => Bool.noConfusion (hv.symm.trans ((hm.context W V).2 he))
      rw [readLocalData_inactive_context R W V C D c d hn]
    · have he : readCoordinate R W V (.forward (.edge C D c d)) = false := by
        rw [hc W V]
        exact hd
      rw [readLocalData_inactive_coordinate R W V C D c d he]
  · intro W V C D c d L M hv hd hs ht
    obtain rfl := (hm.context W V).1 hv
    have rows := coordinate_rows_of_read f a R h hc V
    have hC : C = (G.raw.coordFamily ((coreContextInverse f).obj ⟨V⟩)).Coord := by
      by_contra hn
      exact Bool.noConfusion ((rows.forward.1 C D c d (Or.inl hn)).symm.trans hd)
    subst C
    have hD : D = (H.raw.coordFamily ⟨V⟩).Coord := by
      by_contra hn
      exact Bool.noConfusion ((rows.forward.1 _ D c d (Or.inr hn)).symm.trans hd)
    subst D
    have he := (coordinate_point_iff_of_read f a R h hc V c d).1 hd
    subst d
    obtain rfl := Option.some.inj ((IndependentRawCandidate.read_localData G.site G.Coefficient G.raw _ c).symm.trans hs)
    obtain rfl := Option.some.inj ((IndependentRawCandidate.read_localData H.site H.Coefficient H.raw V _).symm.trans ht)
    have he := (readLocalData_active R V c).symm.trans (hl (inverse f V) V _ _ c ((R.coordinate ⟨V⟩).coordinateEquiv c))
    have hlocal := IndependentInverseGraph.read_isLawful _ _ ((R.coordinate ⟨V⟩).localDataEquiv c)
    rw [he] at hlocal
    exact hlocal
  · intro W V C D c d hv hd
    obtain rfl := (hm.context W V).1 hv
    have rows := coordinate_rows_of_read f a R h hc V
    have hC : C = (G.raw.coordFamily ((coreContextInverse f).obj ⟨V⟩)).Coord := by
      by_contra hn
      exact Bool.noConfusion ((rows.forward.1 C D c d (Or.inl hn)).symm.trans hd)
    subst C
    have hD : D = (H.raw.coordFamily ⟨V⟩).Coord := by
      by_contra hn
      exact Bool.noConfusion ((rows.forward.1 _ D c d (Or.inr hn)).symm.trans hd)
    subst D
    have he := (coordinate_point_iff_of_read f a R h hc V c d).1 hd
    subst d
    exact (IndependentRawCandidate.read_label G.site G.Coefficient G.raw _ c).trans
      ((congrArg some ((R.coordinate ⟨V⟩).label_eq c)).symm.trans
        (IndependentRawCandidate.read_label H.site H.Coefficient H.raw V _).symm)
  · intro W V C D I J rk rl i j p p' hv hij hs ht
    obtain rfl := (hm.context W V).1 hv
    have hst := (IndependentRawCandidate.read_isTyped G.site G.Coefficient G.raw).polynomial (inverse f V) C I rk i
    rcases hst.mp (congrArg Option.isSome hs) with ⟨hC, hI, hk⟩
    subst C
    subst I
    subst rk
    have htt := (IndependentRawCandidate.read_isTyped H.site H.Coefficient H.raw).polynomial V D J rl j
    rcases htt.mp (congrArg Option.isSome ht) with ⟨hD, hJ, hl'⟩
    subst D
    subst J
    subst rl
    have he := (relation_point_iff_of_read f a R h hr V i j).1 hij
    subst j
    obtain rfl := Option.some.inj ((IndependentRawCandidate.read_polynomial G.site G.Coefficient G.raw _ i).symm.trans hs)
    obtain rfl := Option.some.inj ((IndependentRawCandidate.read_polynomial H.site H.Coefficient H.raw V _).symm.trans ht)
    apply (IndependentPolynomialPointTransport.points_iff_rename_map (R.coordinate ⟨V⟩).coordinateEquiv a _ _
      (coordinate_point_iff_of_read f a R h hc V) hm.coefficient _ _).2
    exact (R.relation ⟨V⟩).polynomial_eq i
  · intro W X V Y C D E F rk rl x y p p' hWV hXY hxy hs ht
    obtain rfl := (hm.context W V).1 hWV
    obtain rfl := (hm.context X Y).1 hXY
    have hst := (IndependentRawCandidate.read_isTyped G.site G.Coefficient G.raw).image (inverse f V) (inverse f Y) C E rk x
    rcases hst.mp (congrArg Option.isSome hs) with ⟨hleS, hC, hE, hk⟩
    subst C
    subst E
    subst rk
    have htt := (IndependentRawCandidate.read_isTyped H.site H.Coefficient H.raw).image V Y D F rl y
    rcases htt.mp (congrArg Option.isSome ht) with ⟨hleT, hD, hF, hl'⟩
    subst D
    subst F
    subst rl
    have he := (coordinate_point_iff_of_read f a R h hc Y x y).1 hxy
    subst y
    obtain rfl := Option.some.inj ((IndependentRawCandidate.read_image G.site G.Coefficient G.raw hleS x).symm.trans hs)
    obtain rfl := Option.some.inj ((IndependentRawCandidate.read_image H.site H.Coefficient H.raw hleT _).symm.trans ht)
    apply (IndependentPolynomialPointTransport.points_iff_rename_map (R.coordinate ⟨V⟩).coordinateEquiv a _ _
      (coordinate_point_iff_of_read f a R h hc V) hm.coefficient _ _).2
    let g : (⟨V⟩ : H.site.category) ⟶ ⟨Y⟩ := homOfLE hleT
    have he := (IndependentExplicitRaw.read_isLawful R).image g x
    rw [IndependentExplicitRaw.coordinateMap_read, IndependentExplicitRaw.coordinateMap_read] at he
    exact he

end

end AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.ExplicitRaw

#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.ExplicitRaw
