import ResearchLean.AG.RelativeRepairComposition.W1SubdivisionInput

/-!
# Both authored W1 occurrences of a are replaced by their actual factor paths

The original first Law keeps b,e. The complete second Law becomes
c,first,second,b,first,second,e, with its original ry comparison loop unchanged.
This uses substitution on the same original typed paths, retaining both visits.
-/
namespace AAT.AG.RelativeRepairComposition.W1SubdivisionWords
open CategoryTheory TransportCoherence TransportCoherence.Arbitrary AbelianLiftingObstruction
open W1AffineInput W1Regions W1SubdivisionInput Subdivision

/-- Every retained original loop is different from the chosen a by its unchanged original name. -/
theorem name_ne_chosen (e : Fin 6) (he : e ≠ edgeA) : name e ≠ chosen := by
  intro h
  have hh := congrArg (fun n : EdgeName (K := geometry) => n.2.2) h
  exact he hh

/-- The original b loop remains at its original endpoints after subdivision. -/
def retainedB := oldEdge geometry chosen (name edgeB) (name_ne_chosen edgeB (by decide))

/-- The original c loop remains a distinct original candidate after subdivision. -/
def retainedC := oldEdge geometry chosen (name edgeC) (name_ne_chosen edgeC (by decide))

/-- The shared original always loop e remains unchanged in the authored paths. -/
def retainedE := oldEdge geometry chosen (name edgeE) (name_ne_chosen edgeE (by decide))

/-- The first original Law still has its complete temporal b,e word. -/
theorem first_word : (presentation geometry chosen).twoLeft false =
    PresentedPath.cons retainedB (.cons retainedE (.nil (Sum.inl () : Vertex geometry))) := by
  change substitutePath geometry chosen (.cons (i := ()) (j := ()) edgeB
    (.cons (i := ()) (j := ()) edgeE (.nil ()))) = _
  simp only [substitutePath]
  have hb := edgeWord_old geometry chosen (name edgeB) (name_ne_chosen edgeB (by decide))
  have he := edgeWord_old geometry chosen (name edgeE) (name_ne_chosen edgeE (by decide))
  simp only [name] at hb he
  simp only [hb, he, PresentedPath.append, retainedB, retainedE, name]

/-- The full second authored Law retains both a occurrences as the two actual factors in the specified order. -/
theorem second_word : (presentation geometry chosen).twoLeft true =
    PresentedPath.cons retainedC (.cons (firstEdge geometry chosen) (.cons (secondEdge geometry chosen)
      (.cons retainedB (.cons (firstEdge geometry chosen) (.cons (secondEdge geometry chosen)
        (.cons retainedE (.nil (Sum.inl () : Vertex geometry)))))))) := by
  change substitutePath geometry chosen (.cons (i := ()) (j := ()) edgeC
    (.cons (i := ()) (j := ()) edgeA (.cons (i := ()) (j := ()) edgeB
      (.cons (i := ()) (j := ()) edgeA (.cons (i := ()) (j := ()) edgeE (.nil ())))))) = _
  simp only [substitutePath]
  have ha : edgeWord geometry chosen (name edgeA) = factorPath geometry chosen := edgeWord_chosen geometry chosen
  have hc := edgeWord_old geometry chosen (name edgeC) (name_ne_chosen edgeC (by decide))
  have hb := edgeWord_old geometry chosen (name edgeB) (name_ne_chosen edgeB (by decide))
  have he := edgeWord_old geometry chosen (name edgeE) (name_ne_chosen edgeE (by decide))
  simp only [name] at ha hc hb he
  simp only [ha, hc, hb, he, factorPath, PresentedPath.append, retainedB, retainedC, retainedE, name]

end AAT.AG.RelativeRepairComposition.W1SubdivisionWords
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition.W1SubdivisionWords
