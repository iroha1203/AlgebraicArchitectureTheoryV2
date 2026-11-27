import Formal.SHIGURE.Part2.Schemes.FiberwiseSectionDescent

/-! # Section descent on the identity and empty families -/

namespace SHIGURE.SchemeDescent

open CategoryTheory CategoryTheory.Bicategory Opposite

noncomputable section

private abbrev baseTest := Discrete PUnit.{1}
private abbrev point : baseTest := ⟨PUnit.unit⟩

/-- Each test object has a single possible base structure. -/
private def constantPoint :
    Pseudofunctor (LocallyDiscrete baseTestᵒᵖ) Cat.{0,0} :=
  ((Functor.const (baseTestᵒᵖ)).obj (Cat.of (Discrete PUnit.{1}))).toPseudoFunctor'

/-- Take both section values over the one structure, with identity restriction. -/
private def booleanSections : FiberwiseSections constantPoint where
  fiber _ := (Functor.const (Discrete PUnit.{1})).obj Bool
  restrict _ := 𝟙 _
  restrict_id _ _ _ := rfl
  restrict_comp _ _ _ _ := rfl

/-- Two available sections descend over one identity chart. -/
theorem booleanSections_identityDescent :
    booleanSections.HasSectionDescent (fun _ : Unit => 𝟙 point) := by
  intro M s _
  refine ⟨s (), ?_, ?_⟩
  · rintro ⟨⟩
    rfl
  · intro t h
    exact h ()

/-- The empty family cannot distinguish the two sections. -/
theorem booleanSections_not_emptyDescent :
    ¬ booleanSections.HasSectionDescent (fun _ : Empty => 𝟙 point) := by
  intro h
  let M : constantPoint.obj (.mk (op point)) := ⟨PUnit.unit⟩
  let s : booleanSections.localSections (fun _ : Empty => 𝟙 point) M := fun i => nomatch i
  obtain ⟨t, _, unique⟩ := h M s (fun _ _ i => nomatch i)
  have p := unique true (fun i => nomatch i)
  have q := unique false (fun i => nomatch i)
  exact Bool.noConfusion (p.trans q.symm)

end

end SHIGURE.SchemeDescent
