import ResearchLean.AG.DoctrineFiberProduct.UpperGeometryCleavage

/-!
# Realization transport for the explicit exact geometry cleavage

The local comparisons below are generated from the public carrier-preservation
theorems for `inverseCorePackageForwardUpper`.  They expose no realization
certificate as caller data.
-/

namespace AAT.AG.DoctrineFiberProduct

universe u v

open CategoryTheory AtomFoundation GeometryTransport

namespace UpperGeometryCleavage

/-- Reading transport across equality of complete architecture contexts. -/
private theorem supportReads_cast_context_eq {U : AtomCarrier.{u}}
    {A : ArchitectureObject U} {C D : Site.ArchitectureContext A}
    (hCD : C = D) (support : D.Support) (atom : U.Atom) :
    C.minimal.supportReads
        (cast (congrArg Site.ArchitectureContext.Support hCD).symm support) atom ↔
      D.minimal.supportReads support atom := by
  cases hCD
  rfl

private theorem axisReads_cast_context_eq {U : AtomCarrier.{u}}
    {A : ArchitectureObject U} {C D : Site.ArchitectureContext A}
    (hCD : C = D) (axis : D.Axis) :
    C.minimal.axisReads
        (cast (congrArg Site.ArchitectureContext.Axis hCD).symm axis) ↔
      D.minimal.axisReads axis := by
  cases hCD
  rfl

private theorem observableReads_cast_context_eq {U : AtomCarrier.{u}}
    {A : ArchitectureObject U} {C D : Site.ArchitectureContext A}
    (hCD : C = D) (observable : D.Observable) :
    C.minimal.observableReads
        (cast (congrArg Site.ArchitectureContext.Observable hCD).symm observable) ↔
      D.minimal.observableReads observable := by
  cases hCD
  rfl

/-- Casting backwards along a composite equality is iterated backward casting. -/
private theorem cast_trans_symm {alpha beta gamma : Sort v}
    (first : alpha = beta) (second : beta = gamma) (value : gamma) :
    cast (first.trans second).symm value =
      cast first.symm (cast second.symm value) := by
  cases first
  cases second
  rfl

/-- A cast of the base object preserves the support carrier. -/
private theorem support_type_cast_object_eq {U : AtomCarrier.{u}}
    {A B : ArchitectureObject U} (hAB : A = B)
    (C : Site.ArchitectureContext A) :
    (cast (congrArg Site.ArchitectureContext hAB) C).Support = C.Support := by
  cases hAB
  rfl

private theorem axis_type_cast_object_eq {U : AtomCarrier.{u}}
    {A B : ArchitectureObject U} (hAB : A = B)
    (C : Site.ArchitectureContext A) :
    (cast (congrArg Site.ArchitectureContext hAB) C).Axis = C.Axis := by
  cases hAB
  rfl

private theorem observable_type_cast_object_eq {U : AtomCarrier.{u}}
    {A B : ArchitectureObject U} (hAB : A = B)
    (C : Site.ArchitectureContext A) :
    (cast (congrArg Site.ArchitectureContext hAB) C).Observable = C.Observable := by
  cases hAB
  rfl

/-- Reading transport across an architecture-object cast. -/
private theorem supportReads_cast_object_eq {U : AtomCarrier.{u}}
    {A B : ArchitectureObject U} (hAB : A = B)
    (C : Site.ArchitectureContext A) (support : C.Support) (atom : U.Atom) :
    (cast (congrArg Site.ArchitectureContext hAB) C).minimal.supportReads
        (cast (support_type_cast_object_eq hAB C).symm support) atom ↔
      C.minimal.supportReads support atom := by
  cases hAB
  rfl

private theorem axisReads_cast_object_eq {U : AtomCarrier.{u}}
    {A B : ArchitectureObject U} (hAB : A = B)
    (C : Site.ArchitectureContext A) (axis : C.Axis) :
    (cast (congrArg Site.ArchitectureContext hAB) C).minimal.axisReads
        (cast (axis_type_cast_object_eq hAB C).symm axis) ↔
      C.minimal.axisReads axis := by
  cases hAB
  rfl

private theorem observableReads_cast_object_eq {U : AtomCarrier.{u}}
    {A B : ArchitectureObject U} (hAB : A = B)
    (C : Site.ArchitectureContext A) (observable : C.Observable) :
    (cast (congrArg Site.ArchitectureContext hAB) C).minimal.observableReads
        (cast (observable_type_cast_object_eq hAB C).symm observable) ↔
      C.minimal.observableReads observable := by
  cases hAB
  rfl

/-- The exact inverse-package hom underlying `exactSourceGeometry`. -/
noncomputable def exactBaseHom {U : AtomCarrier.{u}}
    {X : ExtractionInstance U} (G : GeometryPackage.{u, v} U)
    (f : X ⟶ packagePoint G.core) :
    PackageTotalHom (exactSourceGeometry G f).core G.core :=
  inverseCorePackageHom G.core f

/-- Canonical support comparison for the explicit exact inverse package. -/
noncomputable def exactSupportComp {U : AtomCarrier.{u}}
    {X : ExtractionInstance U} (G : GeometryPackage.{u, v} U)
    (f : X ⟶ packagePoint G.core)
    (W : (exactSourceGeometry G f).site.category) :
    W.ctx.Support →
      (refinementGeometryContextForward
        ((exactPackageToRefinement U).map (exactBaseHom G f)) W).ctx.Support :=
  cast (inverseCorePackageForwardUpper_contextFunctor_obj_support_type
    G.core f W).symm

/-- Canonical axis comparison for the explicit exact inverse package. -/
noncomputable def exactAxisComp {U : AtomCarrier.{u}}
    {X : ExtractionInstance U} (G : GeometryPackage.{u, v} U)
    (f : X ⟶ packagePoint G.core)
    (W : (exactSourceGeometry G f).site.category) :
    W.ctx.Axis →
      (refinementGeometryContextForward
        ((exactPackageToRefinement U).map (exactBaseHom G f)) W).ctx.Axis :=
  cast (inverseCorePackageForwardUpper_contextFunctor_obj_axis_type
    G.core f W).symm

/-- Canonical observable comparison for the explicit exact inverse package. -/
noncomputable def exactObservableComp {U : AtomCarrier.{u}}
    {X : ExtractionInstance U} (G : GeometryPackage.{u, v} U)
    (f : X ⟶ packagePoint G.core)
    (W : (exactSourceGeometry G f).site.category) :
    W.ctx.Observable →
      (refinementGeometryContextForward
        ((exactPackageToRefinement U).map (exactBaseHom G f)) W).ctx.Observable :=
  cast (inverseCorePackageForwardUpper_contextFunctor_obj_observable_type
    G.core f W).symm

/-- The canonical exact support comparison preserves the transported reading. -/
theorem exactSupportReads {U : AtomCarrier.{u}}
    {X : ExtractionInstance U} (G : GeometryPackage.{u, v} U)
    (f : X ⟶ packagePoint G.core)
    (W : (exactSourceGeometry G f).site.category) support atom
    (h : W.ctx.minimal.supportReads support atom) :
    (refinementGeometryContextForward
      ((exactPackageToRefinement U).map (exactBaseHom G f)) W).ctx.minimal.supportReads
        (exactSupportComp G f W support)
        (((exactPackageToRefinement U).map
          (exactBaseHom G f)).upper.atomEquiv atom) := by
  unfold exactSupportComp exactBaseHom exactSourceGeometry
  change
    ((inverseCorePackageForwardUpper G.core f).equationTransport.contextForward
      W).ctx.minimal.supportReads
        (cast (inverseCorePackageForwardUpper_contextFunctor_obj_support_type
          G.core f W).symm support)
        (f.doctrineHom.atomEquiv atom)
  let C := ((inverseCorePackageForwardUpper G.core f).equationTransport.contextForward
    W).ctx
  let D := transportArchitectureContextBackward f.doctrineHom.atomEquiv.symm
    G.core.object
    (cast (congrArg Site.ArchitectureContext (inverseBaseObject_eq G.core f)) W.ctx)
  have hCD : C = D :=
    inverseCorePackageForwardUpper_contextFunctor_obj_eq G.core f W
  let hDcarrier : D.Support = W.ctx.Support :=
    support_type_cast_object_eq (inverseBaseObject_eq G.core f) W.ctx
  have hcarrier :
      inverseCorePackageForwardUpper_contextFunctor_obj_support_type G.core f W =
        (congrArg Site.ArchitectureContext.Support hCD).trans hDcarrier := by
    apply Subsingleton.elim
  rw [hcarrier]
  have hD : D.minimal.supportReads
      (cast hDcarrier.symm support) (f.doctrineHom.atomEquiv atom) := by
    dsimp [D, hDcarrier, transportArchitectureContextBackward]
    simpa only [Equiv.symm_apply_apply] using
      (supportReads_cast_object_eq
        (inverseBaseObject_eq G.core f) W.ctx support atom).2 h
  have hread := (supportReads_cast_context_eq hCD
    (cast hDcarrier.symm support) (f.doctrineHom.atomEquiv atom)).2 hD
  have hcast := cast_trans_symm
    (congrArg Site.ArchitectureContext.Support hCD) hDcarrier support
  exact hcast.symm ▸ hread

/-- The canonical exact axis comparison preserves the transported reading. -/
theorem exactAxisReads {U : AtomCarrier.{u}}
    {X : ExtractionInstance U} (G : GeometryPackage.{u, v} U)
    (f : X ⟶ packagePoint G.core)
    (W : (exactSourceGeometry G f).site.category) axis
    (h : W.ctx.minimal.axisReads axis) :
    (refinementGeometryContextForward
      ((exactPackageToRefinement U).map (exactBaseHom G f)) W).ctx.minimal.axisReads
        (exactAxisComp G f W axis) := by
  unfold exactAxisComp exactBaseHom exactSourceGeometry
  change
    ((inverseCorePackageForwardUpper G.core f).equationTransport.contextForward
      W).ctx.minimal.axisReads
        (cast (inverseCorePackageForwardUpper_contextFunctor_obj_axis_type
          G.core f W).symm axis)
  let C := ((inverseCorePackageForwardUpper G.core f).equationTransport.contextForward
    W).ctx
  let D := transportArchitectureContextBackward f.doctrineHom.atomEquiv.symm
    G.core.object
    (cast (congrArg Site.ArchitectureContext (inverseBaseObject_eq G.core f)) W.ctx)
  have hCD : C = D :=
    inverseCorePackageForwardUpper_contextFunctor_obj_eq G.core f W
  let hDcarrier : D.Axis = W.ctx.Axis :=
    axis_type_cast_object_eq (inverseBaseObject_eq G.core f) W.ctx
  have hcarrier :
      inverseCorePackageForwardUpper_contextFunctor_obj_axis_type G.core f W =
        (congrArg Site.ArchitectureContext.Axis hCD).trans hDcarrier := by
    apply Subsingleton.elim
  rw [hcarrier]
  have hD : D.minimal.axisReads (cast hDcarrier.symm axis) := by
    dsimp [D, hDcarrier, transportArchitectureContextBackward]
    exact (axisReads_cast_object_eq
      (inverseBaseObject_eq G.core f) W.ctx axis).2 h
  have hread := (axisReads_cast_context_eq hCD
    (cast hDcarrier.symm axis)).2 hD
  have hcast := cast_trans_symm
    (congrArg Site.ArchitectureContext.Axis hCD) hDcarrier axis
  exact hcast.symm ▸ hread

/-- The canonical exact observable comparison preserves the transported reading. -/
theorem exactObservableReads {U : AtomCarrier.{u}}
    {X : ExtractionInstance U} (G : GeometryPackage.{u, v} U)
    (f : X ⟶ packagePoint G.core)
    (W : (exactSourceGeometry G f).site.category) observable
    (h : W.ctx.minimal.observableReads observable) :
    (refinementGeometryContextForward
      ((exactPackageToRefinement U).map (exactBaseHom G f)) W).ctx.minimal.observableReads
        (exactObservableComp G f W observable) := by
  unfold exactObservableComp exactBaseHom exactSourceGeometry
  change
    ((inverseCorePackageForwardUpper G.core f).equationTransport.contextForward
      W).ctx.minimal.observableReads
        (cast (inverseCorePackageForwardUpper_contextFunctor_obj_observable_type
          G.core f W).symm observable)
  let C := ((inverseCorePackageForwardUpper G.core f).equationTransport.contextForward
    W).ctx
  let D := transportArchitectureContextBackward f.doctrineHom.atomEquiv.symm
    G.core.object
    (cast (congrArg Site.ArchitectureContext (inverseBaseObject_eq G.core f)) W.ctx)
  have hCD : C = D :=
    inverseCorePackageForwardUpper_contextFunctor_obj_eq G.core f W
  let hDcarrier : D.Observable = W.ctx.Observable :=
    observable_type_cast_object_eq (inverseBaseObject_eq G.core f) W.ctx
  have hcarrier :
      inverseCorePackageForwardUpper_contextFunctor_obj_observable_type G.core f W =
        (congrArg Site.ArchitectureContext.Observable hCD).trans hDcarrier := by
    apply Subsingleton.elim
  rw [hcarrier]
  have hD : D.minimal.observableReads
      (cast hDcarrier.symm observable) := by
    dsimp [D, hDcarrier, transportArchitectureContextBackward]
    exact (observableReads_cast_object_eq
      (inverseBaseObject_eq G.core f) W.ctx observable).2 h
  have hread := (observableReads_cast_context_eq hCD
    (cast hDcarrier.symm observable)).2 hD
  have hcast := cast_trans_symm
    (congrArg Site.ArchitectureContext.Observable hCD) hDcarrier observable
  exact hcast.symm ▸ hread

end UpperGeometryCleavage

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct.UpperGeometryCleavage
