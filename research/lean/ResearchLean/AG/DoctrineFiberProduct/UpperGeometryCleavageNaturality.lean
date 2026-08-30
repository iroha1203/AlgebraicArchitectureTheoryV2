import ResearchLean.AG.DoctrineFiberProduct.UpperGeometryCleavageRealization

/-!
# Restriction naturality for the explicit upper geometry cleavage

This module exposes the source-reading cast used by the G-115 geometry lift so
that its context-map computation can be proved locally.  Completed predecessor
modules remain unchanged.
-/

namespace AAT.AG.DoctrineFiberProduct

universe u v

open CategoryTheory AtomFoundation GeometryTransport

namespace UpperGeometryCleavage

/-- G-115-local source reindexing of an exact equation transport. -/
private def geometryCastSourceEquationExact {U : AtomCarrier.{u}}
    {A A' B : ArchitectureObject U}
    {D : Site.ContextPreorderCategory B}
    {G : ArchitecturalEquationSystem D}
    (h : A = A') (S : EquationReading A)
    (e : U.Atom ≃ U.Atom)
    (objectMap : ArchitectureObject U → ArchitectureObject U)
    (T : EquationSystemExactTransport S.equationSystem G e objectMap) :
    EquationSystemExactTransport
      (castEquationReading h S).equationSystem G e objectMap := by
  cases h
  exact T

private def geometryInverseCompositeEquationRefl {U : AtomCarrier.{u}}
    {A : ArchitectureObject U}
    {C : Site.ContextPreorderCategory A}
    (E : ArchitecturalEquationSystem C) (e : U.Atom ≃ U.Atom) :
    EquationSystemExactTransport E E (e.symm.trans e) _root_.id where
  contextEquivalence := CategoryTheory.Equivalence.refl
  equationEquiv := Equiv.refl _
  role_eq _ := rfl
  observableEquiv _ := RingEquiv.refl _
  observable_naturality := by intros; rfl
  violationCoordinate_eq := by intros; simp
  equationResidual_eq := by intros; simp

theorem inverseCoreEquationForward_eq_geometryCast
    {U : AtomCarrier.{u}} {X : ExtractionInstance U}
    (Q : AATCorePackage U) (f : X ⟶ packagePoint Q) :
    inverseCoreEquationForward Q f =
      geometryCastSourceEquationExact
        (inverseBaseObject_eq Q f).symm
        (transportEquationReading f.doctrineHom.atomEquiv.symm
          Q.object Q.reading.equationReading)
        f.doctrineHom.atomEquiv
        (transportArchitectureObject f.doctrineHom.atomEquiv)
        (deconjugateEquationSystemExact f.doctrineHom.atomEquiv.symm
          f.doctrineHom.atomEquiv Q.object
          Q.reading.equationReading.contextPreorder
          Q.reading.equationReading.equationSystem _root_.id
          (geometryInverseCompositeEquationRefl
            Q.reading.equationReading.equationSystem
            f.doctrineHom.atomEquiv)) := by
  rfl

private def geometryDeconjugateEquationSystem {U : AtomCarrier.{u}}
    (Q : AATCorePackage U) (e : U.Atom ≃ U.Atom) :=
  deconjugateEquationSystemExact e.symm e Q.object
    Q.reading.equationReading.contextPreorder
    Q.reading.equationReading.equationSystem _root_.id
    (geometryInverseCompositeEquationRefl
      Q.reading.equationReading.equationSystem e)

private noncomputable def geometryDeconjugateSupportComp
    {U : AtomCarrier.{u}} (Q : AATCorePackage U)
    (e : U.Atom ≃ U.Atom)
    (W : Site.ContextCategoryObject
      (transportEquationReading e.symm Q.object
        Q.reading.equationReading).contextPreorder) :
    W.ctx.Support →
      ((geometryDeconjugateEquationSystem Q e).contextEquivalence.functor.obj
        W).ctx.Support :=
  _root_.id

private theorem geometryDeconjugateSupportComp_naturality
    {U : AtomCarrier.{u}} (Q : AATCorePackage U)
    (e : U.Atom ≃ U.Atom)
    {W V : Site.ContextCategoryObject
      (transportEquationReading e.symm Q.object
        Q.reading.equationReading).contextPreorder}
    (w : W ⟶ V) (support : W.ctx.Support) :
    (Q.contextPreorder.morphism (leOfHom
      ((geometryDeconjugateEquationSystem Q e).contextEquivalence.functor.map
        w))).supportMap
        (geometryDeconjugateSupportComp Q e W support) =
      geometryDeconjugateSupportComp Q e V
        (((transportEquationReading e.symm Q.object
          Q.reading.equationReading).contextPreorder.morphism
            (leOfHom w)).supportMap support) := by
  rfl

private noncomputable def geometryDeconjugateAxisComp
    {U : AtomCarrier.{u}} (Q : AATCorePackage U)
    (e : U.Atom ≃ U.Atom)
    (W : Site.ContextCategoryObject
      (transportEquationReading e.symm Q.object
        Q.reading.equationReading).contextPreorder) :
    W.ctx.Axis →
      ((geometryDeconjugateEquationSystem Q e).contextEquivalence.functor.obj
        W).ctx.Axis :=
  _root_.id

private theorem geometryDeconjugateAxisComp_naturality
    {U : AtomCarrier.{u}} (Q : AATCorePackage U)
    (e : U.Atom ≃ U.Atom)
    {W V : Site.ContextCategoryObject
      (transportEquationReading e.symm Q.object
        Q.reading.equationReading).contextPreorder}
    (w : W ⟶ V) (axis : W.ctx.Axis) :
    (Q.contextPreorder.morphism (leOfHom
      ((geometryDeconjugateEquationSystem Q e).contextEquivalence.functor.map
        w))).axisMap
        (geometryDeconjugateAxisComp Q e W axis) =
      geometryDeconjugateAxisComp Q e V
        (((transportEquationReading e.symm Q.object
          Q.reading.equationReading).contextPreorder.morphism
            (leOfHom w)).axisMap axis) := by
  rfl

private noncomputable def geometryDeconjugateObservableComp
    {U : AtomCarrier.{u}} (Q : AATCorePackage U)
    (e : U.Atom ≃ U.Atom)
    (W : Site.ContextCategoryObject
      (transportEquationReading e.symm Q.object
        Q.reading.equationReading).contextPreorder) :
    W.ctx.Observable →
      ((geometryDeconjugateEquationSystem Q e).contextEquivalence.functor.obj
        W).ctx.Observable :=
  _root_.id

private theorem geometryDeconjugateObservableComp_naturality
    {U : AtomCarrier.{u}} (Q : AATCorePackage U)
    (e : U.Atom ≃ U.Atom)
    {W V : Site.ContextCategoryObject
      (transportEquationReading e.symm Q.object
        Q.reading.equationReading).contextPreorder}
    (w : W ⟶ V) (observable : V.ctx.Observable) :
    (Q.contextPreorder.morphism (leOfHom
      ((geometryDeconjugateEquationSystem Q e).contextEquivalence.functor.map
        w))).observableRestrict
        (geometryDeconjugateObservableComp Q e V observable) =
      geometryDeconjugateObservableComp Q e W
        (((transportEquationReading e.symm Q.object
          Q.reading.equationReading).contextPreorder.morphism
            (leOfHom w)).observableRestrict observable) := by
  rfl

private theorem geometryDeconjugateSupportComp_reads
    {U : AtomCarrier.{u}} (Q : AATCorePackage U)
    (e : U.Atom ≃ U.Atom)
    (W : Site.ContextCategoryObject
      (transportEquationReading e.symm Q.object
        Q.reading.equationReading).contextPreorder)
    (support : W.ctx.Support) (atom : U.Atom)
    (h : W.ctx.minimal.supportReads support atom) :
    ((geometryDeconjugateEquationSystem Q e).contextEquivalence.functor.obj
      W).ctx.minimal.supportReads
        (geometryDeconjugateSupportComp Q e W support) (e atom) := by
  change W.ctx.minimal.supportReads support (e.symm (e atom))
  simpa using h

private theorem geometryDeconjugateAxisComp_reads
    {U : AtomCarrier.{u}} (Q : AATCorePackage U)
    (e : U.Atom ≃ U.Atom)
    (W : Site.ContextCategoryObject
      (transportEquationReading e.symm Q.object
        Q.reading.equationReading).contextPreorder)
    (axis : W.ctx.Axis) (h : W.ctx.minimal.axisReads axis) :
    ((geometryDeconjugateEquationSystem Q e).contextEquivalence.functor.obj
      W).ctx.minimal.axisReads
        (geometryDeconjugateAxisComp Q e W axis) := by
  exact h

private theorem geometryDeconjugateObservableComp_reads
    {U : AtomCarrier.{u}} (Q : AATCorePackage U)
    (e : U.Atom ≃ U.Atom)
    (W : Site.ContextCategoryObject
      (transportEquationReading e.symm Q.object
        Q.reading.equationReading).contextPreorder)
    (observable : W.ctx.Observable)
    (h : W.ctx.minimal.observableReads observable) :
    ((geometryDeconjugateEquationSystem Q e).contextEquivalence.functor.obj
      W).ctx.minimal.observableReads
        (geometryDeconjugateObservableComp Q e W observable) := by
  exact h

private noncomputable def geometryCastSourceSupportComp
    {U : AtomCarrier.{u}} {A A' B : ArchitectureObject U}
    {D : Site.ContextPreorderCategory B}
    {G : ArchitecturalEquationSystem D}
    (h : A = A') (S : EquationReading A)
    (e : U.Atom ≃ U.Atom)
    (objectMap : ArchitectureObject U → ArchitectureObject U)
    (T : EquationSystemExactTransport S.equationSystem G e objectMap)
    (comp : ∀ W : Site.ContextCategoryObject S.contextPreorder,
      W.ctx.Support → (T.contextEquivalence.functor.obj W).ctx.Support)
    (W : Site.ContextCategoryObject
      (castEquationReading h S).contextPreorder) :
    W.ctx.Support →
      ((geometryCastSourceEquationExact h S e objectMap T).contextEquivalence.functor.obj
        W).ctx.Support := by
  cases h
  exact comp W

private theorem geometryCastSourceSupportComp_naturality
    {U : AtomCarrier.{u}} {A A' B : ArchitectureObject U}
    {D : Site.ContextPreorderCategory B}
    {G : ArchitecturalEquationSystem D}
    (h : A = A') (S : EquationReading A)
    (e : U.Atom ≃ U.Atom)
    (objectMap : ArchitectureObject U → ArchitectureObject U)
    (T : EquationSystemExactTransport S.equationSystem G e objectMap)
    (comp : ∀ W : Site.ContextCategoryObject S.contextPreorder,
      W.ctx.Support → (T.contextEquivalence.functor.obj W).ctx.Support)
    (comp_naturality : ∀ {W V : Site.ContextCategoryObject S.contextPreorder}
      (w : W ⟶ V) support,
      (D.morphism (leOfHom (T.contextEquivalence.functor.map w))).supportMap
          (comp W support) =
        comp V ((S.contextPreorder.morphism (leOfHom w)).supportMap support))
    {W V : Site.ContextCategoryObject
      (castEquationReading h S).contextPreorder}
    (w : W ⟶ V) (support : W.ctx.Support) :
    (D.morphism (leOfHom
      ((geometryCastSourceEquationExact h S e objectMap T).contextEquivalence.functor.map
        w))).supportMap
        (geometryCastSourceSupportComp h S e objectMap T comp W support) =
      geometryCastSourceSupportComp h S e objectMap T comp V
        (((castEquationReading h S).contextPreorder.morphism
          (leOfHom w)).supportMap support) := by
  cases h
  exact comp_naturality w support

private noncomputable def geometryCastSourceAxisComp
    {U : AtomCarrier.{u}} {A A' B : ArchitectureObject U}
    {D : Site.ContextPreorderCategory B}
    {G : ArchitecturalEquationSystem D}
    (h : A = A') (S : EquationReading A)
    (e : U.Atom ≃ U.Atom)
    (objectMap : ArchitectureObject U → ArchitectureObject U)
    (T : EquationSystemExactTransport S.equationSystem G e objectMap)
    (comp : ∀ W : Site.ContextCategoryObject S.contextPreorder,
      W.ctx.Axis → (T.contextEquivalence.functor.obj W).ctx.Axis)
    (W : Site.ContextCategoryObject
      (castEquationReading h S).contextPreorder) :
    W.ctx.Axis →
      ((geometryCastSourceEquationExact h S e objectMap T).contextEquivalence.functor.obj
        W).ctx.Axis := by
  cases h
  exact comp W

private theorem geometryCastSourceAxisComp_naturality
    {U : AtomCarrier.{u}} {A A' B : ArchitectureObject U}
    {D : Site.ContextPreorderCategory B}
    {G : ArchitecturalEquationSystem D}
    (h : A = A') (S : EquationReading A)
    (e : U.Atom ≃ U.Atom)
    (objectMap : ArchitectureObject U → ArchitectureObject U)
    (T : EquationSystemExactTransport S.equationSystem G e objectMap)
    (comp : ∀ W : Site.ContextCategoryObject S.contextPreorder,
      W.ctx.Axis → (T.contextEquivalence.functor.obj W).ctx.Axis)
    (comp_naturality : ∀ {W V : Site.ContextCategoryObject S.contextPreorder}
      (w : W ⟶ V) axis,
      (D.morphism (leOfHom (T.contextEquivalence.functor.map w))).axisMap
          (comp W axis) =
        comp V ((S.contextPreorder.morphism (leOfHom w)).axisMap axis))
    {W V : Site.ContextCategoryObject
      (castEquationReading h S).contextPreorder}
    (w : W ⟶ V) (axis : W.ctx.Axis) :
    (D.morphism (leOfHom
      ((geometryCastSourceEquationExact h S e objectMap T).contextEquivalence.functor.map
        w))).axisMap
        (geometryCastSourceAxisComp h S e objectMap T comp W axis) =
      geometryCastSourceAxisComp h S e objectMap T comp V
        (((castEquationReading h S).contextPreorder.morphism
          (leOfHom w)).axisMap axis) := by
  cases h
  exact comp_naturality w axis

private noncomputable def geometryCastSourceObservableComp
    {U : AtomCarrier.{u}} {A A' B : ArchitectureObject U}
    {D : Site.ContextPreorderCategory B}
    {G : ArchitecturalEquationSystem D}
    (h : A = A') (S : EquationReading A)
    (e : U.Atom ≃ U.Atom)
    (objectMap : ArchitectureObject U → ArchitectureObject U)
    (T : EquationSystemExactTransport S.equationSystem G e objectMap)
    (comp : ∀ W : Site.ContextCategoryObject S.contextPreorder,
      W.ctx.Observable → (T.contextEquivalence.functor.obj W).ctx.Observable)
    (W : Site.ContextCategoryObject
      (castEquationReading h S).contextPreorder) :
    W.ctx.Observable →
      ((geometryCastSourceEquationExact h S e objectMap T).contextEquivalence.functor.obj
        W).ctx.Observable := by
  cases h
  exact comp W

private theorem geometryCastSourceObservableComp_naturality
    {U : AtomCarrier.{u}} {A A' B : ArchitectureObject U}
    {D : Site.ContextPreorderCategory B}
    {G : ArchitecturalEquationSystem D}
    (h : A = A') (S : EquationReading A)
    (e : U.Atom ≃ U.Atom)
    (objectMap : ArchitectureObject U → ArchitectureObject U)
    (T : EquationSystemExactTransport S.equationSystem G e objectMap)
    (comp : ∀ W : Site.ContextCategoryObject S.contextPreorder,
      W.ctx.Observable → (T.contextEquivalence.functor.obj W).ctx.Observable)
    (comp_naturality : ∀ {W V : Site.ContextCategoryObject S.contextPreorder}
      (w : W ⟶ V) observable,
      (D.morphism
        (leOfHom (T.contextEquivalence.functor.map w))).observableRestrict
          (comp V observable) =
        comp W
          ((S.contextPreorder.morphism
            (leOfHom w)).observableRestrict observable))
    {W V : Site.ContextCategoryObject
      (castEquationReading h S).contextPreorder}
    (w : W ⟶ V) (observable : V.ctx.Observable) :
    (D.morphism (leOfHom
      ((geometryCastSourceEquationExact h S e objectMap T).contextEquivalence.functor.map
        w))).observableRestrict
        (geometryCastSourceObservableComp h S e objectMap T comp V observable) =
      geometryCastSourceObservableComp h S e objectMap T comp W
        (((castEquationReading h S).contextPreorder.morphism
          (leOfHom w)).observableRestrict observable) := by
  cases h
  exact comp_naturality w observable

private theorem geometryCastSourceSupportComp_reads
    {U : AtomCarrier.{u}} {A A' B : ArchitectureObject U}
    {D : Site.ContextPreorderCategory B}
    {G : ArchitecturalEquationSystem D}
    (h : A = A') (S : EquationReading A)
    (e : U.Atom ≃ U.Atom)
    (objectMap : ArchitectureObject U → ArchitectureObject U)
    (T : EquationSystemExactTransport S.equationSystem G e objectMap)
    (comp : ∀ W : Site.ContextCategoryObject S.contextPreorder,
      W.ctx.Support → (T.contextEquivalence.functor.obj W).ctx.Support)
    (comp_reads : ∀ W support atom,
      W.ctx.minimal.supportReads support atom →
        (T.contextEquivalence.functor.obj W).ctx.minimal.supportReads
          (comp W support) (e atom))
    (W : Site.ContextCategoryObject
      (castEquationReading h S).contextPreorder)
    (support : W.ctx.Support) (atom : U.Atom)
    (hread : W.ctx.minimal.supportReads support atom) :
    ((geometryCastSourceEquationExact h S e objectMap T).contextEquivalence.functor.obj
      W).ctx.minimal.supportReads
        (geometryCastSourceSupportComp h S e objectMap T comp W support)
        (e atom) := by
  cases h
  exact comp_reads W support atom hread

private theorem geometryCastSourceAxisComp_reads
    {U : AtomCarrier.{u}} {A A' B : ArchitectureObject U}
    {D : Site.ContextPreorderCategory B}
    {G : ArchitecturalEquationSystem D}
    (h : A = A') (S : EquationReading A)
    (e : U.Atom ≃ U.Atom)
    (objectMap : ArchitectureObject U → ArchitectureObject U)
    (T : EquationSystemExactTransport S.equationSystem G e objectMap)
    (comp : ∀ W : Site.ContextCategoryObject S.contextPreorder,
      W.ctx.Axis → (T.contextEquivalence.functor.obj W).ctx.Axis)
    (comp_reads : ∀ W axis, W.ctx.minimal.axisReads axis →
      (T.contextEquivalence.functor.obj W).ctx.minimal.axisReads (comp W axis))
    (W : Site.ContextCategoryObject
      (castEquationReading h S).contextPreorder)
    (axis : W.ctx.Axis) (hread : W.ctx.minimal.axisReads axis) :
    ((geometryCastSourceEquationExact h S e objectMap T).contextEquivalence.functor.obj
      W).ctx.minimal.axisReads
        (geometryCastSourceAxisComp h S e objectMap T comp W axis) := by
  cases h
  exact comp_reads W axis hread

private theorem geometryCastSourceObservableComp_reads
    {U : AtomCarrier.{u}} {A A' B : ArchitectureObject U}
    {D : Site.ContextPreorderCategory B}
    {G : ArchitecturalEquationSystem D}
    (h : A = A') (S : EquationReading A)
    (e : U.Atom ≃ U.Atom)
    (objectMap : ArchitectureObject U → ArchitectureObject U)
    (T : EquationSystemExactTransport S.equationSystem G e objectMap)
    (comp : ∀ W : Site.ContextCategoryObject S.contextPreorder,
      W.ctx.Observable → (T.contextEquivalence.functor.obj W).ctx.Observable)
    (comp_reads : ∀ W observable, W.ctx.minimal.observableReads observable →
      (T.contextEquivalence.functor.obj W).ctx.minimal.observableReads
        (comp W observable))
    (W : Site.ContextCategoryObject
      (castEquationReading h S).contextPreorder)
    (observable : W.ctx.Observable)
    (hread : W.ctx.minimal.observableReads observable) :
    ((geometryCastSourceEquationExact h S e objectMap T).contextEquivalence.functor.obj
      W).ctx.minimal.observableReads
        (geometryCastSourceObservableComp h S e objectMap T comp W observable) := by
  cases h
  exact comp_reads W observable hread

/-- G-115-generated support comparison for the exact inverse-package lift. -/
noncomputable def generatedExactSupportComp {U : AtomCarrier.{u}}
    {X : ExtractionInstance U} (G : GeometryPackage.{u, v} U)
    (f : X ⟶ packagePoint G.core)
    (W : (exactSourceGeometry G f).site.category) :
    W.ctx.Support →
      (refinementGeometryContextForward
        ((exactPackageToRefinement U).map (exactBaseHom G f)) W).ctx.Support := by
  change W.ctx.Support →
    ((inverseCoreEquationForward G.core f).contextEquivalence.functor.obj
      W).ctx.Support
  rw [inverseCoreEquationForward_eq_geometryCast]
  exact geometryCastSourceSupportComp
    (inverseBaseObject_eq G.core f).symm
    (transportEquationReading f.doctrineHom.atomEquiv.symm
      G.core.object G.core.reading.equationReading)
    f.doctrineHom.atomEquiv
    (transportArchitectureObject f.doctrineHom.atomEquiv)
    (geometryDeconjugateEquationSystem G.core f.doctrineHom.atomEquiv)
    (geometryDeconjugateSupportComp G.core f.doctrineHom.atomEquiv) W

/-- The generated exact support comparison is natural in restriction. -/
theorem generatedExactSupportComp_naturality {U : AtomCarrier.{u}}
    {X : ExtractionInstance U} (G : GeometryPackage.{u, v} U)
    (f : X ⟶ packagePoint G.core)
    {W V : (exactSourceGeometry G f).site.category} (w : W ⟶ V) support :
    (refinementTargetContextMorphism
      (f := (exactPackageToRefinement U).map (exactBaseHom G f)) w).supportMap
        (generatedExactSupportComp G f W support) =
      generatedExactSupportComp G f V
        ((refinementSourceContextMorphism w).supportMap support) := by
  change
    (G.core.contextPreorder.morphism (leOfHom
      ((inverseCoreEquationForward G.core f).contextEquivalence.functor.map
        w))).supportMap (generatedExactSupportComp G f W support) =
      generatedExactSupportComp G f V
        (((exactSourceGeometry G f).core.contextPreorder.morphism
          (leOfHom w)).supportMap support)
  simpa only [generatedExactSupportComp] using
    (geometryCastSourceSupportComp_naturality
      (inverseBaseObject_eq G.core f).symm
      (transportEquationReading f.doctrineHom.atomEquiv.symm
        G.core.object G.core.reading.equationReading)
      f.doctrineHom.atomEquiv
      (transportArchitectureObject f.doctrineHom.atomEquiv)
      (geometryDeconjugateEquationSystem G.core f.doctrineHom.atomEquiv)
      (geometryDeconjugateSupportComp G.core f.doctrineHom.atomEquiv)
      (geometryDeconjugateSupportComp_naturality
        G.core f.doctrineHom.atomEquiv) w support)

/-- G-115-generated axis comparison for the exact inverse-package lift. -/
noncomputable def generatedExactAxisComp {U : AtomCarrier.{u}}
    {X : ExtractionInstance U} (G : GeometryPackage.{u, v} U)
    (f : X ⟶ packagePoint G.core)
    (W : (exactSourceGeometry G f).site.category) :
    W.ctx.Axis →
      (refinementGeometryContextForward
        ((exactPackageToRefinement U).map (exactBaseHom G f)) W).ctx.Axis := by
  change W.ctx.Axis →
    ((inverseCoreEquationForward G.core f).contextEquivalence.functor.obj
      W).ctx.Axis
  rw [inverseCoreEquationForward_eq_geometryCast]
  exact geometryCastSourceAxisComp
    (inverseBaseObject_eq G.core f).symm
    (transportEquationReading f.doctrineHom.atomEquiv.symm
      G.core.object G.core.reading.equationReading)
    f.doctrineHom.atomEquiv
    (transportArchitectureObject f.doctrineHom.atomEquiv)
    (geometryDeconjugateEquationSystem G.core f.doctrineHom.atomEquiv)
    (geometryDeconjugateAxisComp G.core f.doctrineHom.atomEquiv) W

/-- The generated exact axis comparison is natural in restriction. -/
theorem generatedExactAxisComp_naturality {U : AtomCarrier.{u}}
    {X : ExtractionInstance U} (G : GeometryPackage.{u, v} U)
    (f : X ⟶ packagePoint G.core)
    {W V : (exactSourceGeometry G f).site.category} (w : W ⟶ V) axis :
    (refinementTargetContextMorphism
      (f := (exactPackageToRefinement U).map (exactBaseHom G f)) w).axisMap
        (generatedExactAxisComp G f W axis) =
      generatedExactAxisComp G f V
        ((refinementSourceContextMorphism w).axisMap axis) := by
  change
    (G.core.contextPreorder.morphism (leOfHom
      ((inverseCoreEquationForward G.core f).contextEquivalence.functor.map
        w))).axisMap (generatedExactAxisComp G f W axis) =
      generatedExactAxisComp G f V
        (((exactSourceGeometry G f).core.contextPreorder.morphism
          (leOfHom w)).axisMap axis)
  simpa only [generatedExactAxisComp] using
    (geometryCastSourceAxisComp_naturality
      (inverseBaseObject_eq G.core f).symm
      (transportEquationReading f.doctrineHom.atomEquiv.symm
        G.core.object G.core.reading.equationReading)
      f.doctrineHom.atomEquiv
      (transportArchitectureObject f.doctrineHom.atomEquiv)
      (geometryDeconjugateEquationSystem G.core f.doctrineHom.atomEquiv)
      (geometryDeconjugateAxisComp G.core f.doctrineHom.atomEquiv)
      (geometryDeconjugateAxisComp_naturality
        G.core f.doctrineHom.atomEquiv) w axis)

/-- G-115-generated observable comparison for the exact inverse-package lift. -/
noncomputable def generatedExactObservableComp {U : AtomCarrier.{u}}
    {X : ExtractionInstance U} (G : GeometryPackage.{u, v} U)
    (f : X ⟶ packagePoint G.core)
    (W : (exactSourceGeometry G f).site.category) :
    W.ctx.Observable →
      (refinementGeometryContextForward
        ((exactPackageToRefinement U).map (exactBaseHom G f)) W).ctx.Observable := by
  change W.ctx.Observable →
    ((inverseCoreEquationForward G.core f).contextEquivalence.functor.obj
      W).ctx.Observable
  rw [inverseCoreEquationForward_eq_geometryCast]
  exact geometryCastSourceObservableComp
    (inverseBaseObject_eq G.core f).symm
    (transportEquationReading f.doctrineHom.atomEquiv.symm
      G.core.object G.core.reading.equationReading)
    f.doctrineHom.atomEquiv
    (transportArchitectureObject f.doctrineHom.atomEquiv)
    (geometryDeconjugateEquationSystem G.core f.doctrineHom.atomEquiv)
    (geometryDeconjugateObservableComp G.core f.doctrineHom.atomEquiv) W

/-- The generated exact observable comparison is natural in restriction. -/
theorem generatedExactObservableComp_naturality {U : AtomCarrier.{u}}
    {X : ExtractionInstance U} (G : GeometryPackage.{u, v} U)
    (f : X ⟶ packagePoint G.core)
    {W V : (exactSourceGeometry G f).site.category} (w : W ⟶ V) observable :
    (refinementTargetContextMorphism
      (f := (exactPackageToRefinement U).map
        (exactBaseHom G f)) w).observableRestrict
        (generatedExactObservableComp G f V observable) =
      generatedExactObservableComp G f W
        ((refinementSourceContextMorphism w).observableRestrict observable) := by
  change
    (G.core.contextPreorder.morphism (leOfHom
      ((inverseCoreEquationForward G.core f).contextEquivalence.functor.map
        w))).observableRestrict
        (generatedExactObservableComp G f V observable) =
      generatedExactObservableComp G f W
        (((exactSourceGeometry G f).core.contextPreorder.morphism
          (leOfHom w)).observableRestrict observable)
  simpa only [generatedExactObservableComp] using
    (geometryCastSourceObservableComp_naturality
      (inverseBaseObject_eq G.core f).symm
      (transportEquationReading f.doctrineHom.atomEquiv.symm
        G.core.object G.core.reading.equationReading)
      f.doctrineHom.atomEquiv
      (transportArchitectureObject f.doctrineHom.atomEquiv)
      (geometryDeconjugateEquationSystem G.core f.doctrineHom.atomEquiv)
      (geometryDeconjugateObservableComp G.core f.doctrineHom.atomEquiv)
      (geometryDeconjugateObservableComp_naturality
        G.core f.doctrineHom.atomEquiv) w observable)

/-- The generated exact support comparison preserves the selected reading. -/
theorem generatedExactSupportComp_reads {U : AtomCarrier.{u}}
    {X : ExtractionInstance U} (G : GeometryPackage.{u, v} U)
    (f : X ⟶ packagePoint G.core)
    (W : (exactSourceGeometry G f).site.category) support atom
    (h : W.ctx.minimal.supportReads support atom) :
    (refinementGeometryContextForward
      ((exactPackageToRefinement U).map (exactBaseHom G f)) W).ctx.minimal.supportReads
        (generatedExactSupportComp G f W support)
        (((exactPackageToRefinement U).map
          (exactBaseHom G f)).upper.atomEquiv atom) := by
  change
    ((inverseCoreEquationForward G.core f).contextEquivalence.functor.obj
      W).ctx.minimal.supportReads
        (generatedExactSupportComp G f W support)
        (f.doctrineHom.atomEquiv atom)
  simpa only [generatedExactSupportComp] using
    (geometryCastSourceSupportComp_reads
      (inverseBaseObject_eq G.core f).symm
      (transportEquationReading f.doctrineHom.atomEquiv.symm
        G.core.object G.core.reading.equationReading)
      f.doctrineHom.atomEquiv
      (transportArchitectureObject f.doctrineHom.atomEquiv)
      (geometryDeconjugateEquationSystem G.core f.doctrineHom.atomEquiv)
      (geometryDeconjugateSupportComp G.core f.doctrineHom.atomEquiv)
      (geometryDeconjugateSupportComp_reads
        G.core f.doctrineHom.atomEquiv) W support atom h)

/-- The generated exact axis comparison preserves the selected reading. -/
theorem generatedExactAxisComp_reads {U : AtomCarrier.{u}}
    {X : ExtractionInstance U} (G : GeometryPackage.{u, v} U)
    (f : X ⟶ packagePoint G.core)
    (W : (exactSourceGeometry G f).site.category) axis
    (h : W.ctx.minimal.axisReads axis) :
    (refinementGeometryContextForward
      ((exactPackageToRefinement U).map (exactBaseHom G f)) W).ctx.minimal.axisReads
        (generatedExactAxisComp G f W axis) := by
  change
    ((inverseCoreEquationForward G.core f).contextEquivalence.functor.obj
      W).ctx.minimal.axisReads (generatedExactAxisComp G f W axis)
  simpa only [generatedExactAxisComp] using
    (geometryCastSourceAxisComp_reads
      (inverseBaseObject_eq G.core f).symm
      (transportEquationReading f.doctrineHom.atomEquiv.symm
        G.core.object G.core.reading.equationReading)
      f.doctrineHom.atomEquiv
      (transportArchitectureObject f.doctrineHom.atomEquiv)
      (geometryDeconjugateEquationSystem G.core f.doctrineHom.atomEquiv)
      (geometryDeconjugateAxisComp G.core f.doctrineHom.atomEquiv)
      (geometryDeconjugateAxisComp_reads
        G.core f.doctrineHom.atomEquiv) W axis h)

/-- The generated exact observable comparison preserves the selected reading. -/
theorem generatedExactObservableComp_reads {U : AtomCarrier.{u}}
    {X : ExtractionInstance U} (G : GeometryPackage.{u, v} U)
    (f : X ⟶ packagePoint G.core)
    (W : (exactSourceGeometry G f).site.category) observable
    (h : W.ctx.minimal.observableReads observable) :
    (refinementGeometryContextForward
      ((exactPackageToRefinement U).map
        (exactBaseHom G f)) W).ctx.minimal.observableReads
          (generatedExactObservableComp G f W observable) := by
  change
    ((inverseCoreEquationForward G.core f).contextEquivalence.functor.obj
      W).ctx.minimal.observableReads
        (generatedExactObservableComp G f W observable)
  simpa only [generatedExactObservableComp] using
    (geometryCastSourceObservableComp_reads
      (inverseBaseObject_eq G.core f).symm
      (transportEquationReading f.doctrineHom.atomEquiv.symm
        G.core.object G.core.reading.equationReading)
      f.doctrineHom.atomEquiv
      (transportArchitectureObject f.doctrineHom.atomEquiv)
      (geometryDeconjugateEquationSystem G.core f.doctrineHom.atomEquiv)
      (geometryDeconjugateObservableComp G.core f.doctrineHom.atomEquiv)
      (geometryDeconjugateObservableComp_reads
        G.core f.doctrineHom.atomEquiv) W observable h)

end UpperGeometryCleavage

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct.UpperGeometryCleavage
