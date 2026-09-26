import ResearchLean.AG.LocalSemanticReconstruction.IndependentAATPrimitiveReconstruction
import Formal.Util.AssertStandardAxioms

/-! The common AAT reader preserves every primitive Hom point evaluation.
Application-specific decoders may choose finite query subsets from this same
table without changing the native or local Hom under consideration. -/

namespace AAT.AG.LocalSemanticReconstruction.FiniteCommonHomReading

open CategoryTheory
open IndependentAATPrimitiveReconstruction

universe u v

/-- Pointwise evaluation of the main common reader is the direct primitive
native evaluation for all four parameter branches and every native Hom. -/
theorem homPoint_read (parameter : Parameter.{u, v})
    {source target : NativeCategory parameter} (morphism : source ⟶ target)
    (query : HomQuery parameter) :
    localHomTable parameter ((reading parameter).map morphism) query =
      nativeHomTable parameter morphism query := by
  have h := congrArg homTable (localTable_read parameter morphism)
  exact congrFun (by simpa [localTable, nativeTable] using h) query

/-- The same equality holds on any explicitly supplied finite selection of
primitive Hom queries; its proof does not require the ambient query type to
be finite. -/
theorem finiteHomSupport_read (parameter : Parameter.{u, v})
    {source target : NativeCategory parameter} (morphism : source ⟶ target)
    (support : Finset (HomQuery parameter)) :
    ∀ query : {query // query ∈ support},
      localHomTable parameter ((reading parameter).map morphism) query.1 =
        nativeHomTable parameter morphism query.1 := by
  intro query
  exact homPoint_read parameter morphism query.1

#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.FiniteCommonHomReading

end AAT.AG.LocalSemanticReconstruction.FiniteCommonHomReading
