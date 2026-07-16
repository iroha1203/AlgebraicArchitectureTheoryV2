import Formal.AG.ReadingFunctoriality.Core
import Formal.AG.ReadingFunctoriality.Coverage
import Formal.AG.LawAlgebra.ClosedEquationalGeometry
import Formal.AG.Derived.Intersection
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.Algebra.Category.ModuleCat.Descent
import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.Algebra.Category.Ring.Under.Basic
import Mathlib.Algebra.Category.Ring.Under.Limits
import Mathlib.Algebra.Module.TransferInstance
import Mathlib.CategoryTheory.Sites.Adjunction
import Mathlib.CategoryTheory.Sites.PreservesSheafification
import Mathlib.CategoryTheory.Sites.Whiskering
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
import Mathlib.RingTheory.RingHom.Flat

/-!
# Coefficient-change functoriality

This module owns direct closed-equational reuse and flat coefficient change
for raw systems, standard schemes, ideal geometry, Tor, linear Čech
cohomology, and actual sheaf cohomology fixed by Part 4 SD2 and SD6–SD8.
-/
