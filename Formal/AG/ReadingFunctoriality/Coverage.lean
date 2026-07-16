import Formal.AG.ReadingFunctoriality.Core
import Formal.AG.Site.FinitePosetGeometry
import Formal.AG.Cohomology.CechComplex
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import Mathlib.CategoryTheory.Sites.Limits
import Mathlib.CategoryTheory.Sites.LeftExact
import Mathlib.CategoryTheory.Sites.Abelian
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Adjunction.Restrict
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map

/-!
# Coverage and cohomology functoriality

This module owns topology refinement, selected-cover refinement, canonical
Čech functoriality, and actual sheaf-cohomology comparison fixed by Part 4
SD3–SD5.
-/
