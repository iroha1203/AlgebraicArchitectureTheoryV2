import Formal.Arch.Atom.Composition

namespace Formal.Arch
namespace AAT

universe u v

/--
Composition graph over selected atoms.

The graph does not create atoms; it records that every distinct selected atom
pair composes through the shape presentation.
-/
structure CompositionGraph {system : AtomAxiomSystem.{u, v}}
    (presentation : AtomShapePresentation system)
    (atoms : system.Atom -> Prop) where
  compatiblePairs :
    ∀ {left right},
      atoms left ->
      atoms right ->
      left ≠ right ->
        CompatibleComposition
          (AtomShapeOf presentation left)
          (AtomShapeOf presentation right)
  graphBoundary : Prop

namespace CompositionGraph

/-- Selected distinct atom pairs are compatible in the graph. -/
def compatible_pairs {system : AtomAxiomSystem.{u, v}}
    {presentation : AtomShapePresentation system}
    {atoms : system.Atom -> Prop}
    (graph : CompositionGraph presentation atoms)
    {left right : system.Atom}
    (hLeft : atoms left)
    (hRight : atoms right)
    (hDistinct : left ≠ right) :
    CompatibleComposition
      (AtomShapeOf presentation left)
      (AtomShapeOf presentation right) :=
  graph.compatiblePairs hLeft hRight hDistinct

end CompositionGraph

end AAT
end Formal.Arch
