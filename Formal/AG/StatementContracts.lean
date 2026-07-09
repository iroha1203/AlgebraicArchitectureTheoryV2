import Formal.AG.Site.Geometry

/-!
Statement contracts for fixed Lean statements.

Files under `Formal/AG/StatementContracts*.lean` contain only elaboration
contracts of the form

```lean
example : <fixed signature> := <implemented theorem>
```

They are imported by `Formal/AG.lean`, so `lake build` checks that the fixed
signature and the implemented theorem still match definitionally.
-/

namespace AAT.AG

universe u

open CategoryTheory

/--
Sample contract for the §5.2 placement convention: the existing site topology
theorem still has exactly the fixed statement below.
-/
example {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    (S : Site.AATSite A) :
    S.topology = Site.AATGrothendieckTopology S.requirements S.overlap :=
  Site.AATSite.topology_eq S

end AAT.AG
