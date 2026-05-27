import Formal.Arch.Evolution.SFTInterfaceBoundary
import Formal.Arch.Examples.AtomPureAATExamples

namespace Formal.Arch.AtomicExamples

/--
The no-edge pure Atom theorem suite read as an AAT theorem-status item for
the SFT interface, after supplying the selected Signature arrangement package.
-/
noncomputable def noEdgePureAtomSuiteTheoremStatus :
    AATTheoremStatus :=
  AATTheoremStatus.ofPureAtomTheoremSuite
    noEdgeArchitectureLawModel
    noEdgeAtomAxiomatizedPureTheoremSuite
    noEdgeStaticAtomArrangementPackage
    True True True True True

theorem noEdgePureAtomSuiteTheoremStatus_records_theoremPackage :
    noEdgePureAtomSuiteTheoremStatus.RecordsTheoremPackage := by
  exact
    AATTheoremStatus.records_theoremPackage_of_pureAtomTheoremSuite
      noEdgeArchitectureLawModel
      noEdgeAtomAxiomatizedPureTheoremSuite
      noEdgeStaticAtomArrangementPackage

end Formal.Arch.AtomicExamples
