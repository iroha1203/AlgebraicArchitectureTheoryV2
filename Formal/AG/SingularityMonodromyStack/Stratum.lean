import Formal.AG.Derived
import Formal.AG.Atom.Signature
import Formal.AG.LawAlgebra.StandardScheme
import Formal.AG.Site.Topology

noncomputable section

namespace AAT.AG
namespace SingularityMonodromyStack

universe u v w x y

open CategoryTheory

/--
VI.定義2.1: the selected role used to read an architecture stratum.

These constructors are labels for the carrier chosen by the Part VI geometry.
They do not assert that every such role is present in every architecture
scheme.
-/
inductive StratumRole where
  | component
  | boundary
  | service
  | sharedState
  | authorityHub
  | semanticBoundary
  | runtimeInteraction
  | adapter
  | legacy
  | experimentalFeature
  | custom
  deriving DecidableEq

/--
VI.原則2.2 as data: a stratum reading is relative to a selected Atom
vocabulary, law universe, coverage topology, signature axes, and coefficient
structure.

The generated topology is exposed by `coverageTopology`; this structure only
records the selected inputs. It does not infer a new observation layer or
extend the law universe.
-/
structure StratumReadingParameter {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    (S : Site.AATSite A) where
  signatureAxes : SignatureAxes U
  Coeff : Type u
  selectedCoeff : Coeff

namespace StratumReadingParameter

variable {U : AtomCarrier.{u}} {A : ArchitectureObject U}
variable {S : Site.AATSite A}

/-- VI.原則2.2: the Grothendieck topology selected by the reading data. -/
def coverageTopology (_P : StratumReadingParameter S) :
    GrothendieckTopology S.category :=
  S.topology

/-- VI.原則2.2: expose the selected coefficient structure. -/
theorem selectedCoeff_eq (P : StratumReadingParameter S) :
    P.selectedCoeff = P.selectedCoeff :=
  rfl

end StratumReadingParameter

/--
VI.定義2.1: an architecture stratum inside a selected architecture scheme.

The carrier is a selected subset of an explicit point type. The predicates keep
the intended subobject, local-closedness, decoration compatibility, and reading
compatibility assumptions visible without constructing general stratification
theory in this implementation step.

Implementation notes: the stratum stores the raw ambient system and its
canonical `StandardArchitectureScheme`; ringed and atlas data are recovered
from those owners rather than from a legacy Scheme package.
-/
structure ArchitectureStratum {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} (P : StratumReadingParameter S) (k : Type v) [CommRing k] where
  raw : LawAlgebra.RawAmbientRestrictionSystem S k
  [sheafify : HasSheafify S.topology (LawAlgebra.AATCommAlgCat k)]
  geometry :
    let _universeW : Type w := ULift.{w} Unit
    let _universeX : Type x := ULift.{x} Unit
    LawAlgebra.StandardArchitectureScheme raw
  Point : Type y
  carrier : Set Point
  role : StratumRole
  label : String
  selectedSubobject : Prop
  selectedSubobject_cert : selectedSubobject
  locallyClosed : Prop
  locallyClosed_cert : locallyClosed
  decorationCompatible : Prop
  decorationCompatible_cert : decorationCompatible
  readingCompatible : Prop
  readingCompatible_cert : readingCompatible

namespace ArchitectureStratum

variable {U : AtomCarrier.{u}} {A : ArchitectureObject U}
variable {S : Site.AATSite A}
variable {P : StratumReadingParameter S}
variable {k : Type v} [CommRing k]

/-- VI.定義2.1: membership in the selected stratum carrier. -/
def Mem (X : ArchitectureStratum.{u, v, w, x, y} P k) (p : X.Point) : Prop :=
  p ∈ X.carrier

/-- VI.定義2.1: the carrier is the selected subset recorded by the stratum. -/
theorem mem_iff {X : ArchitectureStratum.{u, v, w, x, y} P k} {p : X.Point} :
    X.Mem p ↔ p ∈ X.carrier :=
  Iff.rfl

/-- VI.定義2.1: the stratum records selected-subobject compatibility. -/
theorem selectedSubobject_holds (X : ArchitectureStratum.{u, v, w, x, y} P k) :
    X.selectedSubobject :=
  X.selectedSubobject_cert

/-- VI.定義2.1: the stratum records locally closed reading data. -/
theorem locallyClosed_holds (X : ArchitectureStratum.{u, v, w, x, y} P k) :
    X.locallyClosed :=
  X.locallyClosed_cert

/-- VI.定義2.1: the stratum records decoration compatibility. -/
theorem decorationCompatible_holds
    (X : ArchitectureStratum.{u, v, w, x, y} P k) :
    X.decorationCompatible :=
  X.decorationCompatible_cert

/-- VI.定義2.1: the stratum records compatibility with the selected reading. -/
theorem readingCompatible_holds
    (X : ArchitectureStratum.{u, v, w, x, y} P k) :
    X.readingCompatible :=
  X.readingCompatible_cert

end ArchitectureStratum

end SingularityMonodromyStack
end AAT.AG
