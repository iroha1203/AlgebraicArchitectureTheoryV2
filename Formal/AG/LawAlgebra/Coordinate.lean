import Formal.AG.Site.Context

namespace AAT.AG
namespace LawAlgebra

universe u v

/--
III.定義3.1: coordinate namespace for architecture coordinates.

These labels classify the source of a coordinate reading. They are labels only:
the coordinate family below supplies the actual local data read on a context.
-/
inductive CoordinateLabel where
  | atom
  | signature
  | state
  | effect
  | authority
  | semantic
  | runtime
  | boundary
  deriving DecidableEq, Repr

/--
III.定義3.1: a single architecture coordinate on a context.

The coordinate reads selected local data on `W` into a coefficient carrier `R`.
No algebraic equation is imposed at this layer.
-/
structure ArchitectureCoordinate {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    (_W : Site.ArchitectureContext A) (R : Type v) where
  label : CoordinateLabel
  LocalData : Type u
  read : LocalData -> R

namespace ArchitectureCoordinate

/-- III.定義3.1: evaluate a coordinate on its local datum. -/
def eval {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {W : Site.ArchitectureContext A} {R : Type v}
    (c : ArchitectureCoordinate W R) (x : c.LocalData) : R :=
  c.read x

/-- III.定義3.1: evaluation is the stored reading function. -/
theorem eval_eq_read {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {W : Site.ArchitectureContext A} {R : Type v}
    (c : ArchitectureCoordinate W R) :
    c.eval = c.read :=
  rfl

end ArchitectureCoordinate

/--
III.定義3.1: a context-indexed family of architecture coordinates.

`Coord` is the Lean form of `Coord_X(W)`. Each coordinate has a namespace label
and a type of local data that later structural relations can reference.
-/
structure CoordinateFamily {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    (_W : Site.ArchitectureContext A) where
  Coord : Type u
  label : Coord -> CoordinateLabel
  LocalData : Coord -> Type u

namespace CoordinateFamily

/-- III.定義3.1: the coordinate type `Coord_X(W)` of a selected family. -/
abbrev CoordX {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {W : Site.ArchitectureContext A} (F : CoordinateFamily W) : Type u :=
  F.Coord

/-- III.定義3.1: the label attached to a coordinate. -/
def namespaceLabel {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {W : Site.ArchitectureContext A} (F : CoordinateFamily W)
    (c : F.CoordX) : CoordinateLabel :=
  F.label c

/-- III.定義3.1: the local data type read by a coordinate. -/
def localData {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {W : Site.ArchitectureContext A} (F : CoordinateFamily W)
    (c : F.CoordX) : Type u :=
  F.LocalData c

end CoordinateFamily

/--
III.定義3.1: a coefficient-valued reading of all coordinates in a family.

This is the abstract `Coord_X(W)`-indexed reading function used before law
equations or structural quotienting are imposed.
-/
structure CoordinateReading {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {W : Site.ArchitectureContext A} (F : CoordinateFamily W) (R : Type v) where
  read : (c : F.CoordX) -> F.localData c -> R

namespace CoordinateReading

/-- III.定義3.1: evaluate the reading attached to one coordinate. -/
def eval {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {W : Site.ArchitectureContext A} {F : CoordinateFamily W} {R : Type v}
    (rho : CoordinateReading F R) (c : F.CoordX) (x : F.localData c) : R :=
  rho.read c x

/-- III.定義3.1: evaluation is the stored family reading. -/
theorem eval_eq_read {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {W : Site.ArchitectureContext A} {F : CoordinateFamily W} {R : Type v}
    (rho : CoordinateReading F R) :
    rho.eval = rho.read :=
  rfl

end CoordinateReading

end LawAlgebra
end AAT.AG
