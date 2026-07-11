import ResearchLean.AG.SFTDynamics.TraceSite

/-!
SFT v2 Lean tower, target **L2** (skeleton note §10; SFT v2 text Part II).

This file fixes the schema layer of forces and proves the distant-commutation
theorem (SFT 定理 14.3 遠隔可換 の Lean 版):

* `ForceSchema` carries a support, a closure assignment, and a local action
  (SFT 定義 11.1 の有限読み).  The two locality fields are exactly the two
  axioms of the text: reading locality (SFT 公理 11.2) and effect containment
  (SFT 公理 11.5).
* `distant_commute`: if the closures of two schemas are disjoint, both
  application orders yield the same configuration — the trivial-transport
  commute of SFT 定理 14.3, i.e. the composite bigon closes and the force
  curvature vanishes (SFT 定義 15.1 の `δ(f, g) = 0` 側).

Simplifications relative to the text, recorded here as the L2 boundary:
actions are total (the `dom_s` field of SFT 定義 11.1 is treated as everywhere
satisfied, so hypothesis (iv) of 定理 14.3 is trivially met), and the closure
assignment is taken as given selected data — the over-approximation contract
of SFT 原則 22.1 (`cl ⊇ footprint`) is an interpretation-side obligation, not
proved here.  Nothing is claimed about transports along nontrivial
connections, about applied forces on trace edges, or about real diffs.
-/

namespace ResearchLean.AG
namespace SFTDynamics

/--
A force schema over contexts `Ctx` with coefficients `Coeff`
(SFT 定義 11.1 の有限読み).

`reads_within` is reading locality (SFT 公理 11.2): the action on the closure
depends only on the configuration restricted to the closure.  `effect_within`
is effect containment (SFT 公理 11.5): outside the closure the action is the
identity, including restriction-induced effects.
-/
structure ForceSchema (Ctx : Type u) (Coeff : Type v) where
  support : Ctx → Prop
  closure : Ctx → Prop
  support_subset : ∀ c, support c → closure c
  act : FieldConfig Ctx Coeff → FieldConfig Ctx Coeff
  reads_within :
    ∀ φ ψ : FieldConfig Ctx Coeff,
      (∀ c, closure c → φ c = ψ c) →
      ∀ c, closure c → act φ c = act ψ c
  effect_within :
    ∀ (φ : FieldConfig Ctx Coeff) (c : Ctx), ¬ closure c → act φ c = φ c

namespace ForceSchema

variable {Ctx : Type u} {Coeff : Type v}

/-- Disjointness of closures (the hypothesis (ii) of SFT 定理 14.3). -/
def DisjointClosures (f g : ForceSchema Ctx Coeff) : Prop :=
  ∀ c, ¬ (f.closure c ∧ g.closure c)

/--
Under disjoint closures, the other schema leaves the closure of `f`
untouched, so `f` cannot distinguish `g.act φ` from `φ` on its closure.
-/
theorem act_act_eq_act_left
    (f g : ForceSchema Ctx Coeff) (h : DisjointClosures f g)
    (φ : FieldConfig Ctx Coeff) {c : Ctx} (hc : f.closure c) :
    f.act (g.act φ) c = f.act φ c := by
  refine f.reads_within (g.act φ) φ ?_ c hc
  intro x hx
  have hxg : ¬ g.closure x := fun hg => h x ⟨hx, hg⟩
  exact g.effect_within φ x hxg

/--
**遠隔可換 (SFT 定理 14.3 の Lean 版)**: if two force schemas have disjoint
closures, both application orders produce the same configuration.  This is the
trivial-transport commute; equivalently the composite bigon closes and the
force curvature `δ(f, g)` vanishes (SFT 定義 14.1・15.1).
-/
theorem distant_commute
    (f g : ForceSchema Ctx Coeff) (h : DisjointClosures f g)
    (φ : FieldConfig Ctx Coeff) :
    f.act (g.act φ) = g.act (f.act φ) := by
  funext c
  by_cases hf : f.closure c
  · have hg : ¬ g.closure c := fun hgc => h c ⟨hf, hgc⟩
    calc f.act (g.act φ) c
        = f.act φ c := act_act_eq_act_left f g h φ hf
      _ = g.act (f.act φ) c := (g.effect_within (f.act φ) c hg).symm
  · by_cases hg : g.closure c
    · have h' : DisjointClosures g f := fun x hx => h x ⟨hx.2, hx.1⟩
      calc f.act (g.act φ) c
          = g.act φ c := f.effect_within (g.act φ) c hf
        _ = g.act (f.act φ) c := (act_act_eq_act_left g f h' φ hg).symm
    · calc f.act (g.act φ) c
          = g.act φ c := f.effect_within (g.act φ) c hf
        _ = φ c := g.effect_within φ c hg
        _ = f.act φ c := (f.effect_within φ c hf).symm
        _ = g.act (f.act φ) c := (g.effect_within (f.act φ) c hg).symm

/--
The merged configuration of two schemas applied in either order.  Under
disjoint closures this is order-independent (SFT 定理 21.1 の二枝の場合の
Lean shadow).
-/
def mergeConfig (f g : ForceSchema Ctx Coeff)
    (φ : FieldConfig Ctx Coeff) : FieldConfig Ctx Coeff :=
  f.act (g.act φ)

theorem mergeConfig_comm
    (f g : ForceSchema Ctx Coeff) (h : DisjointClosures f g)
    (φ : FieldConfig Ctx Coeff) :
    mergeConfig f g φ = mergeConfig g f φ :=
  distant_commute f g h φ

end ForceSchema

end SFTDynamics
end ResearchLean.AG
