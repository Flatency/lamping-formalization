import Lamping.Lamping.PathRewrite
import Lamping.Lamping.Encoding
namespace Lamping.AG
open Graph Lambda

/-- Actual finite graph carriers can change after rewiring. Boundary names
remain fixed; no semantic invariant is a field of this representation. -/
structure ActualNet (B : Type) [FiniteNames B] where
  Node : Type
  Wire : Type
  nodesFinite : FiniteNames Node
  wiresFinite : FiniteNames Wire
  net : @Net signature Node B Wire nodesFinite inferInstance wiresFinite
attribute [instance] ActualNet.nodesFinite ActualNet.wiresFinite

namespace ActualNet
def ofNet {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
    (g : Net signature N B W) : ActualNet B :=
  ⟨N,W,inferInstance,inferInstance,g⟩
def initial (t : Term) : ActualNet (Boundary t) := ofNet (encode 0 t).net
end ActualNet

section
variable {B : Type} [FiniteNames B]

/-- Exactly a physical AG PathSite replacement, up to boundary-fixing graph
isomorphisms. The schema index records the actual rule that was applied. -/
inductive GraphStep (schema : Schema) : ActualNet B → ActualNet B → Prop where
  | atSite {K W V : Type} [FiniteNames K] [FiniteNames W] [FiniteNames V]
      (kept : K → Label signature) (site : PathSite schema kept (B:=B) (W:=W) (V:=V))
      {source target : ActualNet B}
      (sourceIso : NetIso source.net site.net) (targetIso : NetIso site.reduce target.net) :
      GraphStep schema source target

namespace GraphStep
theorem iso_source {s : Schema} {g h k : ActualNet B}
    (step : GraphStep s h k) (iso : NetIso g.net h.net) : GraphStep s g k := by
  cases step with
  | atSite kept site before after => exact .atSite kept site (iso.trans before) after

theorem iso_target {s : Schema} {g h k : ActualNet B}
    (step : GraphStep s g h) (iso : NetIso h.net k.net) : GraphStep s g k := by
  cases step with
  | atSite kept site before after => exact .atSite kept site before (after.trans iso)

theorem site {s : Schema} {K W V : Type} [FiniteNames K] [FiniteNames W] [FiniteNames V]
    (kept : K → Label signature) (site : PathSite s kept (B:=B) (W:=W) (V:=V)) :
    GraphStep s (ActualNet.ofNet site.net) (ActualNet.ofNet site.reduce) :=
  .atSite kept site (.refl _) (.refl _)
end GraphStep

/-- A finite physical rewrite trace. An isomorphism at zero steps changes
only names; it never contributes a beta or an auxiliary event. -/
inductive GraphTrace : ActualNet B → ActualNet B → List Schema → Prop where
  | iso {g h : ActualNet B} (same : NetIso g.net h.net) : GraphTrace g h []
  | cons {g h k : ActualNet B} {s : Schema} {ss : List Schema}
      (step : GraphStep s g h) (tail : GraphTrace h k ss) : GraphTrace g k (s::ss)

namespace GraphTrace
theorem refl (g : ActualNet B) : GraphTrace g g [] := .iso (.refl _)

theorem single {s : Schema} {g h : ActualNet B} (step : GraphStep s g h) :
    GraphTrace g h [s] := .cons step (.refl _)

theorem iso_source {g h k : ActualNet B} {ss : List Schema}
    (trace : GraphTrace h k ss) (iso : NetIso g.net h.net) : GraphTrace g k ss := by
  cases trace with
  | iso same => exact .iso (iso.trans same)
  | cons step tail => exact .cons (step.iso_source iso) tail

theorem iso_target {g h k : ActualNet B} {ss : List Schema}
    (trace : GraphTrace g h ss) (iso : NetIso h.net k.net) : GraphTrace g k ss := by
  induction trace with
  | iso same => exact .iso (same.trans iso)
  | cons step tail ih => exact .cons step (ih iso)

theorem trans {g h k : ActualNet B} {ss tt : List Schema}
    (first : GraphTrace g h ss) (second : GraphTrace h k tt) : GraphTrace g k (ss++tt) := by
  induction first with
  | iso same => exact second.iso_source same
  | cons step tail ih => exact .cons step (ih second)
end GraphTrace

def GraphReachable (g h : ActualNet B) : Prop := ∃ ss, GraphTrace g h ss

def GraphNormal (g : ActualNet B) : Prop := ∀ s h, ¬GraphStep s g h

theorem GraphReachable.refl (g : ActualNet B) : GraphReachable g g := ⟨[],.refl _⟩
theorem GraphReachable.trans {g h k : ActualNet B}
    (first : GraphReachable g h) (second : GraphReachable h k) : GraphReachable g k := by
  obtain ⟨ss,first⟩ := first
  obtain ⟨tt,second⟩ := second
  exact ⟨ss++tt,first.trans second⟩
end
end Lamping.AG
