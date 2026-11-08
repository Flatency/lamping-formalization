import Lamping.Lamping.TransparentCorridors
import Lamping.Graph.RightRestriction
namespace Lamping.AG
open Graph
section
variable (s : Schema) {K B W V : Type}
variable [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable (kept : K → Label signature)

/-- The selected physical corridor after carrier renaming. The selection is
exactly the actual W departures; no internal pairing or reachability proof is
an input. -/
structure SelectedCorridor where
  wire : Pairing (End signature (K ⊕ (Unit ⊕ Unit)) B (W ⊕ V) (ambientLabel s kept))
  edges : List (End signature (K ⊕ (Unit ⊕ Unit)) B (W ⊕ V) (ambientLabel s kept))
  start : edges.head?=some (.inl ⟨.inr (.inl ()),.inl ()⟩)
  finish : edges.getLast?=some (wire (.inl ⟨.inr (.inr ()),.inl ()⟩))
  transparent : ∀ e f,(e,f)∈edges.zip edges.tail →
    ∃ w d,wire e=.inr (.inr (w,d)) ∧f=.inr (.inr (w,!d))
  selectedVertices : ∀ w,(∃ d,(.inr (.inr (w,d)))∈edges) ↔∃ v,w=.inr v

variable {s kept}

def SelectedCorridor.net (corridor : SelectedCorridor s kept (B:=B) (W:=W) (V:=V)) :
    Net signature (K ⊕ (Unit ⊕ Unit)) B (W ⊕ V) := ⟨ambientLabel s kept,corridor.wire⟩

def SelectedCorridor.route (corridor : SelectedCorridor s kept (B:=B) (W:=W) (V:=V)) :
    TransparentCorridor corridor.net where
  first := ⟨.inr (.inl ()),.inl ()⟩
  last := ⟨.inr (.inr ()),.inl ()⟩
  edges := corridor.edges
  start := corridor.start
  finish := corridor.finish
  transparent := corridor.transparent

private theorem SelectedCorridor.map_internal
    (corridor : SelectedCorridor s kept (B:=B) (W:=W) (V:=V))
    (e : Endpoint corridor.net) (member : corridor.route.internal e) :
    ∃ i,fragmentEnd corridor.net.label (pathPartition s V) e=.inr i := by
  rcases member with first |last |⟨w,d,selected,atVertex⟩
  · subst e; exact ⟨.inl false,rfl⟩
  · subst e; exact ⟨.inl true,rfl⟩
  · obtain ⟨v,same⟩ := (corridor.selectedVertices w).mp selected
    subst w
    subst e
    exact ⟨.inr (v,d),rfl⟩

/-- Actual finite-route geometry proves that the selected internal ends are
closed under the original wire pairing. No closed-cut certificate is assumed. -/
theorem SelectedCorridor.internal_closed
    (corridor : SelectedCorridor s kept (B:=B) (W:=W) (V:=V)) :
    ∀ i e,corridor.wire.rename (fragmentEnd corridor.net.label (pathPartition s V)) (.inr i)≠.inl e := by
  intro i e impossible
  let naming := fragmentEnd (B:=B) (W:=W) corridor.net.label (pathPartition s V)
  let original := naming.invFun (.inr i)
  have selected : corridor.route.internal original := by
    cases i with
    | inl d => cases d <;> first | exact Or.inl rfl | exact Or.inr (Or.inl rfl)
    | inr vd =>
      obtain ⟨v,d⟩ := vd
      exact Or.inr (Or.inr ⟨.inr v,d,(corridor.selectedVertices _).mpr ⟨v,rfl⟩,rfl⟩)
  obtain ⟨j,inside⟩ := corridor.map_internal _ (corridor.route.wire_internal original selected)
  change naming (corridor.wire original)=.inl e at impossible
  change naming (corridor.wire original)=.inr j at inside
  rw [inside] at impossible
  cases impossible

/-- The internal pairing is computed from the actual whole pairing. -/
def SelectedCorridor.internalPairing
    (corridor : SelectedCorridor s kept (B:=B) (W:=W) (V:=V)) : Pairing (Bool ⊕ (V × Bool)) :=
  (corridor.wire.rename (fragmentEnd corridor.net.label (pathPartition s V))).restrictRight corridor.internal_closed

theorem SelectedCorridor.internal_wiring
    (corridor : SelectedCorridor s kept (B:=B) (W:=W) (V:=V)) (i : Bool ⊕ (V × Bool)) :
    corridor.wire.rename (fragmentEnd corridor.net.label (pathPartition s V)) (.inr i)=
      .inr (corridor.internalPairing i) :=
  Pairing.restrictRight_mate _ corridor.internal_closed i
end
end Lamping.AG
