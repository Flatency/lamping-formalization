import Lamping.Lamping.GlobalGraphSteps
import Lamping.Graph.SelectedNodes
namespace Lamping.AG
open Graph

private def directInternal : Pairing (Bool ⊕ (Empty × Bool)) where
  mate := fun x => match x with
    | .inl d => .inl (!d)
    | .inr (v,_) => nomatch v
  involutive := by rintro (d | ⟨v,d⟩); cases d <;> rfl; exact nomatch v
  fixedPointFree := by rintro (d | ⟨v,d⟩); cases d <;> (intro same; cases same); exact nomatch v

section
variable {s : Schema} {K B W : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W]
variable {kept : K → Label signature}

/-- An actual direct principal-wire Site is also a PathSite with no deleted
transparent vertices. Every other wire vertex remains in the outside carrier. -/
def Site.pathSite (site : Site s kept (B:=B) (W:=W)) :
    PathSite s kept (B:=B) (W:=W) (V:=Empty) where
  wire := site.wire
  internal := directInternal
  connected := by
    rintro (d | ⟨v,d⟩)
    · cases d with
      | false => exact .refl _
      | true => exact .segment (.inl false)
    · exact nomatch v
  wiring := by
    rintro (d | ⟨v,d⟩)
    · cases d with
      | false =>
        change (fragmentEnd _ _) (site.wire (.inl ⟨.inr (.inl ()),.inl ()⟩))= _
        rw [site.principal]; rfl
      | true =>
        have reverse := site.wire.involutive (.inl ⟨.inr (.inl ()),.inl ()⟩)
        rw [site.principal] at reverse
        change (fragmentEnd _ _) (site.wire (.inl ⟨.inr (.inr ()),.inl ()⟩))= _
        rw [reverse]; rfl
    · exact nomatch v

/-- Actual physical rewritability follows from a direct Site witness;
no path invariant, matching term, or reduction correctness is assumed. -/
theorem Site.graph_step (site : Site s kept (B:=B) (W:=W)) :
    GraphStep s (ActualNet.ofNet site.net) (ActualNet.ofNet site.pathSite.reduce) :=
  GraphStep.site kept site.pathSite

theorem Site.not_graph_normal (site : Site s kept (B:=B) (W:=W)) :
    ¬GraphNormal (ActualNet.ofNet site.net) := by
  intro normal
  exact normal s _ site.graph_step
end
end Lamping.AG
