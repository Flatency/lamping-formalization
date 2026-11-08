import Lamping.Lamping.ActionReverseSourceBlocks
namespace Lamping.AG
open Graph
section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable {g : Net signature N B W}
/-- Reflect the actual selected first node turn of an ordinary Forward path. -/
theorem Forward.actual_node_ports (node : N) (p q : Port (g.label node).sort)
    (rest : List (Endpoint g))
    (forward : Forward g (g.wire (.inl ⟨node,p⟩)::(.inl ⟨node,q⟩)::rest)) :
    ForwardPorts (g.label node).sort p q := by
  cases forward with
  | node actual incoming outgoing arrives leaves direction tail =>
    rw [Pairing.involutive] at arrives
    cases arrives
    cases leaves
    exact direction
  | transparent vertex side arrives leaves tail =>
    rw [Pairing.involutive] at arrives
    cases arrives
end
section
variable {s : Schema} {K B W V : Type}
variable [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K → Label signature} (site : PathSite s kept (B:=B) (W:=W) (V:=V))

/-- An actual ordinary passive-to-passive block can only be the application's
context-to-argument turn. A lambda binding is never traversed, and reverse
proper-node orientations are excluded by the given physical Forward path. -/
theorem PathSite.forward_passive_aux_ports
    (proper : s.passive=.app ∨s.passive=.lam) (p q : Aux s.passive)
    (rest : List (Endpoint site.net))
    (forward : Forward site.net (site.net.wire (.inl ⟨.inr (.inr ()),.inr p⟩)::
      (.inl ⟨.inr (.inr ()),.inr q⟩)::rest)) :
    s.passive=.app ∧HEq p false ∧HEq q true := by
  have direction := forward.actual_node_ports (g:=site.net) (.inr (.inr ())) (.inr p) (.inr q) rest
  have reflect (op : Op) (left right : Aux op) (proper : op=.app ∨op=.lam)
      (direction : ForwardPorts (.op op) (.inr left) (.inr right)) :
      op=.app ∧HEq left false ∧HEq right true := by
    rcases proper with app|lam
    · subst op
      refine ⟨rfl,heq_of_eq (Sum.inr.inj direction.1),?_⟩
      rcases direction.2 with impossible|same
      · cases impossible
      · exact heq_of_eq (Sum.inr.inj same)
    · subst op
      cases direction.1
  exact reflect s.passive p q proper direction
end
end Lamping.AG
