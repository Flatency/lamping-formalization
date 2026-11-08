import Lamping.Lamping.FlowBalance
import Lamping.Lamping.InitialAccessWords
namespace Lamping.AG
open Graph
section
variable {K R B F W V : Type} [FiniteNames K] [FiniteNames R] [FiniteNames B]
  [FiniteNames F] [FiniteNames W] [FiniteNames V]
variable (c : Net signature K (B⊕F) W) (r : Net signature R F V)
variable (cn : K → Bool) (rn : R → Bool) (bp : B → Bool) (fp : F → Bool) (cw : W → Bool) (rv : V → Bool)

theorem flowEndpoint_plugLeft (e : Endpoint c) :
    flowEndpoint (plug c r) (Sum.elim cn rn) bp (plugPolarity fp cw rv)
      ((plugEnd c.label r.label) (.inl e)) =
    flowEndpoint c cn (Sum.elim bp (fun f => !(fp f))) cw e := by
  rcases e with ⟨n,p⟩ | ((b|f) | ⟨w,d⟩) <;> rfl

theorem flowEndpoint_plugRight (e : Endpoint r) :
    flowEndpoint (plug c r) (Sum.elim cn rn) bp (plugPolarity fp cw rv)
      ((plugEnd c.label r.label) (.inr e)) = flowEndpoint r rn fp rv e := by
  rcases e with ⟨n,p⟩ | (f | ⟨w,d⟩)
  · rfl
  · change (!(!(fp f))) = fp f
    simp
  · rfl

def FlowBalance.plug (left : FlowBalance c (Sum.elim bp (fun f => !(fp f))))
    (right : FlowBalance r fp) : FlowBalance (Graph.plug c r) bp where
  nodes := Sum.elim left.nodes right.nodes
  vertices := plugPolarity fp left.vertices right.vertices
  wiring e := by
    rw [←(plugEnd c.label r.label).right_inv e]
    generalize (plugEnd c.label r.label).invFun e = old
    cases old with
    | inl x =>
      change flowEndpoint (Graph.plug c r) _ _ _ ((Graph.plug c r).wire (AG.plugLeft c r x)) = _
      rw [plugLeft_wire]
      simp only [AG.plugLeft]
      rw [flowEndpoint_plugLeft,flowEndpoint_plugLeft,left.wiring]
    | inr x =>
      change flowEndpoint (Graph.plug c r) _ _ _ ((Graph.plug c r).wire (AG.plugRight c r x)) = _
      rw [plugRight_wire]
      simp only [AG.plugRight]
      rw [flowEndpoint_plugRight,flowEndpoint_plugRight,right.wiring]
end
end Lamping.AG
