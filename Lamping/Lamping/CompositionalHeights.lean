import Lamping.Lamping.InitialHeights
namespace Lamping.AG
open Graph Lambda
section
variable {N M B C W V : Type} [FiniteNames N] [FiniteNames M] [FiniteNames B]
  [FiniteNames C] [FiniteNames W] [FiniteNames V]
variable (g : Net signature N B W) (h : Net signature M C V)
variable (bp : B → Option Nat) (cp : C → Option Nat)
variable (gw : W → Option Nat) (hw : V → Option Nat)
theorem endpointHeight_unionL (e : Endpoint g) :
    endpointHeight (unionNet g h) (Sum.elim bp cp) (Sum.elim gw hw)
      ((unionEnd g.label h.label) (.inl e))=endpointHeight g bp gw e := by
  rcases e with ⟨n,p⟩ | (b | ⟨w,d⟩) <;> rfl

theorem endpointHeight_unionR (e : Endpoint h) :
    endpointHeight (unionNet g h) (Sum.elim bp cp) (Sum.elim gw hw)
      ((unionEnd g.label h.label) (.inr e))=endpointHeight h cp hw e := by
  rcases e with ⟨n,p⟩ | (b | ⟨w,d⟩) <;> rfl

def Heighting.union (left : Heighting g bp) (right : Heighting h cp) :
    Heighting (unionNet g h) (Sum.elim bp cp) where
  vertices := Sum.elim left.vertices right.vertices
  wiring e := by
    rw [←(unionEnd g.label h.label).right_inv e]
    generalize (unionEnd g.label h.label).invFun e = old
    cases old with
    | inl x => rw [union_left,endpointHeight_unionL,endpointHeight_unionL,left.wiring]
    | inr x => rw [union_right,endpointHeight_unionR,endpointHeight_unionR,right.wiring]
end
section
variable {K R B F W V : Type} [FiniteNames K] [FiniteNames R] [FiniteNames B]
  [FiniteNames F] [FiniteNames W] [FiniteNames V]
variable (c : Net signature K (B⊕F) W) (r : Net signature R F V)
variable (bp : B → Option Nat) (fp : F → Option Nat)
variable (cw : W → Option Nat) (rv : V → Option Nat)
def plugHeights : ((W⊕V)⊕F) → Option Nat := Sum.elim (Sum.elim cw rv) fp

theorem endpointHeight_plugLeft (e : Endpoint c) :
    endpointHeight (plug c r) bp (plugHeights fp cw rv) ((plugEnd c.label r.label) (.inl e))=
      endpointHeight c (Sum.elim bp fp) cw e := by
  rcases e with ⟨n,p⟩ | ((b|f) | ⟨w,d⟩) <;> rfl

theorem endpointHeight_plugRight (e : Endpoint r) :
    endpointHeight (plug c r) bp (plugHeights fp cw rv) ((plugEnd c.label r.label) (.inr e))=
      endpointHeight r fp rv e := by
  rcases e with ⟨n,p⟩ | (f | ⟨w,d⟩) <;> rfl

def Heighting.plug (left : Heighting c (Sum.elim bp fp)) (right : Heighting r fp) :
    Heighting (Graph.plug c r) bp where
  vertices := plugHeights fp left.vertices right.vertices
  wiring e := by
    rw [←(plugEnd c.label r.label).right_inv e]
    generalize (plugEnd c.label r.label).invFun e = old
    cases old with
    | inl x =>
      change endpointHeight (Graph.plug c r) _ _ ((Graph.plug c r).wire (AG.plugLeft c r x))=_
      rw [plugLeft_wire]
      simp only [AG.plugLeft]
      rw [endpointHeight_plugLeft,endpointHeight_plugLeft,left.wiring]
    | inr x =>
      change endpointHeight (Graph.plug c r) _ _ ((Graph.plug c r).wire (AG.plugRight c r x))=_
      rw [plugRight_wire]
      simp only [AG.plugRight]
      rw [endpointHeight_plugRight,endpointHeight_plugRight,right.wiring]
end
end Lamping.AG
