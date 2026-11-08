import Lamping.Lamping.LevelBalance
import Lamping.Lamping.InitialAccessWords
namespace Lamping.AG
open Graph
section
variable {N M B C W V : Type} [FiniteNames N] [FiniteNames M] [FiniteNames B]
  [FiniteNames C] [FiniteNames W] [FiniteNames V]
variable (g : Net signature N B W) (h : Net signature M C V)
variable (gn : N → Int) (hn : M → Int) (bp : B → Int) (cp : C → Int) (gw : W → Int) (hw : V → Int)

theorem endpointDepth_unionL (e : Endpoint g) :
    endpointDepth (unionNet g h) (Sum.elim gn hn) (Sum.elim bp cp) (Sum.elim gw hw)
      ((unionEnd g.label h.label) (.inl e))=endpointDepth g gn bp gw e := by
  rcases e with ⟨n,p⟩ | (b | ⟨w,d⟩) <;> rfl
theorem endpointDepth_unionR (e : Endpoint h) :
    endpointDepth (unionNet g h) (Sum.elim gn hn) (Sum.elim bp cp) (Sum.elim gw hw)
      ((unionEnd g.label h.label) (.inr e))=endpointDepth h hn cp hw e := by
  rcases e with ⟨n,p⟩ | (b | ⟨w,d⟩) <;> rfl

def LevelBalance.union (left : LevelBalance g bp) (right : LevelBalance h cp) :
    LevelBalance (unionNet g h) (Sum.elim bp cp) where
  nodes := Sum.elim left.nodes right.nodes
  vertices := Sum.elim left.vertices right.vertices
  wiring e := by
    rw [←(unionEnd g.label h.label).right_inv e]
    generalize (unionEnd g.label h.label).invFun e = old
    cases old with
    | inl x => rw [union_left,endpointDepth_unionL,endpointDepth_unionL,left.wiring]
    | inr x => rw [union_right,endpointDepth_unionR,endpointDepth_unionR,right.wiring]
end
section
variable {K R B F W V : Type} [FiniteNames K] [FiniteNames R] [FiniteNames B]
  [FiniteNames F] [FiniteNames W] [FiniteNames V]
variable (c : Net signature K (B⊕F) W) (r : Net signature R F V)
variable (cn : K → Int) (rn : R → Int) (bp : B → Int) (fp : F → Int) (cw : W → Int) (rv : V → Int)

theorem endpointDepth_plugLeft (e : Endpoint c) :
    endpointDepth (plug c r) (Sum.elim cn rn) bp (Sum.elim (Sum.elim cw rv) fp)
      ((plugEnd c.label r.label) (.inl e))=endpointDepth c cn (Sum.elim bp fp) cw e := by
  rcases e with ⟨n,p⟩ | ((b|f) | ⟨w,d⟩) <;> rfl
theorem endpointDepth_plugRight (e : Endpoint r) :
    endpointDepth (plug c r) (Sum.elim cn rn) bp (Sum.elim (Sum.elim cw rv) fp)
      ((plugEnd c.label r.label) (.inr e))=endpointDepth r rn fp rv e := by
  rcases e with ⟨n,p⟩ | (f | ⟨w,d⟩) <;> rfl

def LevelBalance.plug (left : LevelBalance c (Sum.elim bp fp)) (right : LevelBalance r fp) :
    LevelBalance (Graph.plug c r) bp where
  nodes := Sum.elim left.nodes right.nodes
  vertices := Sum.elim (Sum.elim left.vertices right.vertices) fp
  wiring e := by
    rw [←(plugEnd c.label r.label).right_inv e]
    generalize (plugEnd c.label r.label).invFun e = old
    cases old with
    | inl x =>
      change endpointDepth (Graph.plug c r) _ _ _ ((Graph.plug c r).wire (AG.plugLeft c r x))=_
      rw [plugLeft_wire]
      simp only [AG.plugLeft]
      rw [endpointDepth_plugLeft,endpointDepth_plugLeft,left.wiring]
    | inr x =>
      change endpointDepth (Graph.plug c r) _ _ _ ((Graph.plug c r).wire (AG.plugRight c r x))=_
      rw [plugRight_wire]
      simp only [AG.plugRight]
      rw [endpointDepth_plugRight,endpointDepth_plugRight,right.wiring]
end
end Lamping.AG
