import Lamping.Lamping.InitialAddresses
namespace Lamping.AG
open Graph Lambda
private theorem syntaxPortAddress_prefix (kind : Kind) (p : Port kind) (pre address : Path) :
    syntaxPortAddress kind p (pre++address)=
      (syntaxPortAddress kind p address).map (fun word => pre++word) := by
  cases kind with
  | garbage => rfl
  | op op =>
    cases op <;> cases p <;> rename_i p <;> cases p
    all_goals first | rfl | exact congrArg some (List.append_assoc _ _ _)

section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable (g : Net signature N B W) (boundary : B → Option Path)
private theorem endpointAddress_prefix (nodes : N → Path) (vertices : W → Option Path) (pre : Path) (e : Endpoint g) :
    endpointAddress g (fun n => pre++nodes n) (fun b => (boundary b).map (pre++·))
      (fun w => (vertices w).map (pre++·)) e=(endpointAddress g nodes boundary vertices e).map (pre++·) := by
  rcases e with ⟨n,p⟩ | (b | ⟨w,d⟩)
  · exact syntaxPortAddress_prefix _ _ _ _
  · rfl
  · rfl

def Addressing.prefix (addr : Addressing g boundary) (pre : Path) :
    Addressing g (fun b => (boundary b).map (pre++·)) where
  nodes n := pre++addr.nodes n
  vertices w := (addr.vertices w).map (pre++·)
  wiring e := by rw [endpointAddress_prefix,endpointAddress_prefix,addr.wiring]
end
section
variable {N M B C W V : Type} [FiniteNames N] [FiniteNames M] [FiniteNames B]
  [FiniteNames C] [FiniteNames W] [FiniteNames V]
variable (g : Net signature N B W) (h : Net signature M C V)
variable (bp : B → Option Path) (cp : C → Option Path)
variable (ga : N → Path) (ha : M → Path) (gw : W → Option Path) (hw : V → Option Path)

theorem endpointAddress_unionL (e : Endpoint g) :
    endpointAddress (unionNet g h) (Sum.elim ga ha) (Sum.elim bp cp) (Sum.elim gw hw)
      ((unionEnd g.label h.label) (.inl e))=endpointAddress g ga bp gw e := by
  rcases e with ⟨n,p⟩ | (b | ⟨w,d⟩) <;> rfl

theorem endpointAddress_unionR (e : Endpoint h) :
    endpointAddress (unionNet g h) (Sum.elim ga ha) (Sum.elim bp cp) (Sum.elim gw hw)
      ((unionEnd g.label h.label) (.inr e))=endpointAddress h ha cp hw e := by
  rcases e with ⟨n,p⟩ | (b | ⟨w,d⟩) <;> rfl

def Addressing.union (left : Addressing g bp) (right : Addressing h cp) :
    Addressing (unionNet g h) (Sum.elim bp cp) where
  nodes := Sum.elim left.nodes right.nodes
  vertices := Sum.elim left.vertices right.vertices
  wiring e := by
    rw [←(unionEnd g.label h.label).right_inv e]
    generalize (unionEnd g.label h.label).invFun e = old
    cases old with
    | inl x =>
      rw [union_left,endpointAddress_unionL,endpointAddress_unionL,left.wiring]
    | inr x =>
      rw [union_right,endpointAddress_unionR,endpointAddress_unionR,right.wiring]
end
section
variable {K R B F W V : Type} [FiniteNames K] [FiniteNames R] [FiniteNames B]
  [FiniteNames F] [FiniteNames W] [FiniteNames V]
variable (c : Net signature K (B⊕F) W) (r : Net signature R F V)
variable (bp : B → Option Path) (fp : F → Option Path)
variable (cn : K → Path) (rn : R → Path) (cw : W → Option Path) (rw' : V → Option Path)
def plugAddresses : ((W⊕V)⊕F) → Option Path := Sum.elim (Sum.elim cw rw') fp

theorem endpointAddress_plugLeft (e : Endpoint c) :
    endpointAddress (plug c r) (Sum.elim cn rn) bp (plugAddresses fp cw rw') ((plugEnd c.label r.label) (.inl e))=
      endpointAddress c cn (Sum.elim bp fp) cw e := by
  rcases e with ⟨n,p⟩ | ((b|f) | ⟨w,d⟩) <;> rfl

theorem endpointAddress_plugRight (e : Endpoint r) :
    endpointAddress (plug c r) (Sum.elim cn rn) bp (plugAddresses fp cw rw') ((plugEnd c.label r.label) (.inr e))=
      endpointAddress r rn fp rw' e := by
  rcases e with ⟨n,p⟩ | (f | ⟨w,d⟩) <;> rfl

def Addressing.plug (left : Addressing c (Sum.elim bp fp)) (right : Addressing r fp) :
    Addressing (Graph.plug c r) bp where
  nodes := Sum.elim left.nodes right.nodes
  vertices := plugAddresses fp left.vertices right.vertices
  wiring e := by
    rw [←(plugEnd c.label r.label).right_inv e]
    generalize (plugEnd c.label r.label).invFun e = old
    cases old with
    | inl x =>
      change endpointAddress (Graph.plug c r) _ _ _ ((Graph.plug c r).wire (AG.plugLeft c r x))=_
      rw [plugLeft_wire]
      simp only [AG.plugLeft]
      rw [endpointAddress_plugLeft,endpointAddress_plugLeft,left.wiring]
    | inr x =>
      change endpointAddress (Graph.plug c r) _ _ _ ((Graph.plug c r).wire (AG.plugRight c r x))=_
      rw [plugRight_wire]
      simp only [AG.plugRight]
      rw [endpointAddress_plugRight,endpointAddress_plugRight,right.wiring]
end
end Lamping.AG
