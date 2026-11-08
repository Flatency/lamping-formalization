import Lamping.Lamping.InitialPathControls
namespace Lamping.AG
open Graph Lambda
/-- Initial incidence orientation. Binding ports are sinks; the inert Garbage cap has complementary polarity and no traversal rule. -/
def initialPortPolarity : (k : Kind) → Port k → Bool
  | .op .app,.inl _ => true
  | .op .app,.inr b => b
  | .op .lam,.inl _ => false
  | .op .lam,.inr b => b
  | .op .fan,.inl _ | .op .cro,.inl _ | .op .bra,.inl _ => true
  | .op .fan,.inr _ | .op .cro,.inr _ | .op .bra,.inr _ => false
  | .garbage,_ => true
def endPolarity {N B W : Type} {l : N → Label signature}
    (bp : B → Bool) (vp : W → Bool) : End signature N B W l → Bool
  | .inl ⟨n,p⟩ => initialPortPolarity (l n).sort p
  | .inr (.inl b) => bp b
  | .inr (.inr (w,d)) => if d then !(vp w) else vp w
def FlowOn {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
    (g : Net signature N B W) (bp : B → Bool) (vp : W → Bool) : Prop :=
  ∀ e, endPolarity bp vp (g.wire e) = !(endPolarity bp vp e)
def initialBoundaryPolarity {t : Term} : Boundary t → Bool
  | .inl _ => true
  | .inr _ => false
section Plug
variable {K R B F W V : Type} [FiniteNames K] [FiniteNames R] [FiniteNames B]
  [FiniteNames F] [FiniteNames W] [FiniteNames V]
variable (c : Net signature K (B⊕F) W) (r : Net signature R F V)
variable (bp : B→Bool) (fp : F→Bool) (wp : W→Bool) (vp : V→Bool)
def plugPolarity : ((W⊕V)⊕F) → Bool
  | .inl (.inl w) => wp w
  | .inl (.inr v) => vp v
  | .inr f => !(fp f)
theorem plugPolarity_left (e : Endpoint c) :
    endPolarity bp (plugPolarity fp wp vp) (plugLeft c r e) =
    endPolarity (Sum.elim bp (fun f => !(fp f))) wp e := by
  rcases e with ⟨k,p⟩ | ((b | f) | ⟨w,d⟩) <;> rfl
theorem plugPolarity_right (e : Endpoint r) :
    endPolarity bp (plugPolarity fp wp vp) (plugRight c r e) = endPolarity fp vp e := by
  rcases e with ⟨n,p⟩ | (f | ⟨v,d⟩)
  · rfl
  · simp [plugRight,plugEnd,endPolarity,plugPolarity]
  · rfl
theorem FlowOn.plug
    (hc : FlowOn c (Sum.elim bp (fun f => !(fp f))) wp) (hr : FlowOn r fp vp) :
    FlowOn (Graph.plug c r) bp (plugPolarity fp wp vp) := by
  intro e
  have he : (plugEnd c.label r.label) ((plugEnd c.label r.label).invFun e)=e := Bij.right_inv _ e
  rw [←he]
  generalize (plugEnd c.label r.label).invFun e = old
  cases old with
  | inl x =>
    change endPolarity bp (plugPolarity fp wp vp) ((Graph.plug c r).wire (plugLeft c r x)) = !(endPolarity bp (plugPolarity fp wp vp) (plugLeft c r x))
    rw [plugLeft_wire,plugPolarity_left,plugPolarity_left]
    exact hc x
  | inr x =>
    change endPolarity bp (plugPolarity fp wp vp) ((Graph.plug c r).wire (plugRight c r x)) = !(endPolarity bp (plugPolarity fp wp vp) (plugRight c r x))
    rw [plugRight_wire,plugPolarity_right,plugPolarity_right]
    exact hr x
end Plug
end Lamping.AG



namespace Lamping.AG
open Graph Lambda
section Union
variable {N M B C W V : Type} [FiniteNames N] [FiniteNames M] [FiniteNames B]
  [FiniteNames C] [FiniteNames W] [FiniteNames V]
variable (g : Net signature N B W) (h : Net signature M C V)
variable (bp : B→Bool) (cp : C→Bool) (wp : W→Bool) (vp : V→Bool)
theorem unionPolarity_left (e : Endpoint g) :
    endPolarity (Sum.elim bp cp) (Sum.elim wp vp) (unionEnd g.label h.label (.inl e)) = endPolarity bp wp e := by
  rcases e with ⟨n,p⟩ | (b | ⟨w,d⟩) <;> rfl
theorem unionPolarity_right (e : Endpoint h) :
    endPolarity (Sum.elim bp cp) (Sum.elim wp vp) (unionEnd g.label h.label (.inr e)) = endPolarity cp vp e := by
  rcases e with ⟨n,p⟩ | (b | ⟨w,d⟩) <;> rfl
theorem FlowOn.union (hg : FlowOn g bp wp) (hh : FlowOn h cp vp) :
    FlowOn (unionNet g h) (Sum.elim bp cp) (Sum.elim wp vp) := by
  intro e
  rw [← (unionEnd g.label h.label).right_inv e]
  generalize (unionEnd g.label h.label).invFun e = old
  cases old with
  | inl x => rw [union_left,unionPolarity_left,unionPolarity_left]; exact hg x
  | inr x => rw [union_right,unionPolarity_right,unionPolarity_right]; exact hh x
end Union

theorem varNet_flow (n k : Nat) : FlowOn (varNet n k) initialBoundaryPolarity Empty.elim := by
  rintro (⟨u,p⟩ | ((u | x) | ⟨w,d⟩))
  · cases p <;> rfl
  · rfl
  · rfl
  · exact nomatch w

theorem lambdaUsed_flow (n : Nat) (b : Term) (used : free b 0) :
    FlowOn (lambdaUsed n b used)
      (Sum.elim initialBoundaryPolarity (fun x => !initialBoundaryPolarity x)) Empty.elim := by
  rintro (⟨u,p⟩ | (((u | x) | (v | ⟨k,h⟩)) | ⟨w,d⟩))
  · cases p with | inl u => rfl | inr p => cases p <;> rfl
  · rfl
  · rfl
  · rfl
  · cases k <;> rfl
  · exact nomatch w

theorem lambdaUnused_flow (n : Nat) (b : Term) (unused : ¬free b 0) :
    FlowOn (lambdaUnused n b unused)
      (Sum.elim initialBoundaryPolarity (fun x => !initialBoundaryPolarity x)) Empty.elim := by
  rintro (⟨u | v,p⟩ | (((u | x) | (v | ⟨k,h⟩)) | ⟨w,d⟩))
  · cases p with | inl u => rfl | inr p => cases p <;> rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · cases k with | zero => exact False.elim (unused h) | succ k => rfl
  · exact nomatch w

theorem appPatch_flow (n : Nat) (f a : Term) :
    FlowOn (appPatch n f a)
      (Sum.elim initialBoundaryPolarity (fun x => !(Sum.elim initialBoundaryPolarity initialBoundaryPolarity x))) Empty.elim := by
  rintro (⟨u | (x | x),p⟩ | (((u | x) | ((v | x) | (z | x))) | ⟨w,d⟩))
  · cases p with | inl u => rfl | inr p => cases p <;> rfl
  · cases p with
    | inl u => dsimp only [appPatch,appMate]; split <;> rfl
    | inr u => rfl
  · cases p with | inl u => rfl | inr p => cases p <;> rfl
  · rfl
  · dsimp only [appPatch,appMate]; split <;> (try split) <;> rfl
  · rfl
  · dsimp only [appPatch,appMate]; split <;> rfl
  · rfl
  · rfl
  · exact nomatch w
end Lamping.AG

namespace Lamping.AG
open Graph Lambda
/-- A genuine structural invariant of every recursively encoded graph, including
all actual gluing vertices. The vertex polarity is constructed in the induction. -/
theorem encode_flow (t : Term) (n : Nat) :
    ∃ vp : (encode n t).W → Bool, FlowOn (encode n t).net initialBoundaryPolarity vp := by
  induction t generalizing n with
  | var k => exact ⟨Empty.elim,varNet_flow n k⟩
  | lam b ih =>
    obtain ⟨vp,body⟩ := ih n
    dsimp only [encode]
    by_cases used : free b 0
    · rw [dif_pos used]
      exact ⟨plugPolarity initialBoundaryPolarity Empty.elim vp,
        FlowOn.plug (c:=lambdaUsed n b used) (r:=(encode n b).net)
          (bp:=initialBoundaryPolarity) (fp:=initialBoundaryPolarity)
          (wp:=Empty.elim) (vp:=vp) (lambdaUsed_flow n b used) body⟩
    · rw [dif_neg used]
      exact ⟨plugPolarity initialBoundaryPolarity Empty.elim vp,
        FlowOn.plug (c:=lambdaUnused n b used) (r:=(encode n b).net)
          (bp:=initialBoundaryPolarity) (fp:=initialBoundaryPolarity)
          (wp:=Empty.elim) (vp:=vp) (lambdaUnused_flow n b used) body⟩
  | app f a hf ha =>
    obtain ⟨wp,fn⟩ := hf n
    obtain ⟨vp,arg⟩ := ha (n+1)
    exact ⟨plugPolarity (Sum.elim initialBoundaryPolarity initialBoundaryPolarity) Empty.elim (Sum.elim wp vp),
      FlowOn.plug (c:=appPatch n f a) (r:=unionNet (encode n f).net (encode (n+1) a).net)
        (bp:=initialBoundaryPolarity) (fp:=Sum.elim initialBoundaryPolarity initialBoundaryPolarity)
        (wp:=Empty.elim) (vp:=Sum.elim wp vp) (appPatch_flow n f a)
        (FlowOn.union (g:=(encode n f).net) (h:=(encode (n+1) a).net)
          (bp:=initialBoundaryPolarity) (cp:=initialBoundaryPolarity) (wp:=wp) (vp:=vp) fn arg)⟩
end Lamping.AG
namespace Lamping.AG
open Graph Lambda
theorem Passage.polarities {i k p q a b} (h : Passage i k p q a b) :
    initialPortPolarity k p=false ∧ initialPortPolarity k q=true := by
  cases h <;> exact ⟨rfl,rfl⟩
theorem Passage.forward_ports {i k p q a b} (h : Passage i k p q a b) : ForwardPorts k p q := by
  cases h <;> simp [ForwardPorts,AG.appCtx,AG.appArg,AG.lamBody]
theorem Traversal.direct_of_polarity {i k p q a b} (h : Traversal i k p q a b)
    (incoming : initialPortPolarity k p=false) : Passage i k p q a b := by
  cases h with
  | direct h => exact h
  | inverse h => have impossible := h.polarities.2.symm.trans incoming; cases impossible
section Paths
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable {g : Net signature N B W} {bp : B→Bool} {vp : W→Bool}
/-- Initial turns retain only printed top-down passages at controls. -/
inductive InitialTurn : Endpoint g → Endpoint g → Context → Context → Prop
  | node (n : N) (p q : Port (g.label n).sort) {a b}
      (rule : Passage (g.label n).index (g.label n).sort p q a b) :
      InitialTurn (.inl ⟨n,p⟩) (.inl ⟨n,q⟩) a b
  | transparent (w : W) (d : Bool) (a) :
      InitialTurn (.inr (.inr (w,d))) (.inr (.inr (w,!d))) a a

theorem LabelledTurn.initial_of_polarity {e f : Endpoint g} {a b : Context}
    (h : LabelledTurn g e f a b) (incoming : endPolarity bp vp e=false) :
    InitialTurn (g:=g) e f a b ∧ endPolarity bp vp f=true := by
  cases h with
  | node n p q rule =>
    have passage := rule.direct_of_polarity incoming
    exact ⟨.node n p q passage,passage.polarities.2⟩
  | transparent w d a =>
    refine ⟨.transparent w d a,?_⟩
    cases d <;> cases h : vp w <;> simp_all [endPolarity]

inductive InitialLabelling : List (Endpoint g) → Context → Context → Prop
  | single (e a) : InitialLabelling [e] a a
  | cons {e f es a b c} : InitialTurn (g:=g) (g.wire e) f a b →
      InitialLabelling (f::es) b c → InitialLabelling (e::f::es) a c

theorem Labelling.initial_of_flow {es : List (Endpoint g)} {a b : Context}
    (h : Labelling g es a b) (flow : FlowOn g bp vp)
    (first : ∀ e, es.head?=some e → endPolarity bp vp e=true) :
    InitialLabelling (g:=g) es a b := by
  induction h with
  | single e a => exact .single e a
  | @cons e f es a b c ht hs ih =>
    have pe := first e rfl
    have arrival : endPolarity bp vp (g.wire e)=false := by rw [flow e,pe]; rfl
    obtain ⟨turn,pf⟩ := ht.initial_of_polarity arrival
    refine .cons turn (ih ?_)
    intro x hx
    simp only [List.head?_cons,Option.some.injEq] at hx
    subst x; exact pf

theorem InitialTurn.prepend_forward {e f : Endpoint g} {es : List (Endpoint g)} {a b : Context}
    (h : InitialTurn (g:=g) e f a b) (x : Endpoint g) (wire : g.wire x=e)
    (tail : Forward g (f::es)) : Forward g (x::f::es) := by
  cases h with
  | node n p q rule => exact .node n p q wire rfl rule.forward_ports tail
  | transparent w d a => exact .transparent w d wire rfl tail
theorem InitialLabelling.forward {es : List (Endpoint g)} {a b : Context}
    (h : InitialLabelling (g:=g) es a b) : Forward g es := by
  induction h with
  | single e a => exact .single e
  | cons turn tail ih => exact turn.prepend_forward _ rfl ih
end Paths
/-- General initial-path foundation. Every properly labelled root path of an
actual encode has only direct control passages, and is forward. No SND, Matches,
reachability invariant or path transport certificate is an input. -/
theorem encode_root_initial (t : Term) (n : Nat) (es : List (Endpoint (encode n t).net))
    (rooted : es.head?=some (.inr (.inl (.inl ())))) (h : Labelling (encode n t).net es a b) :
    InitialLabelling (g:=(encode n t).net) es a b := by
  obtain ⟨vp,flow⟩ := encode_flow t n
  apply h.initial_of_flow flow
  intro e he
  rw [rooted] at he
  simp only [Option.some.injEq] at he
  subst e; rfl

theorem encode_root_forward (t : Term) (n : Nat) (es : List (Endpoint (encode n t).net))
    (rooted : es.head?=some (.inr (.inl (.inl ())))) (h : ProperPath (encode n t).net es) :
    Forward (encode n t).net es := by
  obtain ⟨a,b,labels⟩ := h
  exact (encode_root_initial t n es rooted labels).forward
end Lamping.AG

