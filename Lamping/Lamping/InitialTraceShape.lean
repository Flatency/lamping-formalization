import Lamping.Lamping.InitialOffsets
import Lamping.Lamping.InitialPatchRoutes
namespace Lamping.AG.InitialOffsets
open Graph Lambda
private theorem last_of_append_nonempty {T : Type} (xs ys : List T) (nonempty : ys≠[]) :
    (xs++ys).getLast?=ys.getLast? := by
  rw [List.getLast?_append]
  cases h : ys.getLast? with
  | none => exact False.elim (nonempty (List.getLast?_eq_none_iff.mp h))
  | some v => rfl
/-- A root used-lambda loop is exactly one child root-to-FV0 path, with the
actual two fresh frontier segments retained. No trace shape is supplied. -/
theorem lambdaUsed_rawLoop_child (n : Nat) (body : Term) (used : free body 0)
    {R V : Type} [FiniteNames R] [FiniteNames V]
    (r : Net signature R (Boundary body) V) (vp : V → Bool)
    (flow : FlowOn r initialBoundaryPolarity vp)
    {es : List (Endpoint (plug (lambdaUsed n body used) r))} {a b : Context}
    (loop : RawLoop (plug (lambdaUsed n body used) r) es a b)
    (binder : loop.binder=.inl ()) :
    ∃ p : LocalPath r (.inl ()) (.inr ⟨0,used⟩) a b,
      es=[plugLeft (lambdaUsed n body used) r (.inl ⟨(),lamBody⟩)] ++
        p.edges.map (plugRight (lambdaUsed n body used) r) ++
        [plugLeft (lambdaUsed n body used) r (.inr (.inl (.inr (.inr ⟨0,used⟩))))] := by
  rcases loop with ⟨node,isLam,bodyPort,bind,bodyRole,bindRole,start,finish,labels⟩
  dsimp only at binder; subst node
  have bodyEq : bodyPort=lamBody := eq_of_heq bodyRole
  have bindEq : bind=lamBind := eq_of_heq bindRole
  subst bodyPort; subst bind
  cases es with
  | nil => simp at start
  | cons e tail =>
    simp only [List.head?_cons,Option.some.injEq] at start; subst e
    have localFinish :
        (plugLeft (lambdaUsed n body used) r (.inl ⟨(),lamBody⟩)::tail).getLast?=
        some (plugLeft (lambdaUsed n body used) r ((lambdaUsed n body used).wire (.inl ⟨(),lamBind⟩))) := by
      rw [←plugLeft_wire]; exact finish
    change Labelling (plug (lambdaUsed n body used) r) (plugLeft (lambdaUsed n body used) r (.inl ⟨(),lamBody⟩)::tail) a b at labels
    rcases labels.outer_child_decompose (lambdaUsed n body used) r
        (lambdaUsed_flow n body used) flow (lambdaUsed_noReturn n body used) rfl localFinish with
      ⟨xs,eq,stay⟩ | ⟨xs,z,z',mid,last,p,ys,entry,exit,eq,first,firstFinish,lastLabels⟩
    · obtain ⟨one,_⟩ := stay.boundary_terminal rfl (.inr (.inl ())) rfl
      rw [eq] at localFinish
      have sourceEq : plugLeft (lambdaUsed n body used) r (.inl ⟨(),lamBody⟩)::xs.map (plugLeft (lambdaUsed n body used) r)=
          ([.inl ⟨(),lamBody⟩] : List (Endpoint (lambdaUsed n body used))).map (plugLeft (lambdaUsed n body used) r) := by
        change ((.inl ⟨(),lamBody⟩::xs).map _)=_; rw [one]
      rw [sourceEq] at localFinish
      cases localFinish
    · have leadingShape : ( .inl ⟨(),lamBody⟩::xs)=[.inl ⟨(),lamBody⟩] ∧ z=.inl () ∧ a=mid :=
        lambdaUsed_body_to_child n body used first rfl z firstFinish
      obtain ⟨one,rfl,rfl⟩ := leadingShape
      have xsNil : xs=[] := by cases one; rfl
      subst xs
      cases z' with
      | inl u => cases exit
      | inr x =>
        have suffixFinish : (.inr (.inl (.inr (.inr x)))::ys).getLast?=
            some ((lambdaUsed n body used).wire (.inl ⟨(),lamBind⟩)) := by
          rw [eq] at localFinish
          change (([plugLeft (lambdaUsed n body used) r (.inl ⟨(),lamBody⟩)] ++ p.edges.map (plugRight (lambdaUsed n body used) r)) ++
            (.inr (.inl (.inr (.inr x)))::ys).map (plugLeft (lambdaUsed n body used) r)).getLast?=_ at localFinish
          rw [last_of_append_nonempty _ _ (by simp),List.getLast?_map] at localFinish
          cases hlast : (.inr (.inl (.inr (.inr x)))::ys).getLast? with
          | none => have impossible := List.getLast?_eq_none_iff.mp hlast; cases impossible
          | some v =>
            simp only [hlast,Option.map_some,Option.some.injEq] at localFinish
            have inject := (plugEnd (lambdaUsed n body used).label r.label).injective localFinish
            cases inject
            rfl
        obtain ⟨suffix,xZero,rfl⟩ := lambdaUsed_child_to_binding n body used x lastLabels rfl suffixFinish
        have ysNil : ys=[] := by cases suffix; rfl
        subst ys
        have xEq : x=(⟨0,used⟩ : FV body) := Subtype.ext xZero
        subst x
        exact ⟨p,by rw [eq]; rfl⟩
end Lamping.AG.InitialOffsets
namespace Lamping.AG.InitialOffsets
open Graph Lambda
/-- A lambda whose variable 0 is absent has no raw actual binding loop. -/
theorem lambdaUnused_no_rawLoop (n : Nat) (body : Term) (unused : ¬free body 0)
    {R V : Type} [FiniteNames R] [FiniteNames V]
    (r : Net signature R (Boundary body) V) (vp : V → Bool)
    (flow : FlowOn r initialBoundaryPolarity vp)
    {es : List (Endpoint (plug (lambdaUnused n body unused) r))} {a b : Context}
    (loop : RawLoop (plug (lambdaUnused n body unused) r) es a b)
    (binder : loop.binder=.inl (.inl ())) : False := by
  rcases loop with ⟨node,isLam,bodyPort,bind,bodyRole,bindRole,start,finish,labels⟩
  dsimp only at binder; subst node
  have bodyEq : bodyPort=lamBody := eq_of_heq bodyRole
  have bindEq : bind=lamBind := eq_of_heq bindRole
  subst bodyPort; subst bind
  cases es with
  | nil => simp at start
  | cons e tail =>
    simp only [List.head?_cons,Option.some.injEq] at start; subst e
    have localFinish :
        (plugLeft (lambdaUnused n body unused) r (.inl ⟨.inl (),lamBody⟩)::tail).getLast?=
        some (plugLeft (lambdaUnused n body unused) r ((lambdaUnused n body unused).wire (.inl ⟨.inl (),lamBind⟩))) := by
      rw [←plugLeft_wire]; exact finish
    change Labelling (plug (lambdaUnused n body unused) r)
      (plugLeft (lambdaUnused n body unused) r (.inl ⟨.inl (),lamBody⟩)::tail) a b at labels
    rcases labels.outer_child_decompose (lambdaUnused n body unused) r
        (lambdaUnused_flow n body unused) flow (lambdaUnused_noReturn n body unused) rfl localFinish with
      ⟨xs,eq,stay⟩ | ⟨xs,z,z',mid,last,p,ys,entry,exit,eq,first,firstFinish,lastLabels⟩
    · obtain ⟨one,_⟩ := stay.boundary_terminal rfl (.inr (.inl ())) rfl
      rw [eq] at localFinish
      have sourceEq : plugLeft (lambdaUnused n body unused) r (.inl ⟨.inl (),lamBody⟩)::xs.map (plugLeft (lambdaUnused n body unused) r)=
          ([.inl ⟨.inl (),lamBody⟩] : List (Endpoint (lambdaUnused n body unused))).map (plugLeft (lambdaUnused n body unused) r) := by
        change ((.inl ⟨.inl (),lamBody⟩::xs).map _)=_; rw [one]
      rw [sourceEq] at localFinish
      cases localFinish
    · cases z' with
      | inl u => cases exit
      | inr x =>
        have suffixFinish : (.inr (.inl (.inr (.inr x)))::ys).getLast?=
            some ((lambdaUnused n body unused).wire (.inl ⟨.inl (),lamBind⟩)) := by
          rw [eq] at localFinish
          change (((.inl ⟨.inl (),lamBody⟩::xs).map (plugLeft (lambdaUnused n body unused) r) ++ p.edges.map (plugRight (lambdaUnused n body unused) r)) ++
            (.inr (.inl (.inr (.inr x)))::ys).map (plugLeft (lambdaUnused n body unused) r)).getLast?=_ at localFinish
          rw [last_of_append_nonempty _ _ (by simp),List.getLast?_map] at localFinish
          cases hlast : (.inr (.inl (.inr (.inr x)))::ys).getLast? with
          | none => have impossible := List.getLast?_eq_none_iff.mp hlast; cases impossible
          | some v =>
            simp only [hlast,Option.map_some,Option.some.injEq] at localFinish
            have inject := (plugEnd (lambdaUnused n body unused).label r.label).injective localFinish
            cases inject
            rfl
        exact lambdaUnused_child_not_binding n body unused x lastLabels rfl suffixFinish
end Lamping.AG.InitialOffsets
namespace Lamping.AG.InitialOffsets
open Graph Lambda
section EventsMap
variable {K R B F W V : Type} [FiniteNames K] [FiniteNames R] [FiniteNames B]
  [FiniteNames F] [FiniteNames W] [FiniteNames V]
variable (c : Net signature K (B⊕F) W) (r : Net signature R F V)
theorem allEvents_plugRight (es : List (Endpoint r)) :
    allEvents (plug c r) (es.map (AG.plugRight c r))=allEvents r es := by
  induction es with
  | nil => rfl
  | cons e es ih =>
    change arrivalEvents (plug c r) (plugRight c r e) ++ allEvents (plug c r) (es.map (AG.plugRight c r))=
      arrivalEvents r e ++ allEvents r es
    rw [arrivalEvents_plugRight,ih]
end EventsMap
/-- The control word of an actual root lambda loop is precisely the actual
child root-to-FV0 word. Transparent gluing contributes no control event. -/
theorem lambdaUsed_rawLoop_events (n : Nat) (body : Term) (used : free body 0)
    {R V : Type} [FiniteNames R] [FiniteNames V]
    (r : Net signature R (Boundary body) V) (vp : V → Bool)
    (flow : FlowOn r initialBoundaryPolarity vp)
    {es : List (Endpoint (plug (lambdaUsed n body used) r))} {a b : Context}
    (loop : RawLoop (plug (lambdaUsed n body used) r) es a b)
    (binder : loop.binder=.inl ()) :
    ∃ p : LocalPath r (.inl ()) (.inr ⟨0,used⟩) a b,
      eventsOfEdges (plug (lambdaUsed n body used) r) es=eventsOfEdges r p.edges := by
  obtain ⟨p,eq⟩ := lambdaUsed_rawLoop_child n body used r vp flow loop binder
  refine ⟨p,?_⟩
  rw [eq,events_eq_allEvents]
  · simp only [allEvents,List.flatMap_append,List.flatMap_cons,List.flatMap_nil,List.append_nil]
    change [] ++ (allEvents (plug (lambdaUsed n body used) r) (p.edges.map (plugRight (lambdaUsed n body used) r)) ++ [])=_
    rw [List.nil_append,List.append_nil,allEvents_plugRight,←LocalPath.events_all r p]
  · intro e he
    rw [last_of_append_nonempty _ _ (by simp)] at he
    simp only [List.getLast?_cons,List.getLast?_nil,Option.some.injEq] at he
    subst e
    rfl
end Lamping.AG.InitialOffsets
namespace Lamping.AG.InitialOffsets
open Graph Lambda
section Visits
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable (g : Net signature N B W)
def Visits (v : N) (e : Endpoint g) : Prop := ∃ p, e=.inl ⟨v,p⟩
def NoBinderRevisit (v : N) (es : List (Endpoint g)) : Prop :=
  ∀ e, e∈es.drop 1 → ¬Visits g v e
end Visits
/-- The root lambda occurs only as the first outgoing segment of its loop. -/
theorem lambdaUsed_rawLoop_no_revisit (n : Nat) (body : Term) (used : free body 0)
    {R V : Type} [FiniteNames R] [FiniteNames V]
    (r : Net signature R (Boundary body) V) (vp : V → Bool)
    (flow : FlowOn r initialBoundaryPolarity vp)
    {es : List (Endpoint (plug (lambdaUsed n body used) r))} {a b : Context}
    (loop : RawLoop (plug (lambdaUsed n body used) r) es a b)
    (binder : loop.binder=.inl ()) :
    NoBinderRevisit (plug (lambdaUsed n body used) r) (.inl ()) es := by
  obtain ⟨p,eq⟩ := lambdaUsed_rawLoop_child n body used r vp flow loop binder
  intro e mem ⟨q,atNode⟩
  rw [eq] at mem
  simp only [List.cons_append,List.nil_append,List.drop_succ_cons,List.drop_zero,List.mem_append,
    List.mem_map,List.mem_singleton] at mem
  rcases mem with ⟨x,_,image⟩ | atSuffix
  · rcases x with ⟨v,port⟩ | (boundary | ⟨w,d⟩)
    all_goals cases image.trans atNode
  · cases atSuffix.symm.trans atNode
section RevisitMaps
variable {K R B F W V : Type} [FiniteNames K] [FiniteNames R] [FiniteNames B]
  [FiniteNames F] [FiniteNames W] [FiniteNames V]
variable (c : Net signature K (B⊕F) W) (r : Net signature R F V)
theorem NoBinderRevisit.plugRight {v : R} {es : List (Endpoint r)}
    (h : NoBinderRevisit r v es) :
    NoBinderRevisit (plug c r) (.inr v) (es.map (AG.plugRight c r)) := by
  intro e mem ⟨q,atNode⟩
  have mappedDrop : (es.map (AG.plugRight c r)).drop 1=(es.drop 1).map (AG.plugRight c r) := by cases es <;> rfl
  rw [mappedDrop] at mem
  obtain ⟨x,hx,image⟩ := List.mem_map.mp mem
  rcases x with ⟨w,port⟩ | (boundary | ⟨w,d⟩)
  · have eq : (.inr w : K⊕R)=.inr v := congrArg Sigma.fst (Sum.inl.inj (image.trans atNode))
    have same := Sum.inr.inj eq
    subst w
    exact h _ hx ⟨port,rfl⟩
  · cases image.trans atNode
  · cases image.trans atNode
end RevisitMaps
end Lamping.AG.InitialOffsets
namespace Lamping.AG.InitialOffsets
open Graph Lambda
section UnionRevisit
variable {N M B C W V : Type} [FiniteNames N] [FiniteNames M] [FiniteNames B]
  [FiniteNames C] [FiniteNames W] [FiniteNames V]
variable (g : Net signature N B W) (h : Net signature M C V)
theorem NoBinderRevisit.unionL {v : N} {es : List (Endpoint g)}
    (avoids : NoBinderRevisit g v es) :
    NoBinderRevisit (unionNet g h) (.inl v) (es.map (AG.InitialOffsets.unionL g h)) := by
  intro e mem ⟨q,atNode⟩
  have mappedDrop : (es.map (AG.InitialOffsets.unionL g h)).drop 1=(es.drop 1).map (AG.InitialOffsets.unionL g h) := by cases es <;> rfl
  rw [mappedDrop] at mem
  obtain ⟨x,hx,image⟩ := List.mem_map.mp mem
  rcases x with ⟨w,port⟩ | (boundary | ⟨w,d⟩)
  · have eq : (.inl w : N⊕M)=.inl v := congrArg Sigma.fst (Sum.inl.inj (image.trans atNode))
    have same := Sum.inl.inj eq
    subst w
    exact avoids _ hx ⟨port,rfl⟩
  · cases image.trans atNode
  · cases image.trans atNode
theorem NoBinderRevisit.unionR {v : M} {es : List (Endpoint h)}
    (avoids : NoBinderRevisit h v es) :
    NoBinderRevisit (unionNet g h) (.inr v) (es.map (AG.InitialOffsets.unionR g h)) := by
  intro e mem ⟨q,atNode⟩
  have mappedDrop : (es.map (AG.InitialOffsets.unionR g h)).drop 1=(es.drop 1).map (AG.InitialOffsets.unionR g h) := by cases es <;> rfl
  rw [mappedDrop] at mem
  obtain ⟨x,hx,image⟩ := List.mem_map.mp mem
  rcases x with ⟨w,port⟩ | (boundary | ⟨w,d⟩)
  · have eq : (.inr w : N⊕M)=.inr v := congrArg Sigma.fst (Sum.inl.inj (image.trans atNode))
    have same := Sum.inr.inj eq
    subst w
    exact avoids _ hx ⟨port,rfl⟩
  · cases image.trans atNode
  · cases image.trans atNode
end UnionRevisit
/-- No initial raw binding loop revisits its own binder after leaving its body.
This quantifies over arbitrary labelled edge lists, with no length/simple-path input. -/
theorem encode_rawLoop_no_revisit (t : Term) (n : Nat)
    (es : List (Endpoint (encode n t).net)) (a b : Context)
    (loop : RawLoop (encode n t).net es a b) :
    NoBinderRevisit (encode n t).net loop.binder es := by
  induction t generalizing n a b with
  | var k => have impossible:=loop.isLam; change Kind.op .cro=Kind.op .lam at impossible; cases impossible
  | lam body ih =>
    revert es
    dsimp only [encode]
    obtain ⟨vp,rflow⟩ := encode_flow body n
    by_cases used : free body 0
    · rw [dif_pos used]
      intro es loop
      cases binder : loop.binder with
      | inl u =>
        cases u
        exact lambdaUsed_rawLoop_no_revisit n body used (encode n body).net vp rflow loop binder
      | inr v =>
        obtain ⟨rs,child,childBinder,eq⟩ := rawLoop_plugRight (lambdaUsed n body used) (encode n body).net
          (lambdaUsed_flow n body used) rflow (lambdaUsed_noReturn n body used) loop v binder
        have avoids := ih n rs a b child
        rw [childBinder] at avoids
        rw [eq]
        exact NoBinderRevisit.plugRight (lambdaUsed n body used) (encode n body).net avoids
    · rw [dif_neg used]
      intro es loop
      cases binder : loop.binder with
      | inl patch =>
        cases patch with
        | inl u =>
          cases u
          exact False.elim (lambdaUnused_no_rawLoop n body used (encode n body).net vp rflow loop binder)
        | inr u => have impossible:=loop.isLam; rw [binder] at impossible; cases impossible
      | inr v =>
        obtain ⟨rs,child,childBinder,eq⟩ := rawLoop_plugRight (lambdaUnused n body used) (encode n body).net
          (lambdaUnused_flow n body used) rflow (lambdaUnused_noReturn n body used) loop v binder
        have avoids := ih n rs a b child
        rw [childBinder] at avoids
        rw [eq]
        exact NoBinderRevisit.plugRight (lambdaUnused n body used) (encode n body).net avoids
  | app f arg hf ha =>
    dsimp only [encode] at loop ⊢
    cases binder : loop.binder with
    | inl patch =>
      rcases patch with u | (x | x)
      all_goals have impossible:=loop.isLam; rw [binder] at impossible; cases impossible
    | inr v =>
      obtain ⟨wp,fnFlow⟩ := encode_flow f n
      obtain ⟨vp,argFlow⟩ := encode_flow arg (n+1)
      have unionFlow := FlowOn.union (g:=(encode n f).net) (h:=(encode (n+1) arg).net)
        (bp:=initialBoundaryPolarity) (cp:=initialBoundaryPolarity) (wp:=wp) (vp:=vp) fnFlow argFlow
      obtain ⟨rs,child,childBinder,eq⟩ := rawLoop_plugRight (appPatch n f arg)
        (unionNet (encode n f).net (encode (n+1) arg).net) (appPatch_flow n f arg) unionFlow
        (appPatch_noReturn n f arg) loop v binder
      rw [eq]
      apply NoBinderRevisit.plugRight (appPatch n f arg) (unionNet (encode n f).net (encode (n+1) arg).net)
      cases v with
      | inl v =>
        obtain ⟨ss,localLoop,localBinder,localEq⟩ := rawLoop_unionL (encode n f).net (encode (n+1) arg).net child v childBinder
        have avoids := hf n ss a b localLoop
        rw [localBinder] at avoids
        rw [localEq]
        exact NoBinderRevisit.unionL (encode n f).net (encode (n+1) arg).net avoids
      | inr v =>
        obtain ⟨ss,localLoop,localBinder,localEq⟩ := rawLoop_unionR (encode n f).net (encode (n+1) arg).net child v childBinder
        have avoids := ha (n+1) ss a b localLoop
        rw [localBinder] at avoids
        rw [localEq]
        exact NoBinderRevisit.unionR (encode n f).net (encode (n+1) arg).net avoids
end Lamping.AG.InitialOffsets
