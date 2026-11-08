import Lamping.Lamping.TraceSeams
namespace Lamping.AG
open Graph Lambda
private theorem no_app_ctx_output {kind : Kind} {p q : Port kind}
    (hd : ForwardPorts kind p q) (sort : kind=.op .app) (role : HEq q appCtx) : False := by
  subst kind
  have same : q=appCtx := eq_of_heq role
  subst q
  rcases hd.2 with impossible | impossible <;> cases impossible
private theorem no_lam_incoming_output {kind : Kind} {p q : Port kind}
    (hd : ForwardPorts kind p q) (sort : kind=.op .lam)
    (role : HEq q (Sum.inl () : Port (.op .lam)) ∨ HEq q lamBind) : False := by
  subst kind
  rcases role with ctx | bind
  · have same : q=.inl () := eq_of_heq ctx; subst q; cases hd.2
  · have same : q=lamBind := eq_of_heq bind; subst q; cases hd.2
section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable {g : Net signature N B W}
private theorem no_incoming_turn_output {root : B} (node : N) (p q : Port (g.label node).sort)
    (hd : ForwardPorts (g.label node).sort p q) {role : ProperRole} {index : Nat}
    (atRole : AtProperRole g root (.inl ⟨node,q⟩) role index) (incoming : role.incoming) : False := by
  cases atRole with
  | appCtx n q i lab role => exact no_app_ctx_output hd (congrArg Label.sort lab) role
  | lamCtx n q i lab role => exact no_lam_incoming_output hd (congrArg Label.sort lab) (Or.inl role)
  | lamBind n q i lab role => exact no_lam_incoming_output hd (congrArg Label.sort lab) (Or.inr role)
  | appFun | appArg | lamBody => cases incoming

private theorem Forward.no_incoming_tail {root : B} {es : List (Endpoint g)} (fw : Forward g es)
    (i : Nat) (e : Endpoint g) (atE : es[i+1]?=some e) (role : ProperRole) (index : Nat)
    (atRole : AtProperRole g root e role index) (incoming : role.incoming) : False := by
  induction fw generalizing i with
  | single x => simp at atE
  | node n p q arrives leaves direction after ih =>
    cases i with
    | zero =>
      have same : _=e := Option.some.inj atE
      rw [←same,leaves] at atRole
      exact no_incoming_turn_output n p q direction atRole incoming
    | succ i => exact ih i atE
  | transparent w d arrives leaves after ih =>
    cases i with
    | zero =>
      have same : _=e := Option.some.inj atE
      rw [←same,leaves] at atRole
      cases atRole
    | succ i => exact ih i atE

/-- Proper incoming ports cannot depart as a segment anywhere in an ordinary
rooted forward path, including its selected first occurrence. -/
theorem Forward.no_incoming_occurrence {root : B} {es : List (Endpoint g)} (fw : Forward g es)
    (rooted : es.head?=some (.inr (.inl root))) (i : Nat) (e : Endpoint g) (atE : es[i]?=some e)
    (role : ProperRole) (index : Nat) (atRole : AtProperRole g root e role index) (incoming : role.incoming) : False := by
  cases i with
  | zero =>
    have atHead : es.head?=some e := by cases es <;> exact atE
    have same := Option.some.inj (atHead.symm.trans rooted)
    subst e
    cases atRole
    cases incoming
  | succ i => exact fw.no_incoming_tail i e atE role index atRole incoming

 theorem Forward.no_reversed_source {root : B} {es : List (Endpoint g)} (fw : Forward g es)
    (rooted : es.head?=some (.inr (.inl root))) (i : Nat) (r : BetaEdge g)
    (atE : es[i]?=some r.ctxEnd) : False :=
  fw.no_incoming_occurrence rooted i r.ctxEnd atE .lamCtx r.index
    (.lamCtx r.lam r.lamCtx r.index r.lamLabel r.lamCtx_role) True.intro
private theorem Forward.last_direction (pre : List (Endpoint g)) (last : Endpoint g)
    (fw : Forward g (pre++[last])) (nonempty : pre≠[]) :
    ∃ previous,pre.getLast?=some previous ∧Forward g pre ∧ExpandedDirection g (g.wire previous) last := by
  induction pre with
  | nil => exact False.elim (nonempty rfl)
  | cons x pre ih =>
    cases pre with
    | nil =>
      cases fw with
      | node n p q arrives leaves direction after =>
        refine ⟨x,rfl,.single _,?_⟩
        rw [arrives,leaves]
        exact .node n p q direction
      | transparent w d arrives leaves after =>
        refine ⟨x,rfl,.single _,?_⟩
        rw [arrives,leaves]
        exact .transparent w d
    | cons y pre =>
      cases fw with
      | node n p q arrives leaves direction after =>
        obtain ⟨previous,finish,first,step⟩ := ih after (by simp)
        exact ⟨previous,by simpa only [List.getLast?_cons_cons] using finish,
          .node n p q arrives leaves direction first,step⟩
      | transparent w d arrives leaves after =>
        obtain ⟨previous,finish,first,step⟩ := ih after (by simp)
        exact ⟨previous,by simpa only [List.getLast?_cons_cons] using finish,
          .transparent w d arrives leaves first,step⟩

private theorem direction_ending_W {x y : Endpoint g} (step : ExpandedDirection g x y)
    (w : W) (d : Bool) (finish : y=.inr (.inr (w,d))) : x=.inr (.inr (w,!d)) := by
  cases step with
  | node => cases finish
  | bindToCtx => cases finish
  | funToArg => cases finish
  | transparent other bit => cases bit <;> cases d <;> simp_all
/-- A rooted ordinary path ending at one side of a W must have traversed its
other side immediately before. The physical prefix and its direction remain. -/
theorem Forward.transparent_predecessor {root : B} {es : List (Endpoint g)}
    (fw : Forward g es) (rooted : es.head?=some (.inr (.inl root))) (w : W) (d : Bool)
    (finish : es.getLast?=some (.inr (.inr (w,d)))) :
    ∃ pre,es=pre++[.inr (.inr (w,d))] ∧Forward g pre ∧pre.head?=some (.inr (.inl root)) ∧
      pre.getLast?=some (g.wire (.inr (.inr (w,!d)))) := by
  obtain ⟨pre,decomp⟩ := List.getLast?_eq_some_iff.mp finish
  have nonempty : pre≠[] := by
    intro empty
    rw [empty] at decomp
    rw [decomp] at rooted
    cases rooted
  rw [decomp] at fw
  obtain ⟨previous,last,first,step⟩ := fw.last_direction pre _ nonempty
  have arrival : g.wire previous=.inr (.inr (w,!d)) := direction_ending_W step w d rfl
  refine ⟨pre,decomp,first,?_,?_⟩
  · rw [decomp] at rooted
    cases pre with
    | nil => exact False.elim (nonempty rfl)
    | cons => exact rooted
  · rw [last]
    congr 1
    exact ((congrArg g.wire.mate arrival).symm.trans (Pairing.involutive g.wire previous)).symm

/-- Reverse tracing a finite transparent route must reach its proper incoming
start, which an ordinary root path cannot depart. This handles every W segment. -/
theorem Forward.no_reverse_transparent {root : B} {es : List (Endpoint g)}
    (fw : Forward g es) (rooted : es.head?=some (.inr (.inl root)))
    (route : List (Endpoint g)) (first target : Endpoint g)
    (start : route.head?=some first) (finish : route.getLast?=some (g.wire target))
    (transparent : ∀ e f,(e,f)∈route.zip route.tail →
      ∃ w d,g.wire e=.inr (.inr (w,d)) ∧f=.inr (.inr (w,!d)))
    (role : ProperRole) (index : Nat) (incoming : AtProperRole g root target role index)
    (isIncoming : role.incoming) (ends : es.getLast?=some (g.wire first)) : False := by
  induction route generalizing es first with
  | nil => cases start
  | cons x route ih =>
    have same : x=first := Option.some.inj start
    subst first
    cases route with
    | nil =>
      have last : x=g.wire target := Option.some.inj finish
      rw [last,Pairing.involutive] at ends
      obtain ⟨pre,decomp⟩ := List.getLast?_eq_some_iff.mp ends
      have atTarget : es[pre.length]?=some target := by
        rw [decomp]
        simp
      exact fw.no_incoming_occurrence rooted pre.length target atTarget role index incoming isIncoming
    | cons y route =>
      obtain ⟨w,d,arrives,leaves⟩ := transparent x y (by simp)
      rw [arrives] at ends
      obtain ⟨pre,decomp,first,rootedPre,lastPre⟩ := fw.transparent_predecessor rooted w d ends
      apply ih first rootedPre y rfl (by simpa only [List.getLast?_cons_cons] using finish)
      · intro e f pair
        exact transparent e f (by simp only [List.zip_cons_cons,List.tail_cons,List.mem_cons]; exact Or.inr pair)
      · simpa only [leaves] using lastPre

 theorem Forward.no_reversed_target {root : B} {es : List (Endpoint g)} (fw : Forward g es)
    (rooted : es.head?=some (.inr (.inl root))) (r : BetaEdge g)
    (finish : es.getLast?=some (g.wire r.funEnd)) : False :=
  fw.no_reverse_transparent rooted r.principal r.funEnd r.ctxEnd r.principalStart r.principalEnd r.transparent
    .lamCtx r.index (.lamCtx r.lam r.lamCtx r.index r.lamLabel r.lamCtx_role) True.intro finish
end
end Lamping.AG


