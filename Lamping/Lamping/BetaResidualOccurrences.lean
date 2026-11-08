import Lamping.Lamping.BetaResidualContraction
namespace Lamping.AG
open Graph
section Routes
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable {g : Net signature N B W}

private theorem first_or_vertex {es : List (Endpoint g)}
    (turns : ∀ e f,(e,f)∈es.zip es.tail →∃ w d,g.wire e=.inr (.inr (w,d)) ∧f=.inr (.inr (w,!d)))
    (e : Endpoint g) (member : e∈es) : es.head?=some e ∨∃ w d,e=.inr (.inr (w,d)) := by
  induction es with
  | nil => cases member
  | cons x xs ih =>
    rcases List.mem_cons.mp member with rfl |member
    · exact Or.inl rfl
    · cases xs with
      | nil => cases member
      | cons y ys =>
        have remaining : ∀ e f,(e,f)∈(y::ys).zip (y::ys).tail →
            ∃ w d,g.wire e=.inr (.inr (w,d)) ∧f=.inr (.inr (w,!d)) := by
          intro e f pair
          exact turns e f (List.mem_cons_of_mem _ pair)
        rcases ih remaining member with head |vertex
        · have same : y=e := Option.some.inj head
          obtain ⟨w,d,_,atY⟩ := turns x y (by simp)
          exact Or.inr ⟨w,!d,same.symm.trans atY⟩
        · exact Or.inr vertex

private theorem last_or_arrival_vertex {es : List (Endpoint g)}
    (turns : ∀ e f,(e,f)∈es.zip es.tail →∃ w d,g.wire e=.inr (.inr (w,d)) ∧f=.inr (.inr (w,!d)))
    (e : Endpoint g) (member : e∈es) : es.getLast?=some e ∨∃ w d,g.wire e=.inr (.inr (w,d)) := by
  induction es with
  | nil => cases member
  | cons x xs ih =>
    cases xs with
    | nil =>
      have same : e=x := List.mem_singleton.mp member
      subst e
      exact Or.inl rfl
    | cons y ys =>
      rcases List.mem_cons.mp member with rfl |member
      · obtain ⟨w,d,arrives,_⟩ := turns e y (by simp)
        exact Or.inr ⟨w,d,arrives⟩
      · have remaining : ∀ e f,(e,f)∈(y::ys).zip (y::ys).tail →
            ∃ w d,g.wire e=.inr (.inr (w,d)) ∧f=.inr (.inr (w,!d)) := by
          intro e f pair
          exact turns e f (List.mem_cons_of_mem _ pair)
        rcases ih remaining member with last |vertex
        · exact Or.inl (by simpa only [List.getLast?_cons_cons] using last)
        · exact Or.inr vertex

/-- Only the initial active application can occur as a node departure on
this actual principal component. Repeated transparent segments are allowed. -/
theorem BetaEdge.principal_node_occurrence (edge : BetaEdge g) (node : N) (p : Port (g.label node).sort)
    (member : (.inl ⟨node,p⟩ : Endpoint g)∈edge.principal) : node=edge.app := by
  rcases first_or_vertex edge.transparent _ member with first |⟨w,d,impossible⟩
  · have same := Option.some.inj (first.symm.trans edge.principalStart)
    exact congrArg Sigma.fst (Sum.inl.inj same)
  · cases impossible

/-- At node arrivals only the terminal active lambda occurs; no kept node
can be hidden inside a transparent principal subdivision. -/
theorem BetaEdge.principal_arrival_node_occurrence (edge : BetaEdge g) (node : N) (p : Port (g.label node).sort)
    (e : Endpoint g) (member : e∈edge.principal) (arrival : g.wire e=.inl ⟨node,p⟩) : node=edge.lam := by
  rcases last_or_arrival_vertex edge.transparent e member with last |⟨w,d,vertex⟩
  · have same : e=g.wire edge.ctxEnd := Option.some.inj (last.symm.trans edge.principalEnd)
    rw [same,Pairing.involutive] at arrival
    exact (congrArg Sigma.fst (Sum.inl.inj arrival)).symm
  · rw [arrival] at vertex
    cases vertex

theorem BetaEdge.reverse_node_occurrence (edge : BetaEdge g) (node : N) (p : Port (g.label node).sort)
    (member : (.inl ⟨node,p⟩ : Endpoint g)∈edge.reverseRoute) : node=edge.lam := by
  obtain ⟨e,inside,arrives⟩ := List.mem_map.mp member
  exact edge.principal_arrival_node_occurrence node p e (List.mem_reverse.mp inside) arrives

theorem BetaEdge.reverse_arrival_node_occurrence (edge : BetaEdge g) (node : N) (p : Port (g.label node).sort)
    (e : Endpoint g) (member : e∈edge.reverseRoute) (arrival : g.wire e=.inl ⟨node,p⟩) : node=edge.app := by
  obtain ⟨f,inside,same⟩ := List.mem_map.mp member
  rw [←same,Pairing.involutive] at arrival
  exact edge.principal_node_occurrence node p (arrival ▸ List.mem_reverse.mp inside)
end Routes

section Residuals
variable {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K → Label signature} {i : Nat}
variable (site : PathSite (.beta i) kept (B:=B) (W:=W) (V:=V))
local notation "cut" => cutFragment site.net (pathPartition (Schema.beta i) V) site.closed

theorem PathSite.outsideEnd_injective : Function.Injective site.outsideEnd := by
  intro e f same
  let split := fragmentEnd (B:=B) (W:=W) site.net.label (pathPartition (Schema.beta i) V)
  change split.invFun (.inl e)=split.invFun (.inl f) at same
  have mapped := congrArg split same
  simpa only [split.right_inv,Sum.inl.injEq] using mapped

/-- Neither departure nor arrival at a retained node can lie in one of the
principal blocks inserted by this actual beta residual. -/
theorem SiteBetaGeometry.kept_not_principal {edge : BetaEdge site.net}
    (geometry : SiteBetaGeometry site edge) (node : K) (p : Port (kept node).sort) :
    (.inl ⟨.inl node,p⟩ : Endpoint site.net)∉edge.principal ∧
      site.net.wire (.inl ⟨.inl node,p⟩)∉edge.principal := by
  have appEq : edge.app=.inr (.inl ()) := congrArg Sigma.fst (Sum.inl.inj geometry.appCtx)
  have lamEq : edge.lam=.inr (.inr ()) := congrArg Sigma.fst (Sum.inl.inj geometry.body)
  constructor
  · intro member
    have same := edge.principal_node_occurrence (.inl node) p member
    rw [appEq] at same
    cases same
  · intro member
    have same := edge.principal_arrival_node_occurrence (.inl node) p _ member (Pairing.involutive _ _)
    rw [lamEq] at same
    cases same

theorem SiteBetaGeometry.kept_not_reverse {edge : BetaEdge site.net}
    (geometry : SiteBetaGeometry site edge) (node : K) (p : Port (kept node).sort) :
    (.inl ⟨.inl node,p⟩ : Endpoint site.net)∉edge.reverseRoute ∧
      site.net.wire (.inl ⟨.inl node,p⟩)∉edge.reverseRoute := by
  have appEq : edge.app=.inr (.inl ()) := congrArg Sigma.fst (Sum.inl.inj geometry.appCtx)
  have lamEq : edge.lam=.inr (.inr ()) := congrArg Sigma.fst (Sum.inl.inj geometry.body)
  constructor
  · intro member
    have same := edge.reverse_node_occurrence (.inl node) p member
    rw [lamEq] at same
    cases same
  · intro member
    have same := edge.reverse_arrival_node_occurrence (.inl node) p _ member (Pairing.involutive _ _)
    rw [appEq] at same
    cases same

/-- An occurrence cut retains both overlapping residuals and the exact old
ordinal. It is an output of finite residual analysis, not a graph invariant. -/
structure BetaResidualOccurrence (edge : BetaEdge site.net)
    (raw : List (PlugSegment cut (Schema.beta i).right.net)) (old : List (Endpoint site.net))
    (endpoint : Endpoint cut) (ordinal : Nat) where
  before : List (PlugSegment cut (Schema.beta i).right.net)
  after : List (PlugSegment cut (Schema.beta i).right.net)
  oldBefore : List (Endpoint site.net)
  oldAfter : List (Endpoint site.net)
  raw_eq : raw=before++ .inl endpoint::after
  old_eq : old=oldBefore++site.outsideEnd endpoint::oldAfter
  position : oldBefore.length=ordinal
  prefixResidual : BetaPathResidual site edge (before++[.inl endpoint]) (oldBefore++[site.outsideEnd endpoint])
  suffixResidual : BetaPathResidual site edge (.inl endpoint::after) (site.outsideEnd endpoint::oldAfter)

theorem BetaResidualOccurrence.prefix_head {edge : BetaEdge site.net} {raw old endpoint ordinal}
    (cutAt : BetaResidualOccurrence site edge raw old endpoint ordinal) :
    (cutAt.before++[Sum.inl endpoint]).head?=raw.head? := by
  apply Eq.trans _ (congrArg List.head? cutAt.raw_eq).symm
  cases cutAt.before <;> rfl

private theorem occurrence_zero {edge : BetaEdge site.net} {raw old endpoint}
    (relation : BetaPathResidual site edge raw old)
    (atZero : old[0]?=some (site.outsideEnd endpoint)) :
    Nonempty (BetaResidualOccurrence site edge raw old endpoint 0) := by
  have rawHead : ∃ e,raw.head?=some (.inl e) := by cases relation <;> exact ⟨_,rfl⟩
  obtain ⟨e,rawHead⟩ := rawHead
  have oldHead := relation.head site rawHead
  have zeroHead : old.head?=some (site.outsideEnd endpoint) := by simpa only [List.head?_eq_getElem?] using atZero
  have same := site.outsideEnd_injective (Option.some.inj (oldHead.symm.trans zeroHead))
  subst e
  obtain ⟨rawTail,rawSplit⟩ := List.head?_eq_some_iff.mp rawHead
  obtain ⟨oldTail,oldSplit⟩ := List.head?_eq_some_iff.mp oldHead
  exact ⟨⟨[],rawTail,[],oldTail,rawSplit,oldSplit,rfl,.single endpoint,
    by simpa only [rawSplit,oldSplit] using relation⟩⟩

/-- Cut at the specified old occurrence, not at an arbitrary visit of the
same physical endpoint. The two forbidden blocks are checked separately. -/
theorem BetaPathResidual.split_occurrence {edge : BetaEdge site.net} {raw old endpoint ordinal}
    (relation : BetaPathResidual site edge raw old)
    (notPrincipal : site.outsideEnd endpoint∉edge.principal)
    (notReverse : site.outsideEnd endpoint∉edge.reverseRoute)
    (atOccurrence : old[ordinal]?=some (site.outsideEnd endpoint)) :
    Nonempty (BetaResidualOccurrence site edge raw old endpoint ordinal) := by
  induction relation generalizing ordinal with
  | single e =>
    cases ordinal with
    | zero => exact occurrence_zero site (.single e) atOccurrence
    | succ n => cases atOccurrence
  | @outside e f tail oldTail rest ih =>
    cases ordinal with
    | zero => exact occurrence_zero site (.outside rest) atOccurrence
    | succ n =>
      obtain ⟨cutAt⟩ := ih atOccurrence
      have prefixHead : (cutAt.before++[Sum.inl endpoint]).head?=some (.inl f) := cutAt.prefix_head site
      obtain ⟨prefixTail,prefixSplit⟩ := List.head?_eq_some_iff.mp prefixHead
      have before := cutAt.prefixResidual
      rw [prefixSplit] at before
      refine ⟨⟨.inl e::cutAt.before,cutAt.after,site.outsideEnd e::cutAt.oldBefore,cutAt.oldAfter,
        ?_,?_,?_,?_,cutAt.suffixResidual⟩⟩
      · simpa only [List.cons_append] using congrArg (Sum.inl e::·) cutAt.raw_eq
      · simpa only [List.cons_append] using congrArg (site.outsideEnd e::·) cutAt.old_eq
      · simp only [List.length_cons,cutAt.position]
      · simpa only [List.cons_append,←prefixSplit] using BetaPathResidual.outside (e:=e) before
  | @context e tail oldTail arrival rest ih =>
    cases ordinal with
    | zero => exact occurrence_zero site (.context arrival rest) atOccurrence
    | succ n =>
      change (edge.principal++oldTail)[n]?=some (site.outsideEnd endpoint) at atOccurrence
      have bound : edge.principal.length≤n := by
        by_cases bound : edge.principal.length≤n
        · exact bound
        · have within : n<edge.principal.length := by omega
          rw [List.getElem?_append_left within] at atOccurrence
          exact False.elim (notPrincipal (List.mem_of_getElem? atOccurrence))
      rw [List.getElem?_append_right bound] at atOccurrence
      obtain ⟨cutAt⟩ := ih atOccurrence
      have prefixHead : (cutAt.before++[Sum.inl endpoint]).head?=
          some (.inl (.inr (.inl (.inr (.inr true))))) := cutAt.prefix_head site
      obtain ⟨prefixTail,prefixSplit⟩ := List.head?_eq_some_iff.mp prefixHead
      have before := cutAt.prefixResidual
      rw [prefixSplit] at before
      refine ⟨⟨.inl e::.inr (.inr (.inl (.inl false)))::cutAt.before,cutAt.after,
        site.outsideEnd e::(edge.principal++cutAt.oldBefore),cutAt.oldAfter,?_,?_,?_,?_,cutAt.suffixResidual⟩⟩
      · simpa only [List.cons_append] using congrArg (fun xs => .inl e::.inr (.inr (.inl (.inl false)))::xs) cutAt.raw_eq
      · simpa only [List.cons_append,List.append_assoc] using congrArg (fun xs => site.outsideEnd e::(edge.principal++xs)) cutAt.old_eq
      · simp only [List.length_cons,List.length_append]
        have position := cutAt.position
        omega
      · simpa only [List.cons_append,List.append_assoc,←prefixSplit] using BetaPathResidual.context arrival before
  | @binding e tail oldTail arrival rest ih =>
    cases ordinal with
    | zero => exact occurrence_zero site (.binding arrival rest) atOccurrence
    | succ n =>
      change (edge.reverseRoute++oldTail)[n]?=some (site.outsideEnd endpoint) at atOccurrence
      have bound : edge.reverseRoute.length≤n := by
        by_cases bound : edge.reverseRoute.length≤n
        · exact bound
        · have within : n<edge.reverseRoute.length := by omega
          rw [List.getElem?_append_left within] at atOccurrence
          exact False.elim (notReverse (List.mem_of_getElem? atOccurrence))
      rw [List.getElem?_append_right bound] at atOccurrence
      obtain ⟨cutAt⟩ := ih atOccurrence
      have prefixHead : (cutAt.before++[Sum.inl endpoint]).head?=
          some (.inl (.inr (.inl (.inr (.inl true))))) := cutAt.prefix_head site
      obtain ⟨prefixTail,prefixSplit⟩ := List.head?_eq_some_iff.mp prefixHead
      have before := cutAt.prefixResidual
      rw [prefixSplit] at before
      refine ⟨⟨.inl e::.inr (.inr (.inl (.inr false)))::cutAt.before,cutAt.after,
        site.outsideEnd e::(edge.reverseRoute++cutAt.oldBefore),cutAt.oldAfter,?_,?_,?_,?_,cutAt.suffixResidual⟩⟩
      · simpa only [List.cons_append] using congrArg (fun xs => .inl e::.inr (.inr (.inl (.inr false)))::xs) cutAt.raw_eq
      · simpa only [List.cons_append,List.append_assoc] using congrArg (fun xs => site.outsideEnd e::(edge.reverseRoute++xs)) cutAt.old_eq
      · simp only [List.length_cons,List.length_append]
        have position := cutAt.position
        omega
      · simpa only [List.cons_append,List.append_assoc,←prefixSplit] using BetaPathResidual.binding arrival before

private theorem equal_ordinal_splits {T : Type} {left right : List T} {e f : T} {after tail : List T}
    (same : left++e::after=right++f::tail) (length : left.length=right.length) :
    left=right ∧e=f ∧after=tail := by
  induction left generalizing right with
  | nil =>
    cases right with
    | nil => have eqs := List.cons.inj same; exact ⟨rfl,eqs.1,eqs.2⟩
    | cons h right => simp at length
  | cons h left ih =>
    cases right with
    | nil => simp at length
    | cons k right =>
      obtain ⟨heads,rest⟩ := List.cons.inj same
      have lengths : left.length=right.length := by simpa only [List.length_cons,Nat.succ.injEq] using length
      obtain ⟨rfl,rfl,rfl⟩ := ih rest lengths
      subst k
      exact ⟨rfl,rfl,rfl⟩

theorem BetaPathResidual.split_decomposition {edge : BetaEdge site.net} {raw old endpoint}
    (relation : BetaPathResidual site edge raw old)
    (notPrincipal : site.outsideEnd endpoint∉edge.principal)
    (notReverse : site.outsideEnd endpoint∉edge.reverseRoute)
    (pre after : List (Endpoint site.net))
    (split : old=pre++site.outsideEnd endpoint::after) :
    ∃ cutAt : BetaResidualOccurrence site edge raw old endpoint pre.length,
      cutAt.oldBefore=pre ∧cutAt.oldAfter=after := by
  have atOccurrence : old[pre.length]?=some (site.outsideEnd endpoint) := by
    rw [split,List.getElem?_append_right (Nat.le_refl _),Nat.sub_self]
    rfl
  obtain ⟨cutAt⟩ := relation.split_occurrence site notPrincipal notReverse atOccurrence
  obtain ⟨beforeEq,_,afterEq⟩ := equal_ordinal_splits (cutAt.old_eq.symm.trans split) cutAt.position
  exact ⟨cutAt,beforeEq,afterEq⟩

/-- Retained-node departures require no exclusion oracle: the actual beta
principal geometry excludes them from both inserted blocks. -/
theorem BetaPathResidual.split_kept_departure {edge : BetaEdge site.net} {raw old}
    (relation : BetaPathResidual site edge raw old) (geometry : SiteBetaGeometry site edge)
    (node : K) (p : Port (kept node).sort) (pre after : List (Endpoint site.net))
    (split : old=pre++(.inl ⟨.inl node,p⟩)::after) :
    ∃ cutAt : BetaResidualOccurrence site edge raw old (.inl ⟨node,p⟩) pre.length,
      cutAt.oldBefore=pre ∧cutAt.oldAfter=after := by
  exact relation.split_decomposition site (endpoint:=.inl ⟨node,p⟩) (geometry.kept_not_principal site node p).1
    (geometry.kept_not_reverse site node p).1 pre after split
end Residuals
end Lamping.AG







