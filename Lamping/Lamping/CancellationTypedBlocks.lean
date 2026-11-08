import Lamping.Lamping.ControlPrincipalPrefixes
import Lamping.Lamping.MatchedControlInputs
namespace Lamping.AG
open Graph
private theorem control_aux_untyped (op : Op) (p : Aux op)
    (control : op=.fan ∨op=.cro ∨op=.bra) : portKind (.op op) (.inr p)=none := by
  cases op <;> simp_all [portKind]

private theorem control_aux_principal (op : Op) (p : Aux op) (q : Port (.op op))
    (control : op=.fan ∨op=.cro ∨op=.bra)
    (forced : ControlAuxOutput (.op op) (.inr p) q) : q=.inl () := by
  cases op <;> simp_all [ControlAuxOutput]

section
variable {s : Schema} {K B W V : Type} [FiniteNames K] [FiniteNames B]
  [FiniteNames W] [FiniteNames V] {kept : K → Label signature}
variable (site : PathSite s kept (B:=B) (W:=W) (V:=V))

/-- A supplied typed old path which has already left the active principal
crosses the whole actual W route and the passive control. No path is extended. -/
theorem PathSite.typed_passive_control_prefix
    (control : s.passive=.fan ∨s.passive=.cro ∨s.passive=.bra)
    {es : List (Endpoint site.net)} {a b : Context}
    (labels : Labelling site.net es a b) (typed : ∃ k,accessKind site.net es=some k)
    (first : es.head?=some (.inl ⟨.inr (.inl ()),.inl ()⟩)) :
    ∃ (pre : List (Endpoint site.net)) (q : Aux s.passive) (rest : List (Endpoint site.net)) (middle : Context),
      es=pre++(site.net.wire (.inl ⟨.inr (.inr ()),.inl ()⟩)::
        (.inl ⟨.inr (.inr ()),.inr q⟩)::rest) ∧
      Traversal s.high (.op s.passive) (.inl ()) (.inr q) a middle ∧
      Labelling site.net ((.inl ⟨.inr (.inr ()),.inr q⟩)::rest) middle b := by
  obtain ⟨route,routeHead,routeLast,turns⟩ := site.principal_route
  have nonempty : route≠[] := by intro empty; rw [empty] at routeHead; cases routeHead
  obtain ⟨suffix,split,suffixHead,remaining⟩ := labels.typed_transparent_prefix typed route nonempty
    (first.trans routeHead.symm) turns
  rw [routeLast] at suffixHead
  have suffixLast : es.getLast?=suffix.getLast? := by
    rw [split]
    cases suffix with
    | nil => cases suffixHead
    | cons x xs => simp only [List.getLast?_append,List.getLast?_cons,Option.some_or]
  have suffixTyped : ∃ k,accessKind site.net suffix=some k := by
    simpa only [accessKind,suffixLast] using typed
  have nonterminal : portKind (.op s.passive) (.inl ())=none := by
    rcases control with same | same | same <;> rw [same] <;> rfl
  obtain ⟨port,rest,middle,depart,rule,tail⟩ := remaining.typed_nonterminal_departure suffixTyped
    (site.net.wire (.inl ⟨.inr (.inr ()),.inl ()⟩)) suffixHead (.inr (.inr ())) (.inl ())
    (site.net.wire.involutive _) nonterminal
  change Traversal s.high (.op s.passive) (.inl ()) port a middle at rule
  cases port with
  | inl u => cases u; exact False.elim (rule.distinct rfl)
  | inr q => exact ⟨route.dropLast,q,rest,middle,split.trans (congrArg (List.append route.dropLast) depart),rule,tail⟩

/-- An existing typed path entering an active control auxiliary has already
made its real principal departure. This is a decomposition, not completion. -/
theorem PathSite.typed_active_aux_departure
    (control : s.active=.fan ∨s.active=.cro ∨s.active=.bra)
    (p : Aux s.active) {es : List (Endpoint site.net)} {a b : Context}
    (labels : Labelling site.net es a b) (typed : ∃ k,accessKind site.net es=some k)
    (first : es.head?=some (site.net.wire (.inl ⟨.inr (.inl ()),.inr p⟩))) :
    ∃ rest middle,
      es=site.net.wire (.inl ⟨.inr (.inl ()),.inr p⟩)::
        (.inl ⟨.inr (.inl ()),.inl ()⟩)::rest ∧
      Traversal s.low (.op s.active) (.inr p) (.inl ()) a middle ∧
      Labelling site.net ((.inl ⟨.inr (.inl ()),.inl ()⟩)::rest) middle b := by
  have untyped := control_aux_untyped s.active p control
  obtain ⟨q,rest,middle,split,rule,tail⟩ := labels.typed_nonterminal_departure typed
    (site.net.wire (.inl ⟨.inr (.inl ()),.inr p⟩)) first (.inr (.inl ())) (.inr p)
    (site.net.wire.involutive _) untyped
  change Traversal s.low (.op s.active) (.inr p) q a middle at rule
  have principal : q=.inl () := control_aux_principal s.active p q control rule.control_aux
  subst q
  exact ⟨rest,middle,split,rule,tail⟩
end

/-- A real pair of equal-index/equal-control passages cancels on the same
auxiliary and returns the exact input context, including its low shell. -/
theorem Traversal.control_cancellation {op : Op} {index : Nat} {p q : Aux op}
    {a middle b : Context} (control : op=.fan ∨op=.cro ∨op=.bra)
    (first : Traversal index (.op op) (.inr p) (.inl ()) a middle)
    (second : Traversal index (.op op) (.inl ()) (.inr q) middle b) : p=q ∧a=b := by
  have branches := first.reverse.control_auxiliary_unique control second
  subst q
  exact ⟨rfl,first.reverse.output_unique second⟩

section
variable {s : Schema} {K B W V : Type} [FiniteNames K] [FiniteNames B]
  [FiniteNames W] [FiniteNames V] {kept : K → Label signature}
variable (site : PathSite s kept (B:=B) (W:=W) (V:=V))

/-- Actual typed control-to-control crossing, preserving both real primitive
turns and their shared seam. Only the already supplied finite path is split. -/
theorem PathSite.typed_control_crossing_prefix
    (active : s.active=.fan ∨s.active=.cro ∨s.active=.bra)
    (passive : s.passive=.fan ∨s.passive=.cro ∨s.passive=.bra)
    (p : Aux s.active) {es : List (Endpoint site.net)} {a b : Context}
    (labels : Labelling site.net es a b) (typed : ∃ k,accessKind site.net es=some k)
    (first : es.head?=some (site.net.wire (.inl ⟨.inr (.inl ()),.inr p⟩))) :
    ∃ (pre : List (Endpoint site.net)) (q : Aux s.passive) (rest : List (Endpoint site.net))
      (seam middle : Context),
      es=site.net.wire (.inl ⟨.inr (.inl ()),.inr p⟩)::
        (pre++site.net.wire (.inl ⟨.inr (.inr ()),.inl ()⟩)::
          (.inl ⟨.inr (.inr ()),.inr q⟩)::rest) ∧
      Traversal s.low (.op s.active) (.inr p) (.inl ()) a seam ∧
      Traversal s.high (.op s.passive) (.inl ()) (.inr q) seam middle ∧
      Labelling site.net ((.inl ⟨.inr (.inr ()),.inr q⟩)::rest) middle b := by
  obtain ⟨after,seam,split,firstTurn,remaining⟩ := site.typed_active_aux_departure active p labels typed first
  have afterTyped : ∃ k,accessKind site.net ((.inl ⟨.inr (.inl ()),.inl ()⟩)::after)=some k := by
    simpa only [split,accessKind,List.getLast?_cons_cons] using typed
  obtain ⟨pre,q,rest,middle,tailSplit,secondTurn,tail⟩ :=
    site.typed_passive_control_prefix passive remaining afterTyped rfl
  exact ⟨pre,q,rest,seam,middle,split.trans (congrArg (_::·) tailSplit),firstTurn,secondTurn,tail⟩
end

section
variable {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K → Label signature} {i : Nat}

/-- The actual fan cancellation crossing must use the original branch and
returns exactly the entry context before its already existing typed suffix. -/
theorem PathSite.fan_cancel_typed_block
    (site : PathSite (.fanCancel i) kept (B:=B) (W:=W) (V:=V))
    (branch : Bool) {es : List (Endpoint site.net)} {a b : Context}
    (labels : Labelling site.net es a b) (typed : ∃ k,accessKind site.net es=some k)
    (first : es.head?=some (site.net.wire (.inl ⟨.inr (.inl ()),.inr branch⟩))) :
    ∃ pre rest,es=site.net.wire (.inl ⟨.inr (.inl ()),.inr branch⟩)::
      (pre++site.net.wire (.inl ⟨.inr (.inr ()),.inl ()⟩)::
        (.inl ⟨.inr (.inr ()),.inr branch⟩)::rest) ∧
      Labelling site.net ((.inl ⟨.inr (.inr ()),.inr branch⟩)::rest) a b := by
  obtain ⟨pre,q,rest,seam,middle,split,left,right,tail⟩ :=
    site.typed_control_crossing_prefix (Or.inl rfl) (Or.inl rfl) branch labels typed first
  obtain ⟨same,contextEq⟩ := left.control_cancellation (Or.inl rfl) right
  subst q
  subst middle
  exact ⟨pre,rest,split,tail⟩

/-- The unary cancellation also consumes its real whole crossing and preserves the exact input. -/
theorem PathSite.cro_cancel_typed_block
    (site : PathSite (.croCancel i) kept (B:=B) (W:=W) (V:=V))
    (branch : Unit) {es : List (Endpoint site.net)} {a b : Context}
    (labels : Labelling site.net es a b) (typed : ∃ k,accessKind site.net es=some k)
    (first : es.head?=some (site.net.wire (.inl ⟨.inr (.inl ()),.inr branch⟩))) :
    ∃ pre rest,es=site.net.wire (.inl ⟨.inr (.inl ()),.inr branch⟩)::
      (pre++site.net.wire (.inl ⟨.inr (.inr ()),.inl ()⟩)::
        (.inl ⟨.inr (.inr ()),.inr branch⟩)::rest) ∧
      Labelling site.net ((.inl ⟨.inr (.inr ()),.inr branch⟩)::rest) a b := by
  obtain ⟨pre,q,rest,seam,middle,split,left,right,tail⟩ :=
    site.typed_control_crossing_prefix (Or.inr (Or.inl rfl)) (Or.inr (Or.inl rfl)) branch labels typed first
  obtain ⟨same,contextEq⟩ := left.control_cancellation (Or.inr (Or.inl rfl)) right
  subst q
  subst middle
  exact ⟨pre,rest,split,tail⟩

/-- The unary cancellation also consumes its real whole crossing and preserves the exact input. -/
theorem PathSite.bra_cancel_typed_block
    (site : PathSite (.braCancel i) kept (B:=B) (W:=W) (V:=V))
    (branch : Unit) {es : List (Endpoint site.net)} {a b : Context}
    (labels : Labelling site.net es a b) (typed : ∃ k,accessKind site.net es=some k)
    (first : es.head?=some (site.net.wire (.inl ⟨.inr (.inl ()),.inr branch⟩))) :
    ∃ pre rest,es=site.net.wire (.inl ⟨.inr (.inl ()),.inr branch⟩)::
      (pre++site.net.wire (.inl ⟨.inr (.inr ()),.inl ()⟩)::
        (.inl ⟨.inr (.inr ()),.inr branch⟩)::rest) ∧
      Labelling site.net ((.inl ⟨.inr (.inr ()),.inr branch⟩)::rest) a b := by
  obtain ⟨pre,q,rest,seam,middle,split,left,right,tail⟩ :=
    site.typed_control_crossing_prefix (Or.inr (Or.inr rfl)) (Or.inr (Or.inr rfl)) branch labels typed first
  obtain ⟨same,contextEq⟩ := left.control_cancellation (Or.inr (Or.inr rfl)) right
  subst q
  subst middle
  exact ⟨pre,rest,split,tail⟩
end
end Lamping.AG
