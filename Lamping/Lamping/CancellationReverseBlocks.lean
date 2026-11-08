import Lamping.Lamping.CancellationTypedBlocks
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

/-- The reverse-side cancellation decomposition consumes only an already
supplied proper-ended path; it never extends its control prefix. -/
theorem PathSite.typed_passive_aux_departure
    (control : s.passive=.fan ∨s.passive=.cro ∨s.passive=.bra)
    (p : Aux s.passive) {es : List (Endpoint site.net)} {a b : Context}
    (labels : Labelling site.net es a b) (typed : ∃ k,accessKind site.net es=some k)
    (first : es.head?=some (site.net.wire (.inl ⟨.inr (.inr ()),.inr p⟩))) :
    ∃ rest middle,
      es=site.net.wire (.inl ⟨.inr (.inr ()),.inr p⟩)::
        (.inl ⟨.inr (.inr ()),.inl ()⟩)::rest ∧
      Traversal s.high (.op s.passive) (.inr p) (.inl ()) a middle ∧
      Labelling site.net ((.inl ⟨.inr (.inr ()),.inl ()⟩)::rest) middle b := by
  have untyped := control_aux_untyped s.passive p control
  obtain ⟨q,rest,middle,split,rule,tail⟩ := labels.typed_nonterminal_departure typed
    (site.net.wire (.inl ⟨.inr (.inr ()),.inr p⟩)) first (.inr (.inr ())) (.inr p)
    (site.net.wire.involutive _) untyped
  change Traversal s.high (.op s.passive) (.inr p) q a middle at rule
  have principal : q=.inl () := control_aux_principal s.passive p q control rule.control_aux
  subst q
  exact ⟨rest,middle,split,rule,tail⟩

theorem PathSite.typed_reverse_control_crossing_prefix
    (active : s.passive=.fan ∨s.passive=.cro ∨s.passive=.bra)
    (passive : s.active=.fan ∨s.active=.cro ∨s.active=.bra)
    (p : Aux s.passive) {es : List (Endpoint site.net)} {a b : Context}
    (labels : Labelling site.net es a b) (typed : ∃ k,accessKind site.net es=some k)
    (first : es.head?=some (site.net.wire (.inl ⟨.inr (.inr ()),.inr p⟩))) :
    ∃ (pre : List (Endpoint site.net)) (q : Aux s.active) (rest : List (Endpoint site.net))
      (seam middle : Context),
      es=site.net.wire (.inl ⟨.inr (.inr ()),.inr p⟩)::
        (pre++site.net.wire (.inl ⟨.inr (.inl ()),.inl ()⟩)::
          (.inl ⟨.inr (.inl ()),.inr q⟩)::rest) ∧
      Traversal s.high (.op s.passive) (.inr p) (.inl ()) a seam ∧
      Traversal s.low (.op s.active) (.inl ()) (.inr q) seam middle ∧
      Labelling site.net ((.inl ⟨.inr (.inl ()),.inr q⟩)::rest) middle b := by
  obtain ⟨after,seam,split,firstTurn,remaining⟩ := site.typed_passive_aux_departure active p labels typed first
  have afterTyped : ∃ k,accessKind site.net ((.inl ⟨.inr (.inr ()),.inl ()⟩)::after)=some k := by
    simpa only [split,accessKind,List.getLast?_cons_cons] using typed
  obtain ⟨pre,q,rest,middle,tailSplit,secondTurn,tail⟩ :=
    site.typed_active_control_prefix passive remaining afterTyped rfl
  exact ⟨pre,q,rest,seam,middle,split.trans (congrArg (_::·) tailSplit),firstTurn,secondTurn,tail⟩
end

section
variable {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K → Label signature} {i : Nat}
theorem PathSite.fan_cancel_reverse_typed_block
    (site : PathSite (.fanCancel i) kept (B:=B) (W:=W) (V:=V))
    (branch : Bool) {es : List (Endpoint site.net)} {a b : Context}
    (labels : Labelling site.net es a b) (typed : ∃ k,accessKind site.net es=some k)
    (first : es.head?=some (site.net.wire (.inl ⟨.inr (.inr ()),.inr branch⟩))) :
    ∃ pre rest,es=site.net.wire (.inl ⟨.inr (.inr ()),.inr branch⟩)::
      (pre++site.net.wire (.inl ⟨.inr (.inl ()),.inl ()⟩)::
        (.inl ⟨.inr (.inl ()),.inr branch⟩)::rest) ∧
      Labelling site.net ((.inl ⟨.inr (.inl ()),.inr branch⟩)::rest) a b := by
  obtain ⟨pre,q,rest,seam,middle,split,left,right,tail⟩ :=
    site.typed_reverse_control_crossing_prefix (Or.inl rfl) (Or.inl rfl) branch labels typed first
  obtain ⟨same,contextEq⟩ := left.control_cancellation (Or.inl rfl) right
  subst q
  subst middle
  exact ⟨pre,rest,split,tail⟩

/-- The unary cancellation also consumes its real whole crossing and preserves the exact input. -/
theorem PathSite.cro_cancel_reverse_typed_block
    (site : PathSite (.croCancel i) kept (B:=B) (W:=W) (V:=V))
    (branch : Unit) {es : List (Endpoint site.net)} {a b : Context}
    (labels : Labelling site.net es a b) (typed : ∃ k,accessKind site.net es=some k)
    (first : es.head?=some (site.net.wire (.inl ⟨.inr (.inr ()),.inr branch⟩))) :
    ∃ pre rest,es=site.net.wire (.inl ⟨.inr (.inr ()),.inr branch⟩)::
      (pre++site.net.wire (.inl ⟨.inr (.inl ()),.inl ()⟩)::
        (.inl ⟨.inr (.inl ()),.inr branch⟩)::rest) ∧
      Labelling site.net ((.inl ⟨.inr (.inl ()),.inr branch⟩)::rest) a b := by
  obtain ⟨pre,q,rest,seam,middle,split,left,right,tail⟩ :=
    site.typed_reverse_control_crossing_prefix (Or.inr (Or.inl rfl)) (Or.inr (Or.inl rfl)) branch labels typed first
  obtain ⟨same,contextEq⟩ := left.control_cancellation (Or.inr (Or.inl rfl)) right
  subst q
  subst middle
  exact ⟨pre,rest,split,tail⟩

/-- The unary cancellation also consumes its real whole crossing and preserves the exact input. -/
theorem PathSite.bra_cancel_reverse_typed_block
    (site : PathSite (.braCancel i) kept (B:=B) (W:=W) (V:=V))
    (branch : Unit) {es : List (Endpoint site.net)} {a b : Context}
    (labels : Labelling site.net es a b) (typed : ∃ k,accessKind site.net es=some k)
    (first : es.head?=some (site.net.wire (.inl ⟨.inr (.inr ()),.inr branch⟩))) :
    ∃ pre rest,es=site.net.wire (.inl ⟨.inr (.inr ()),.inr branch⟩)::
      (pre++site.net.wire (.inl ⟨.inr (.inl ()),.inl ()⟩)::
        (.inl ⟨.inr (.inl ()),.inr branch⟩)::rest) ∧
      Labelling site.net ((.inl ⟨.inr (.inl ()),.inr branch⟩)::rest) a b := by
  obtain ⟨pre,q,rest,seam,middle,split,left,right,tail⟩ :=
    site.typed_reverse_control_crossing_prefix (Or.inr (Or.inr rfl)) (Or.inr (Or.inr rfl)) branch labels typed first
  obtain ⟨same,contextEq⟩ := left.control_cancellation (Or.inr (Or.inr rfl)) right
  subst q
  subst middle
  exact ⟨pre,rest,split,tail⟩
end
end Lamping.AG
