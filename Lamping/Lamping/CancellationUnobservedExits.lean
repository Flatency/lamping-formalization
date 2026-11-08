import Lamping.Lamping.CancellationUnobservedBlocks
import Lamping.Lamping.CancellationReverseBlocks
import Lamping.Lamping.CancellationSourceExcursions
namespace Lamping.AG
open Graph
private theorem control_port_none (op : Op) (p : Port (.op op))
    (control : op=.fan ∨op=.cro ∨op=.bra) : portKind (.op op) p=none := by
  cases op <;> simp_all [portKind]

section
variable {s : Schema} {K B W V : Type} [FiniteNames K] [FiniteNames B]
  [FiniteNames W] [FiniteNames V] {kept : K → Label signature}
variable (site : PathSite s kept (B:=B) (W:=W) (V:=V))

/-- The whole actual control crossing front has no proper arrival, including
its first auxiliary entrance and final principal arrival. -/
theorem PathSite.typed_control_unobserved_front
    (entryControl : s.active=.fan ∨s.active=.cro ∨s.active=.bra)
    (exitControl : s.passive=.fan ∨s.passive=.cro ∨s.passive=.bra)
    (p : Aux s.active) {es : List (Endpoint site.net)} {a b : Context}
    (labels : Labelling site.net es a b) (typed : ∃ k,accessKind site.net es=some k)
    (first : es.head?=some (site.net.wire (.inl ⟨.inr (.inl ()),.inr p⟩))) :
    ∃ (front : List (Endpoint site.net)) (q : Aux s.passive) (rest : List (Endpoint site.net))
      (seam middle : Context),
      es=front++(.inl ⟨.inr (.inr ()),.inr q⟩)::rest ∧front≠[] ∧
      (∀ e∈front,accessKind site.net [e]=none) ∧
      Traversal s.low (.op s.active) (.inr p) (.inl ()) a seam ∧
      Traversal s.high (.op s.passive) (.inl ()) (.inr q) seam middle ∧
      Labelling site.net ((.inl ⟨.inr (.inr ()),.inr q⟩)::rest) middle b := by
  obtain ⟨after,seam,split,firstTurn,remaining⟩ := site.typed_active_aux_departure entryControl p labels typed first
  have afterTyped : ∃ k,accessKind site.net ((.inl ⟨.inr (.inl ()),.inl ()⟩)::after)=some k := by
    simpa only [split,accessKind,List.getLast?_cons_cons] using typed
  obtain ⟨pre,q,rest,middle,tailSplit,unobserved,secondTurn,tail⟩ :=
    site.typed_passive_prefix_unobserved exitControl remaining afterTyped rfl
  have entryNone : accessKind site.net [site.net.wire (.inl ⟨.inr (.inl ()),.inr p⟩)]=none := by
    simp only [accessKind,List.getLast?_cons,List.getLast?_nil,Option.getD_none,Option.bind_some,Pairing.involutive]
    exact control_port_none s.active (.inr p) entryControl
  have endNone : accessKind site.net [site.net.wire (.inl ⟨.inr (.inr ()),.inl ()⟩)]=none := by
    simp only [accessKind,List.getLast?_cons,List.getLast?_nil,Option.getD_none,Option.bind_some,Pairing.involutive]
    exact control_port_none s.passive (.inl ()) exitControl
  refine ⟨site.net.wire (.inl ⟨.inr (.inl ()),.inr p⟩)::
    (pre++[site.net.wire (.inl ⟨.inr (.inr ()),.inl ()⟩)]),q,rest,seam,middle,?_,by simp,?_,firstTurn,secondTurn,tail⟩
  · simpa only [List.cons_append,List.append_assoc,List.singleton_append] using
      split.trans (congrArg (_::·) tailSplit)
  · intro e member
    simp only [List.mem_cons,List.mem_append,List.not_mem_nil,or_false] at member
    rcases member with same | member | same
    · subst e
      exact entryNone
    · exact unobserved e member
    · subst e
      exact endNone

/-- The opposite physical frontier direction also removes no proper arrival. -/
theorem PathSite.typed_reverse_control_unobserved_front
    (entryControl : s.passive=.fan ∨s.passive=.cro ∨s.passive=.bra)
    (exitControl : s.active=.fan ∨s.active=.cro ∨s.active=.bra)
    (p : Aux s.passive) {es : List (Endpoint site.net)} {a b : Context}
    (labels : Labelling site.net es a b) (typed : ∃ k,accessKind site.net es=some k)
    (first : es.head?=some (site.net.wire (.inl ⟨.inr (.inr ()),.inr p⟩))) :
    ∃ (front : List (Endpoint site.net)) (q : Aux s.active) (rest : List (Endpoint site.net))
      (seam middle : Context),
      es=front++(.inl ⟨.inr (.inl ()),.inr q⟩)::rest ∧front≠[] ∧
      (∀ e∈front,accessKind site.net [e]=none) ∧
      Traversal s.high (.op s.passive) (.inr p) (.inl ()) a seam ∧
      Traversal s.low (.op s.active) (.inl ()) (.inr q) seam middle ∧
      Labelling site.net ((.inl ⟨.inr (.inl ()),.inr q⟩)::rest) middle b := by
  obtain ⟨after,seam,split,firstTurn,remaining⟩ := site.typed_passive_aux_departure entryControl p labels typed first
  have afterTyped : ∃ k,accessKind site.net ((.inl ⟨.inr (.inr ()),.inl ()⟩)::after)=some k := by
    simpa only [split,accessKind,List.getLast?_cons_cons] using typed
  obtain ⟨pre,q,rest,middle,tailSplit,unobserved,secondTurn,tail⟩ :=
    site.typed_active_prefix_unobserved exitControl remaining afterTyped rfl
  have entryNone : accessKind site.net [site.net.wire (.inl ⟨.inr (.inr ()),.inr p⟩)]=none := by
    simp only [accessKind,List.getLast?_cons,List.getLast?_nil,Option.getD_none,Option.bind_some,Pairing.involutive]
    exact control_port_none s.passive (.inr p) entryControl
  have endNone : accessKind site.net [site.net.wire (.inl ⟨.inr (.inl ()),.inl ()⟩)]=none := by
    simp only [accessKind,List.getLast?_cons,List.getLast?_nil,Option.getD_none,Option.bind_some,Pairing.involutive]
    exact control_port_none s.active (.inl ()) exitControl
  refine ⟨site.net.wire (.inl ⟨.inr (.inr ()),.inr p⟩)::
    (pre++[site.net.wire (.inl ⟨.inr (.inl ()),.inl ()⟩)]),q,rest,seam,middle,?_,by simp,?_,firstTurn,secondTurn,tail⟩
  · simpa only [List.cons_append,List.append_assoc,List.singleton_append] using
      split.trans (congrArg (_::·) tailSplit)
  · intro e member
    simp only [List.mem_cons,List.mem_append,List.not_mem_nil,or_false] at member
    rcases member with same | member | same
    · subst e
      exact entryNone
    · exact unobserved e member
    · subst e
      exact endNone

/-- Actual cancellation frontiers have a nonempty removed front with no
proper observations at any position. The original context and literal
already existing paired-frontier suffix are retained. -/
theorem PathSite.cancellation_unobserved_exit (cancel : IsCancellation s) (f : s.Frontier)
    {es : List (Endpoint site.net)} {a b : Context}
    (labels : Labelling site.net es a b) (typed : ∃ k,accessKind site.net es=some k)
    (first : es.head?=some (site.net.wire (site.outsideEnd (.inr (.inl (.inr f)))))) :
    ∃ (front rest : List (Endpoint site.net)),
      es=front++(site.outsideEnd (.inr (.inl (.inr (cancellationMate s f)))))::rest ∧
      front≠[] ∧(∀ e∈front,accessKind site.net [e]=none) ∧
      Labelling site.net ((site.outsideEnd (.inr (.inl (.inr (cancellationMate s f)))))::rest) a b := by
  cases cancel with
  | fan i =>
    cases f with
    | inl branch =>
      obtain ⟨front,q,rest,seam,middle,split,nonempty,unobserved,left,right,tail⟩ :=
        site.typed_control_unobserved_front (Or.inl rfl) (Or.inl rfl) branch labels typed first
      obtain ⟨same,contextEq⟩ := left.control_cancellation (Or.inl rfl) right
      subst q
      subst middle
      exact ⟨front,rest,split,nonempty,unobserved,tail⟩
    | inr branch =>
      obtain ⟨front,q,rest,seam,middle,split,nonempty,unobserved,left,right,tail⟩ :=
        site.typed_reverse_control_unobserved_front (Or.inl rfl) (Or.inl rfl) branch labels typed first
      obtain ⟨same,contextEq⟩ := left.control_cancellation (Or.inl rfl) right
      subst q
      subst middle
      exact ⟨front,rest,split,nonempty,unobserved,tail⟩
  | cro i =>
    cases f with
    | inl branch =>
      obtain ⟨front,q,rest,seam,middle,split,nonempty,unobserved,left,right,tail⟩ :=
        site.typed_control_unobserved_front (Or.inr (Or.inl rfl)) (Or.inr (Or.inl rfl)) branch labels typed first
      obtain ⟨same,contextEq⟩ := left.control_cancellation (Or.inr (Or.inl rfl)) right
      subst q
      subst middle
      exact ⟨front,rest,split,nonempty,unobserved,tail⟩
    | inr branch =>
      obtain ⟨front,q,rest,seam,middle,split,nonempty,unobserved,left,right,tail⟩ :=
        site.typed_reverse_control_unobserved_front (Or.inr (Or.inl rfl)) (Or.inr (Or.inl rfl)) branch labels typed first
      obtain ⟨same,contextEq⟩ := left.control_cancellation (Or.inr (Or.inl rfl)) right
      subst q
      subst middle
      exact ⟨front,rest,split,nonempty,unobserved,tail⟩
  | bra i =>
    cases f with
    | inl branch =>
      obtain ⟨front,q,rest,seam,middle,split,nonempty,unobserved,left,right,tail⟩ :=
        site.typed_control_unobserved_front (Or.inr (Or.inr rfl)) (Or.inr (Or.inr rfl)) branch labels typed first
      obtain ⟨same,contextEq⟩ := left.control_cancellation (Or.inr (Or.inr rfl)) right
      subst q
      subst middle
      exact ⟨front,rest,split,nonempty,unobserved,tail⟩
    | inr branch =>
      obtain ⟨front,q,rest,seam,middle,split,nonempty,unobserved,left,right,tail⟩ :=
        site.typed_reverse_control_unobserved_front (Or.inr (Or.inr rfl)) (Or.inr (Or.inr rfl)) branch labels typed first
      obtain ⟨same,contextEq⟩ := left.control_cancellation (Or.inr (Or.inr rfl)) right
      subst q
      subst middle
      exact ⟨front,rest,split,nonempty,unobserved,tail⟩

end
end Lamping.AG
