import Lamping.Lamping.CancellationReverseBlocks
import Lamping.Lamping.CancellationRoutes
import Lamping.Lamping.CancellationTypedBlocks
namespace Lamping.AG
open Graph
section
variable {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K → Label signature} {s : Schema}
/-- Every existing typed cancellation crossing contains this supplied actual
principal route, not merely some semantic-equivalent prefix. -/
theorem PathSite.cancel_fixed_prefix
    (site : PathSite s kept (B:=B) (W:=W) (V:=V))
    (cancel : IsCancellation s)
    (route : List (Endpoint site.net))
    (routeHead : route.head?=some (.inl ⟨.inr (.inl ()),.inl ()⟩))
    (routeLast : route.getLast?=some (site.net.wire (.inl ⟨.inr (.inr ()),.inl ()⟩)))
    (turns : ∀ e f,(e,f)∈route.zip route.tail →
      ∃ w d,site.net.wire e=.inr (.inr (w,d)) ∧f=.inr (.inr (w,!d)))
    (branch : Aux s.active) {es : List (Endpoint site.net)} {a b : Context}
    (labels : Labelling site.net es a b) (typed : ∃ k,accessKind site.net es=some k)
    (first : es.head?=some (site.net.wire (.inl ⟨.inr (.inl ()),.inr branch⟩))) :
    ∃ (q : Aux s.passive) (rest : List (Endpoint site.net)),HEq branch q ∧ es=site.net.wire (.inl ⟨.inr (.inl ()),.inr branch⟩)::
      (route.dropLast++site.net.wire (.inl ⟨.inr (.inr ()),.inl ()⟩)::
        (.inl ⟨.inr (.inr ()),.inr q⟩)::rest) ∧
      Labelling site.net ((.inl ⟨.inr (.inr ()),.inr q⟩)::rest) a b := by
  obtain ⟨remaining,seam,initial,left,after⟩ :=
    site.typed_active_aux_departure (by cases cancel <;> first | exact Or.inl rfl | exact Or.inr (Or.inl rfl) | exact Or.inr (Or.inr rfl)) branch labels typed first
  have afterTyped : ∃ k,accessKind site.net ((.inl ⟨.inr (.inl ()),.inl ()⟩)::remaining)=some k := by
    simpa only [initial,accessKind,List.getLast?_cons_cons] using typed
  have nonempty : route≠[] := by intro empty; rw [empty] at routeHead; cases routeHead
  obtain ⟨suffix,split,suffixHead,suffixLabels⟩ := after.typed_transparent_prefix
    afterTyped route nonempty (rfl.trans routeHead.symm) turns
  rw [routeLast] at suffixHead
  have suffixLast : ((.inl ⟨.inr (.inl ()),.inl ()⟩)::remaining).getLast?=suffix.getLast? := by
    rw [split]
    cases suffix with
    | nil => cases suffixHead
    | cons x xs => simp only [List.getLast?_append,List.getLast?_cons,Option.some_or]
  have suffixTyped : ∃ k,accessKind site.net suffix=some k := by
    simpa only [accessKind,suffixLast] using afterTyped
  obtain ⟨port,rest,middle,departure,right,tail⟩ := suffixLabels.typed_nonterminal_departure suffixTyped
    (site.net.wire (.inl ⟨.inr (.inr ()),.inl ()⟩)) suffixHead
    (.inr (.inr ())) (.inl ()) (site.net.wire.involutive _) (by cases cancel <;> rfl)
  cases port with
  | inl u => cases u; exact False.elim (right.distinct rfl)
  | inr q =>
    cases cancel
    all_goals
      obtain ⟨branchEq,contextEq⟩ := left.control_cancellation
        (by first | exact Or.inl rfl | exact Or.inr (Or.inl rfl) | exact Or.inr (Or.inr rfl)) right
      subst q
      subst middle
      refine ⟨branch,rest,HEq.rfl,?_,tail⟩
      rw [initial,split,departure]

/-- Every existing typed reverse cancellation crossing contains this supplied actual
principal route, not merely some semantic-equivalent prefix. -/
theorem PathSite.cancel_reverse_fixed_prefix
    (site : PathSite s kept (B:=B) (W:=W) (V:=V))
    (cancel : IsCancellation s)
    (route : List (Endpoint site.net))
    (routeHead : route.head?=some (.inl ⟨.inr (.inr ()),.inl ()⟩))
    (routeLast : route.getLast?=some (site.net.wire (.inl ⟨.inr (.inl ()),.inl ()⟩)))
    (turns : ∀ e f,(e,f)∈route.zip route.tail →
      ∃ w d,site.net.wire e=.inr (.inr (w,d)) ∧f=.inr (.inr (w,!d)))
    (branch : Aux s.passive) {es : List (Endpoint site.net)} {a b : Context}
    (labels : Labelling site.net es a b) (typed : ∃ k,accessKind site.net es=some k)
    (first : es.head?=some (site.net.wire (.inl ⟨.inr (.inr ()),.inr branch⟩))) :
    ∃ (q : Aux s.active) (rest : List (Endpoint site.net)),HEq branch q ∧ es=site.net.wire (.inl ⟨.inr (.inr ()),.inr branch⟩)::
      (route.dropLast++site.net.wire (.inl ⟨.inr (.inl ()),.inl ()⟩)::
        (.inl ⟨.inr (.inl ()),.inr q⟩)::rest) ∧
      Labelling site.net ((.inl ⟨.inr (.inl ()),.inr q⟩)::rest) a b := by
  obtain ⟨remaining,seam,initial,left,after⟩ :=
    site.typed_passive_aux_departure (by cases cancel <;> first | exact Or.inl rfl | exact Or.inr (Or.inl rfl) | exact Or.inr (Or.inr rfl)) branch labels typed first
  have afterTyped : ∃ k,accessKind site.net ((.inl ⟨.inr (.inr ()),.inl ()⟩)::remaining)=some k := by
    simpa only [initial,accessKind,List.getLast?_cons_cons] using typed
  have nonempty : route≠[] := by intro empty; rw [empty] at routeHead; cases routeHead
  obtain ⟨suffix,split,suffixHead,suffixLabels⟩ := after.typed_transparent_prefix
    afterTyped route nonempty (rfl.trans routeHead.symm) turns
  rw [routeLast] at suffixHead
  have suffixLast : ((.inl ⟨.inr (.inr ()),.inl ()⟩)::remaining).getLast?=suffix.getLast? := by
    rw [split]
    cases suffix with
    | nil => cases suffixHead
    | cons x xs => simp only [List.getLast?_append,List.getLast?_cons,Option.some_or]
  have suffixTyped : ∃ k,accessKind site.net suffix=some k := by
    simpa only [accessKind,suffixLast] using afterTyped
  obtain ⟨port,rest,middle,departure,right,tail⟩ := suffixLabels.typed_nonterminal_departure suffixTyped
    (site.net.wire (.inl ⟨.inr (.inl ()),.inl ()⟩)) suffixHead
    (.inr (.inl ())) (.inl ()) (site.net.wire.involutive _) (by cases cancel <;> rfl)
  cases port with
  | inl u => cases u; exact False.elim (right.distinct rfl)
  | inr q =>
    cases cancel
    all_goals
      obtain ⟨branchEq,contextEq⟩ := left.control_cancellation
        (by first | exact Or.inl rfl | exact Or.inr (Or.inl rfl) | exact Or.inr (Or.inr rfl)) right
      subst q
      subst middle
      refine ⟨branch,rest,HEq.rfl,?_,tail⟩
      rw [initial,split,departure]

end
end Lamping.AG