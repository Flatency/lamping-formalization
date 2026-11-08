import Lamping.Lamping.TransparentRouteObservations
namespace Lamping.AG
open Graph
section
variable {s : Schema} {K B W V : Type} [FiniteNames K] [FiniteNames B]
  [FiniteNames W] [FiniteNames V] {kept : K → Label signature}
variable (site : PathSite s kept (B:=B) (W:=W) (V:=V))

/-- The actual removed principal-prefix segments carry no proper arrival.
This strengthens the same finite typed decomposition, rather than every
arbitrary bare block residual. -/
theorem PathSite.typed_passive_prefix_unobserved
    (control : s.passive=.fan ∨s.passive=.cro ∨s.passive=.bra)
    {es : List (Endpoint site.net)} {a b : Context}
    (labels : Labelling site.net es a b) (typed : ∃ k,accessKind site.net es=some k)
    (first : es.head?=some (.inl ⟨.inr (.inl ()),.inl ()⟩)) :
    ∃ (pre : List (Endpoint site.net)) (q : Aux s.passive) (rest : List (Endpoint site.net)) (middle : Context),
      es=pre++(site.net.wire (.inl ⟨.inr (.inr ()),.inl ()⟩)::
        (.inl ⟨.inr (.inr ()),.inr q⟩)::rest) ∧
      (∀ e∈pre,accessKind site.net [e]=none) ∧
      Traversal s.high (.op s.passive) (.inl ()) (.inr q) a middle ∧
      Labelling site.net ((.inl ⟨.inr (.inr ()),.inr q⟩)::rest) middle b := by
  obtain ⟨route,routeHead,routeLast,turns⟩ := site.principal_route
  have terminalNone : accessKind site.net [site.net.wire (.inl ⟨.inr (.inr ()),.inl ()⟩)]=none := by
    simp only [accessKind,List.getLast?_cons,List.getLast?_nil,Option.getD_none,Option.bind_some,Pairing.involutive]
    change portKind (.op s.passive) (.inl ())=none
    rcases control with same | same | same <;> rw [same] <;> rfl
  have unobserved := transparent_route_no_proper_arrivals route _ routeLast terminalNone turns
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
  | inr q => exact ⟨route.dropLast,q,rest,middle,split.trans (congrArg (List.append route.dropLast) depart),
      (fun e member => unobserved e ((List.dropLast_sublist route).subset member)),rule,tail⟩


/-- The same actual no-proper-arrival fact in the opposite principal direction. -/
theorem PathSite.typed_active_prefix_unobserved
    (control : s.active=.fan ∨s.active=.cro ∨s.active=.bra)
    {es : List (Endpoint site.net)} {a b : Context}
    (labels : Labelling site.net es a b) (typed : ∃ k,accessKind site.net es=some k)
    (first : es.head?=some (.inl ⟨.inr (.inr ()),.inl ()⟩)) :
    ∃ (pre : List (Endpoint site.net)) (q : Aux s.active) (rest : List (Endpoint site.net)) (middle : Context),
      es=pre++(site.net.wire (.inl ⟨.inr (.inl ()),.inl ()⟩)::
        (.inl ⟨.inr (.inl ()),.inr q⟩)::rest) ∧
      (∀ e∈pre,accessKind site.net [e]=none) ∧
      Traversal s.low (.op s.active) (.inl ()) (.inr q) a middle ∧
      Labelling site.net ((.inl ⟨.inr (.inl ()),.inr q⟩)::rest) middle b := by
  obtain ⟨route,routeHead,routeLast,turns⟩ := site.reverse_principal_route
  have terminalNone : accessKind site.net [site.net.wire (.inl ⟨.inr (.inl ()),.inl ()⟩)]=none := by
    simp only [accessKind,List.getLast?_cons,List.getLast?_nil,Option.getD_none,Option.bind_some,Pairing.involutive]
    change portKind (.op s.active) (.inl ())=none
    rcases control with same | same | same <;> rw [same] <;> rfl
  have unobserved := transparent_route_no_proper_arrivals route _ routeLast terminalNone turns
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
  have nonterminal : portKind (.op s.active) (.inl ())=none := by
    rcases control with same | same | same <;> rw [same] <;> rfl
  obtain ⟨port,rest,middle,depart,rule,tail⟩ := remaining.typed_nonterminal_departure suffixTyped
    (site.net.wire (.inl ⟨.inr (.inl ()),.inl ()⟩)) suffixHead (.inr (.inl ())) (.inl ())
    (site.net.wire.involutive _) nonterminal
  change Traversal s.low (.op s.active) (.inl ()) port a middle at rule
  cases port with
  | inl u => cases u; exact False.elim (rule.distinct rfl)
  | inr q => exact ⟨route.dropLast,q,rest,middle,split.trans (congrArg (List.append route.dropLast) depart),
      (fun e member => unobserved e ((List.dropLast_sublist route).subset member)),rule,tail⟩

end
end Lamping.AG
