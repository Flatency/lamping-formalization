import Lamping.Lamping.ActionSourceBlocks
namespace Lamping.AG
open Graph
section
variable {s : Schema} {K B W V : Type}
variable [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K → Label signature} (site : PathSite s kept (B:=B) (W:=W) (V:=V))

/-- The selected reverse physical principal route is consumed from an already
present typed path; a control principal cannot itself be a typed terminal. -/
theorem PathSite.typed_action_reverse_principal
    (control : s.active=.fan ∨s.active=.cro ∨s.active=.bra)
    (principal : SiteActionPrincipal site)
    {es : List (Endpoint site.net)} {a b : Context}
    (labels : Labelling site.net es a b) (typed : ∃ k,accessKind site.net es=some k)
    (first : es.head?=some (.inl ⟨.inr (.inr ()),.inl ()⟩)) :
    ∃ (q : Aux s.active) (rest : List (Endpoint site.net)) (middle : Context),
      es=(reverseEdges principal.edges).dropLast++
        (site.net.wire (.inl ⟨.inr (.inl ()),.inl ()⟩))::(.inl ⟨.inr (.inl ()),.inr q⟩)::rest ∧
      Traversal s.low (.op s.active) (.inl ()) (.inr q) a middle ∧
      Labelling site.net ((.inl ⟨.inr (.inl ()),.inr q⟩)::rest) middle b := by
  let route := reverseEdges principal.edges
  have routeHead : route.head?=some (.inl ⟨.inr (.inr ()),.inl ()⟩) := by
    simp only [route,reverseEdges,List.head?_map,List.head?_reverse,principal.last,Option.map_some,Pairing.involutive]
  have routeLast : route.getLast?=some (site.net.wire (.inl ⟨.inr (.inl ()),.inl ()⟩)) := by
    simp only [route,reverseEdges,List.getLast?_map,List.getLast?_reverse,principal.first,Option.map_some]
  have nonempty : route≠[] := by intro empty; rw [empty] at routeHead; cases routeHead
  obtain ⟨suffix,split,suffixHead,remaining⟩ := labels.typed_transparent_prefix typed route nonempty
    (first.trans routeHead.symm) (transparent_reverse_turns principal.edges principal.transparent)
  have suffixFirst := suffixHead.trans routeLast
  have last : es.getLast?=suffix.getLast? := by
    rw [split]
    cases suffix with
    | nil => cases suffixFirst
    | cons e suffix => simp only [List.getLast?_append,List.getLast?_cons,Option.some_or]
  have suffixTyped : ∃ k,accessKind site.net suffix=some k := by simpa only [accessKind,last] using typed
  have noTerminal : portKind (.op s.active) (.inl ())=none := by
    rcases control with same|same|same <;> rw [same] <;> rfl
  obtain ⟨port,rest,middle,depart,rule,tail⟩ := remaining.typed_nonterminal_departure suffixTyped
    (site.net.wire (.inl ⟨.inr (.inl ()),.inl ()⟩)) suffixFirst (.inr (.inl ())) (.inl ())
    (site.net.wire.involutive _) noTerminal
  cases port with
  | inl u => cases u; exact False.elim (rule.distinct rfl)
  | inr q => exact ⟨q,rest,middle,split.trans (congrArg (List.append route.dropLast) depart),rule,tail⟩

/-- At a passive auxiliary, retain a legitimate typed stop or split the next
real node turn. A principal departure is followed through the entire selected
reverse principal route; an auxiliary departure is a literal two-edge block. -/
theorem PathSite.typed_action_passive_cases
    (control : s.active=.fan ∨s.active=.cro ∨s.active=.bra)
    (principal : SiteActionPrincipal site) (p : Aux s.passive)
    {es : List (Endpoint site.net)} {a b : Context}
    (labels : Labelling site.net es a b) (typed : ∃ k,accessKind site.net es=some k)
    (first : es.head?=some (site.net.wire (.inl ⟨.inr (.inr ()),.inr p⟩))) :
    (es=[site.net.wire (.inl ⟨.inr (.inr ()),.inr p⟩)] ∧a=b ∧
      ∃ k,portKind (.op s.passive) (.inr p)=some k) ∨
    (∃ (q : Aux s.passive) (rest : List (Endpoint site.net)) (middle : Context),
      es=site.passiveCanonical p q++rest ∧
      Traversal s.high (.op s.passive) (.inr p) (.inr q) a middle ∧
      Labelling site.net ((.inl ⟨.inr (.inr ()),.inr q⟩)::rest) middle b) ∨
    (∃ (q : Aux s.active) (rest : List (Endpoint site.net)) (seam middle : Context),
      es=site.net.wire (.inl ⟨.inr (.inr ()),.inr p⟩)::
        ((reverseEdges principal.edges).dropLast++
          (site.net.wire (.inl ⟨.inr (.inl ()),.inl ()⟩))::(.inl ⟨.inr (.inl ()),.inr q⟩)::rest) ∧
      Traversal s.high (.op s.passive) (.inr p) (.inl ()) a seam ∧
      Traversal s.low (.op s.active) (.inl ()) (.inr q) seam middle ∧
      Labelling site.net ((.inl ⟨.inr (.inl ()),.inr q⟩)::rest) middle b) := by
  obtain ⟨rest,split⟩ := List.head?_eq_some_iff.mp first
  subst es
  cases rest with
  | nil =>
    cases labels
    obtain ⟨kind,observed⟩ := typed
    simp only [accessKind,List.getLast?_cons,List.getLast?_nil,Option.getD_none,Option.bind_some] at observed
    rw [Pairing.involutive] at observed
    exact Or.inl ⟨rfl,rfl,kind,observed⟩
  | cons e rest =>
    cases labels with
    | cons turn tail =>
      rw [Pairing.involutive] at turn
      obtain ⟨port,same,rule⟩ := turn.from_node (.inr (.inr ())) (.inr p) rfl
      subst e
      cases port with
      | inr q => exact Or.inr (Or.inl ⟨q,rest,_,rfl,rule,tail⟩)
      | inl u =>
        cases u
        have tailTyped : ∃ k,accessKind site.net ((.inl ⟨.inr (.inr ()),.inl ()⟩)::rest)=some k := by
          simpa only [accessKind,List.getLast?_cons_cons] using typed
        obtain ⟨q,rest,middle,split,active,remaining⟩ :=
          site.typed_action_reverse_principal control principal tail tailTyped rfl
        exact Or.inr (Or.inr ⟨q,rest,_,middle,congrArg (_::·) split,rule,active,remaining⟩)
end
end Lamping.AG
