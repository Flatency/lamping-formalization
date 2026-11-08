import Lamping.Lamping.CancellationTypedBlocks
import Lamping.Lamping.ActionCanonicalRoutes
namespace Lamping.AG
open Graph
section
variable {s : Schema} {K B W V : Type}
variable [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K → Label signature} (site : PathSite s kept (B:=B) (W:=W) (V:=V))

/-- Decompose an EXISTING typed path entering an active control auxiliary.
The actual principal W route is consumed with the same intermediate context.
The suffix may be a singleton: a passive lambda context is a legal terminal.
No continuation through that proper node is asserted. -/
theorem PathSite.typed_action_active_prefix
    (control : s.active=.fan ∨s.active=.cro ∨s.active=.bra)
    (principal : SiteActionPrincipal site) (p : Aux s.active)
    {es : List (Endpoint site.net)} {a b : Context}
    (labels : Labelling site.net es a b) (typed : ∃ k,accessKind site.net es=some k)
    (first : es.head?=some (site.net.wire (.inl ⟨.inr (.inl ()),.inr p⟩))) :
    ∃ (suffix : List (Endpoint site.net)) (middle : Context),
      es=site.net.wire (.inl ⟨.inr (.inl ()),.inr p⟩)::(principal.edges.dropLast++suffix) ∧
      suffix.head?=some (site.net.wire (.inl ⟨.inr (.inr ()),.inl ()⟩)) ∧
      Traversal s.low (.op s.active) (.inr p) (.inl ()) a middle ∧
      Labelling site.net suffix middle b ∧
      (∃ k,accessKind site.net suffix=some k) := by
  obtain ⟨rest,middle,split,rule,tail⟩ := site.typed_active_aux_departure control p labels typed first
  have tailTyped : ∃ k,accessKind site.net ((.inl ⟨.inr (.inl ()),.inl ()⟩)::rest)=some k := by
    simpa only [accessKind,split,List.getLast?_cons_cons] using typed
  have nonempty : principal.edges≠[] := by
    intro empty
    have firstRoute := principal.first
    rw [empty] at firstRoute
    cases firstRoute
  obtain ⟨suffix,decomposition,suffixFirst,remaining⟩ := tail.typed_transparent_prefix tailTyped principal.edges
    nonempty (by exact principal.first.symm) principal.transparent
  have suffixHead : suffix.head?=some (site.net.wire (.inl ⟨.inr (.inr ()),.inl ()⟩)) :=
    suffixFirst.trans principal.last
  refine ⟨suffix,middle,split.trans (congrArg (_::·) decomposition),?_,rule,remaining,?_⟩
  · exact suffixHead
  · have last : ((.inl ⟨.inr (.inl ()),.inl ()⟩ : Endpoint site.net)::rest).getLast?=suffix.getLast? := by
      rw [decomposition]
      cases suffix with
      | nil => cases suffixHead
      | cons e suffix => simp only [List.getLast?_append,List.getLast?_cons,Option.some_or]
    simpa only [accessKind,last] using tailTyped
end
end Lamping.AG
