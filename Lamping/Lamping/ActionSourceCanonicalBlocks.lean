import Lamping.Lamping.ActionSourceDirection
namespace Lamping.AG
open Graph
section
variable {s : Schema} {K B W V : Type}
variable [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K → Label signature} (site : PathSite s kept (B:=B) (W:=W) (V:=V))

theorem SiteActionPrincipal.reverse_crossing_edges (principal : SiteActionPrincipal site)
    (p : Aux s.active) (q : Aux s.passive) :
    reverseEdges (principal.crossing site p q)=
      site.net.wire (.inl ⟨.inr (.inr ()),.inr q⟩)::
        (reverseEdges principal.edges++[.inl ⟨.inr (.inl ()),.inr p⟩]) := by
  simp [SiteActionPrincipal.crossing,reverseEdges,List.map_append,List.map_reverse,Pairing.involutive]

/-- Canonical finite source decomposition at a passive auxiliary. Each complete
alternative carries the actual labelled prefix and actual labelled suffix at
the same overlap occurrence. A typed terminal is kept as a separate case. -/
theorem PathSite.typed_passive_canonical_cases
    (control : s.active=.fan ∨s.active=.cro ∨s.active=.bra)
    (principal : SiteActionPrincipal site) (p : Aux s.passive)
    {es : List (Endpoint site.net)} {a b : Context}
    (labels : Labelling site.net es a b) (typed : ∃ k,accessKind site.net es=some k)
    (first : es.head?=some (site.net.wire (.inl ⟨.inr (.inr ()),.inr p⟩))) :
    (es=[site.net.wire (.inl ⟨.inr (.inr ()),.inr p⟩)] ∧a=b ∧
      ∃ k,portKind (.op s.passive) (.inr p)=some k) ∨
    (∃ (q : Aux s.passive) (rest : List (Endpoint site.net)) (middle : Context),
      es=site.passiveCanonical p q++rest ∧
      Labelling site.net (site.passiveCanonical p q) a middle ∧
      Labelling site.net ((.inl ⟨.inr (.inr ()),.inr q⟩)::rest) middle b) ∨
    (∃ (q : Aux s.active) (rest : List (Endpoint site.net)) (middle : Context),
      es=reverseEdges (principal.crossing site q p)++rest ∧
      Labelling site.net (reverseEdges (principal.crossing site q p)) a middle ∧
      Labelling site.net ((.inl ⟨.inr (.inl ()),.inr q⟩)::rest) middle b) := by
  rcases site.typed_action_passive_cases control principal p labels typed first with
    terminal|⟨q,rest,middle,split,rule,tail⟩|⟨q,rest,seam,middle,split,passive,active,tail⟩
  · exact Or.inl terminal
  · have localLabels : Labelling site.net (site.passiveCanonical p q) a middle := by
      apply Labelling.cons
      · rw [Pairing.involutive]
        exact .node _ _ _ rule
      · exact .single _ _
    exact Or.inr (Or.inl ⟨q,rest,middle,split,localLabels,tail⟩)
  · have last : (reverseEdges principal.edges).getLast?=
        some (site.net.wire (.inl ⟨.inr (.inl ()),.inl ()⟩)) := by
      simp only [reverseEdges,List.getLast?_map,List.getLast?_reverse,principal.first,Option.map_some]
    obtain ⟨routePre,routeEnd⟩ := List.getLast?_eq_some_iff.mp last
    have rebuild : (reverseEdges principal.edges).dropLast++
        [site.net.wire (.inl ⟨.inr (.inl ()),.inl ()⟩)]=reverseEdges principal.edges := by
      rw [routeEnd,List.dropLast_concat]
    have decomposition : es=reverseEdges (principal.crossing site q p)++rest := by
      rw [principal.reverse_crossing_edges site q p]
      change es=site.net.wire (.inl ⟨.inr (.inr ()),.inr p⟩)::
        ((reverseEdges principal.edges++[.inl ⟨.inr (.inl ()),.inr q⟩])++rest)
      rw [List.append_assoc,List.singleton_append]
      rw [←rebuild]
      simpa only [List.append_assoc,List.singleton_append] using split
    have oldForward : Labelling s.left (leftRoute s.active s.passive s.low s.high q p) middle a :=
      (leftRoute_labeling_iff s.active s.passive s.low s.high q p middle a).mpr
        ⟨seam,active.reverse,passive.reverse⟩
    have localLabels : Labelling site.net (reverseEdges (principal.crossing site q p)) a middle :=
      ((principal.crossing_labels_iff site q p middle a).mpr oldForward).reverse
    exact Or.inr (Or.inr ⟨q,rest,middle,decomposition,localLabels,tail⟩)
end
end Lamping.AG
