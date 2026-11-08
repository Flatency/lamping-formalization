import Lamping.Lamping.ActionSourcePrefixes
namespace Lamping.AG
open Graph
private theorem principal_kind (op : Op) (proper : op=.app ∨op=.lam)
    {kind : AccessKind} (observed : portKind (.op op) (.inl ())=some kind) : op=.lam := by
  rcases proper with same|same
  · subst op; cases observed
  · exact same
section
variable {s : Schema} {K B W V : Type}
variable [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K → Label signature} (site : PathSite s kept (B:=B) (W:=W) (V:=V))

/-- An existing typed suffix at the passive principal either stops at its
lambda context, or already contains its actual next auxiliary departure.
Singletons and the original intermediate/output labels are retained. -/
theorem PathSite.typed_passive_principal_cases
    (proper : s.passive=.app ∨s.passive=.lam)
    {es : List (Endpoint site.net)} {a b : Context}
    (labels : Labelling site.net es a b) (typed : ∃ k,accessKind site.net es=some k)
    (first : es.head?=some (site.net.wire (.inl ⟨.inr (.inr ()),.inl ()⟩))) :
    (s.passive=.lam ∧es=[site.net.wire (.inl ⟨.inr (.inr ()),.inl ()⟩)] ∧a=b) ∨
    ∃ (q : Aux s.passive) (rest : List (Endpoint site.net)) (middle : Context),
      es=site.net.wire (.inl ⟨.inr (.inr ()),.inl ()⟩)::(.inl ⟨.inr (.inr ()),.inr q⟩)::rest ∧
      Traversal s.high (.op s.passive) (.inl ()) (.inr q) a middle ∧
      Labelling site.net ((.inl ⟨.inr (.inr ()),.inr q⟩)::rest) middle b := by
  obtain ⟨rest,split⟩ := List.head?_eq_some_iff.mp first
  subst es
  cases rest with
  | nil =>
    cases labels
    obtain ⟨kind,observed⟩ := typed
    simp only [accessKind,List.getLast?_cons,List.getLast?_nil,Option.getD_none,Option.bind_some] at observed
    rw [Pairing.involutive] at observed
    exact Or.inl ⟨principal_kind s.passive proper observed,rfl,rfl⟩
  | cons e rest =>
    cases labels with
    | cons turn tail =>
      rw [Pairing.involutive] at turn
      obtain ⟨port,same,rule⟩ := turn.from_node (.inr (.inr ())) (.inl ()) rfl
      subst e
      cases port with
      | inl u => cases u; exact False.elim (rule.distinct rfl)
      | inr q => exact Or.inr ⟨q,rest,_,rfl,rule,tail⟩

/-- Whole finite old crossing or a genuine typed terminal at the matched
lambda context. The complete branch is the selected physical principal route,
including every W subdivision and its real two primitive traversals. -/
theorem PathSite.typed_action_crossing_cases
    (control : s.active=.fan ∨s.active=.cro ∨s.active=.bra)
    (proper : s.passive=.app ∨s.passive=.lam)
    (principal : SiteActionPrincipal site) (p : Aux s.active)
    {es : List (Endpoint site.net)} {a b : Context}
    (labels : Labelling site.net es a b) (typed : ∃ k,accessKind site.net es=some k)
    (first : es.head?=some (site.net.wire (.inl ⟨.inr (.inl ()),.inr p⟩))) :
    (s.passive=.lam ∧es=site.net.wire (.inl ⟨.inr (.inl ()),.inr p⟩)::principal.edges ∧
      Traversal s.low (.op s.active) (.inr p) (.inl ()) a b) ∨
    ∃ (q : Aux s.passive) (rest : List (Endpoint site.net)) (middle : Context),
      es=principal.crossing site p q++rest ∧
      Labelling site.net (principal.crossing site p q) a middle ∧
      Labelling site.net ((.inl ⟨.inr (.inr ()),.inr q⟩)::rest) middle b := by
  obtain ⟨suffix,seam,split,suffixHead,active,remaining,suffixTyped⟩ :=
    site.typed_action_active_prefix control principal p labels typed first
  obtain ⟨routePre,routeEnd⟩ := List.getLast?_eq_some_iff.mp principal.last
  have rebuild : principal.edges.dropLast++[site.net.wire (.inl ⟨.inr (.inr ()),.inl ()⟩)]=principal.edges := by
    rw [routeEnd,List.dropLast_concat]
  rcases site.typed_passive_principal_cases proper remaining suffixTyped suffixHead with
    ⟨isLam,terminal,same⟩|⟨q,rest,middle,tailSplit,passive,tail⟩
  · subst b
    rw [terminal,rebuild] at split
    exact Or.inl ⟨isLam,split,active⟩
  · have decomposition : es=principal.crossing site p q++rest := by
      rw [tailSplit] at split
      have normalized : principal.edges.dropLast++site.net.wire (.inl ⟨.inr (.inr ()),.inl ()⟩)::
          (.inl ⟨.inr (.inr ()),.inr q⟩)::rest =
          principal.edges++(.inl ⟨.inr (.inr ()),.inr q⟩)::rest := by
        calc
          _=(principal.edges.dropLast++[site.net.wire (.inl ⟨.inr (.inr ()),.inl ()⟩)])++
              (.inl ⟨.inr (.inr ()),.inr q⟩)::rest := by simp only [List.append_assoc,List.singleton_append]
          _=_ := by rw [rebuild]
      simpa only [SiteActionPrincipal.crossing,List.cons_append,List.append_assoc,List.singleton_append,normalized] using split
    have crossingLabels : Labelling site.net (principal.crossing site p q) a middle :=
      (principal.crossing_labels_iff site p q a middle).mpr
        ((leftRoute_labeling_iff s.active s.passive s.low s.high p q a middle).mpr ⟨seam,active,passive⟩)
    exact Or.inr ⟨q,rest,middle,decomposition,crossingLabels,tail⟩
end
end Lamping.AG

