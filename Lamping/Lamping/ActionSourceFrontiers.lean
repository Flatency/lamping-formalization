import Lamping.Lamping.SourceActionLocalExpansion
namespace Lamping.AG
open Graph
section
variable {s : Schema} {K B W V : Type}
variable [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K → Label signature} (site : PathSite s kept (B:=B) (W:=W) (V:=V))
local notation "cut" => cutFragment site.net (pathPartition s V) site.closed

private theorem principal_outside_impossible (side : Bool) (e : Endpoint cut) :
    site.internalEnd (.inl side)≠site.outsideEnd e := by
  intro same
  let split := fragmentEnd (B:=B) (W:=W) site.net.label (pathPartition s V)
  have mapped := congrArg split same
  change split (split.invFun (.inr (.inl side)))=split (split.invFun (.inl e)) at mapped
  simp only [split.right_inv] at mapped
  cases mapped

private theorem passive_principal_wire_not_outside (e : Endpoint cut) :
    site.net.wire (.inl ⟨.inr (.inr ()),.inl ()⟩)≠site.outsideEnd e := by
  intro same
  have reversed := congrArg site.net.wire.mate same
  rw [Pairing.involutive,site.outsideEnd_wire] at reversed
  exact principal_outside_impossible site true ((cut).wire e) reversed

private theorem any_passive_principal_cases
    {es : List (Endpoint site.net)} {a b : Context}
    (labels : Labelling site.net es a b) (typed : ∃ k,accessKind site.net es=some k)
    (first : es.head?=some (site.net.wire (.inl ⟨.inr (.inr ()),.inl ()⟩))) :
    (s.passive=.lam ∧es=[site.net.wire (.inl ⟨.inr (.inr ()),.inl ()⟩)] ∧a=b) ∨
    ∃ (q : Aux s.passive) (rest : List (Endpoint site.net)) (middle : Context),
      es=site.net.wire (.inl ⟨.inr (.inr ()),.inl ()⟩)::(.inl ⟨.inr (.inr ()),.inr q⟩)::rest ∧
      Traversal s.high (.op s.passive) (.inl ()) (.inr q) a middle ∧
      Labelling site.net ((.inl ⟨.inr (.inr ()),.inr q⟩)::rest) middle b := by
  by_cases proper : s.passive=.app ∨s.passive=.lam
  · exact site.typed_passive_principal_cases proper labels typed first
  · have control : s.passive=.fan ∨s.passive=.cro ∨s.passive=.bra := by
      cases same : s.passive <;> simp_all
    have nonterminal : portKind (.op s.passive) (.inl ())=none := by
      rcases control with same|same|same <;> rw [same] <;> rfl
    obtain ⟨port,rest,middle,split,rule,tail⟩ := labels.typed_nonterminal_departure typed
      (site.net.wire (.inl ⟨.inr (.inr ()),.inl ()⟩)) first (.inr (.inr ())) (.inl ())
      (site.net.wire.involutive _) nonterminal
    cases port with
    | inl u => cases u; exact False.elim (rule.distinct rfl)
    | inr q => exact Or.inr ⟨q,rest,middle,split,rule,tail⟩

/-- For an actual outside-ended typed old path the principal-internal lambda
terminal is physically impossible. Thus an active-auxiliary entry already
contains one complete source crossing, with its genuine labelled tail. -/
theorem PathSite.typed_active_complete_source
    (control : s.active=.fan ∨s.active=.cro ∨s.active=.bra)
    (principal : SiteActionPrincipal site) (p : Aux s.active)
    {es : List (Endpoint site.net)} {a b : Context}
    (labels : Labelling site.net es a b) (typed : ∃ k,accessKind site.net es=some k)
    (first : es.head?=some (site.net.wire (.inl ⟨.inr (.inl ()),.inr p⟩)))
    (last : Endpoint cut) (finish : es.getLast?=some (site.outsideEnd last)) :
    ∃ (q : Aux s.passive) (rest : List (Endpoint site.net)) (middle : Context),
      es=principal.crossing site p q++rest ∧
      SourceActionRoute site principal (.inl p) (.inr q) (principal.crossing site p q) ∧
      Labelling site.net (principal.crossing site p q) a middle ∧
      Labelling site.net ((.inl ⟨.inr (.inr ()),.inr q⟩)::rest) middle b := by
  obtain ⟨suffix,seam,split,suffixHead,active,remaining,suffixTyped⟩ :=
    site.typed_action_active_prefix control principal p labels typed first
  obtain ⟨routePre,routeEnd⟩ := List.getLast?_eq_some_iff.mp principal.last
  have rebuild : principal.edges.dropLast++[site.net.wire (.inl ⟨.inr (.inr ()),.inl ()⟩)]=principal.edges := by
    rw [routeEnd,List.dropLast_concat]
  rcases any_passive_principal_cases site remaining suffixTyped suffixHead with
    ⟨_,terminal,_⟩|⟨q,rest,middle,tailSplit,passive,tail⟩
  · rw [terminal,rebuild] at split
    have terminalEnd : es.getLast?=some (site.net.wire (.inl ⟨.inr (.inr ()),.inl ()⟩)) := by
      rw [split]
      simp only [routeEnd,List.getLast?_append,List.getLast?_cons,List.getLast?_nil,Option.getD_none,Option.getD_some,Option.some_or]
    exact False.elim (passive_principal_wire_not_outside site last (Option.some.inj (terminalEnd.symm.trans finish)))
  · have decomposition : es=principal.crossing site p q++rest := by
      rw [tailSplit] at split
      change es=(site.net.wire (.inl ⟨.inr (.inl ()),.inr p⟩)::
        (principal.edges++[.inl ⟨.inr (.inr ()),.inr q⟩]))++rest
      simp only [List.cons_append,List.append_assoc]
      rw [←rebuild]
      simpa only [List.append_assoc,List.singleton_append] using split
    have crossingLabels : Labelling site.net (principal.crossing site p q) a middle :=
      (principal.crossing_labels_iff site p q a middle).mpr
        ((leftRoute_labeling_iff s.active s.passive s.low s.high p q a middle).mpr ⟨seam,active,passive⟩)
    exact ⟨q,rest,middle,decomposition,.cross p q,crossingLabels,tail⟩
theorem SourceActionRoute.length_ge_two {principal : SiteActionPrincipal site} {entry exit front}
    (route : SourceActionRoute site principal entry exit front) : 2≤front.length := by
  cases route with
  | cross p q => simp [SiteActionPrincipal.crossing,List.length_append]
  | backward p q => simp [reverseEdges,SiteActionPrincipal.crossing,List.length_append]
  | passive p q => exact Nat.le_refl 2

/-- Every actual next turn at a frontier of a typed outside-ended path belongs
to one finite canonical source block. Its exit is a real overlap segment,
with at least two block segments, giving strict descent for whole-path recursion.
The no-next-turn singleton case is deliberately excluded by length, not completed. -/
theorem PathSite.typed_frontier_source_route
    (control : s.active=.fan ∨s.active=.cro ∨s.active=.bra)
    (principal : SiteActionPrincipal site) (entry : s.Frontier)
    {es : List (Endpoint site.net)} {a b : Context}
    (labels : Labelling site.net es a b) (typed : ∃ k,accessKind site.net es=some k)
    (first : es.head?=some (site.net.wire (site.outsideEnd (.inr (.inl (.inr entry))))))
    (last : Endpoint cut) (finish : es.getLast?=some (site.outsideEnd last))
    (next : 1<es.length) :
    ∃ (exit : s.Frontier) (front rest : List (Endpoint site.net)) (middle : Context),
      es=front++rest ∧SourceActionRoute site principal entry exit front ∧
      front.getLast?=some (site.outsideEnd (.inr (.inl (.inr exit)))) ∧
      Labelling site.net front a middle ∧
      Labelling site.net ((site.outsideEnd (.inr (.inl (.inr exit))))::rest) middle b := by
  cases entry with
  | inl p =>
    obtain ⟨q,rest,middle,split,route,frontLabels,tail⟩ :=
      site.typed_active_complete_source control principal p labels typed first last finish
    refine ⟨.inr q,_,rest,middle,split,route,?_,frontLabels,tail⟩
    simp only [SiteActionPrincipal.crossing,List.getLast?_cons,List.getLast?_append,
      List.getLast?_cons,List.getLast?_nil,Option.getD_none,Option.some_or,Option.getD_some]
    rfl
  | inr p =>
    rcases site.typed_passive_canonical_cases control principal p labels typed first with
      ⟨terminal,_,_⟩|⟨q,rest,middle,split,frontLabels,tail⟩|⟨q,rest,middle,split,frontLabels,tail⟩
    · rw [terminal] at next
      exact False.elim (Nat.lt_irrefl 1 next)
    · exact ⟨.inr q,_,rest,middle,split,.passive p q,rfl,frontLabels,tail⟩
    · refine ⟨.inl q,_,rest,middle,split,.backward q p,?_,frontLabels,tail⟩
      simp only [reverseEdges,List.getLast?_map,List.getLast?_reverse,SiteActionPrincipal.crossing,
        List.head?_cons,Option.map_some,Pairing.involutive]
      rfl
end
end Lamping.AG



