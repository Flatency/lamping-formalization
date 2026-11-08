import Lamping.Lamping.BetaUncreatedRootResiduals
import Lamping.Checks.DegreeFamily

namespace Lamping.Checks.BetaUncreatedRootResiduals
open AG Graph Lambda Lambda.Labelled
private abbrev term : Term := .lam (.app (.lam (.var 0)) (.var 0))
private abbrev initial := initLabels term
private abbrev result : LTerm := .lam (.atom 0)
  (LTerm.contract (.atom 1) (.atom 2) (.var (.atom 3) 0) (.var (.atom 4) 0))
private def turn : StepAt [.body] initial result := .body (.root _ _ _ _)
private def history : History [[.body]] initial result := .cons turn (.nil _)
private theorem closed : Closed term := by change (0<2) ∧ (0<1);decide
private def complete : ParallelStep [[.body]] initial.erase result.erase := by
  refine ⟨[[.body]],.lam (.var 0),(Marked.completeOld_iff _ _).mpr ⟨?_,True.intro⟩,rfl⟩
  exact .cons (.lam (.root _ _ _)) (.nil _)

theorem actual_nonroot_beta_root_fragment :
    ∃ presentation : PhysicalCorridorPresentation (encode 0 term).net (.beta 0)
      (.inr (.inl (.inl ()))) (.inr (.inr (.inl (.inl ())))) (.inl ()) (.inl ()),
      ∃ (sourceSelection : OccurrenceFragmentSelection initial presentation.site.net (.inl ()))
      (targetSelection : OccurrenceFragmentSelection result presentation.site.reduce (.inl ()))
      (edge : BetaEdge presentation.site.net),SiteBetaGeometry presentation.site edge ∧
      BetaPathResidual presentation.site edge
        ((targetSelection ⟨[],rfl⟩).fragment.segments.map (plugEnd _ _).invFun)
        (sourceSelection ⟨[],rfl⟩).fragment.segments := by
  obtain ⟨presentation,fiber,relative,matching⟩ :=
    DegreeFamily.P06CorridorPresentation.actual_nonroot_fiber_and_schedule_transport
  have inputs := presentation.sourceIso.rootInputs (encode_closed_independence term closed 0).rootInputs
  obtain ⟨originalFlow⟩ := encode_flowBalance term 0
  have flow := presentation.sourceIso.flowBalance originalFlow
  obtain ⟨originalBalance⟩ := encode_indexed_balance term 0
  have balance := presentation.sourceIso.indexed_balance originalBalance
  have transparency := presentation.sourceIso.transparency (encode_closed_transparency term closed 0)
  have selected (p : Path) (member : p∈([[.body]] : List Path)) :
      initial.degreeAt p=some (Labelled.Label.atom 2) := by
    have same := List.mem_singleton.mp member
    subst p;rfl
  have targetMatches := presentation.site.beta_complete_matches (init_is_INIT term) closed matching inputs flow rfl
    balance rfl transparency relative True.intro history
  obtain ⟨sourceSelection⟩ := matching.occurrence_fragment_selection closed (current:=initial)
  obtain ⟨targetSelection⟩ := targetMatches.occurrence_fragment_selection (history.closed closed)
  obtain ⟨edge,geometry,all⟩ := presentation.site.beta_uncreated_root_residuals (source:=initial) closed matching
    inputs flow rfl balance rfl transparency relative True.intro history complete.complete.1
      (DegreeAligned.initial initial [[.body]]) selected
  let child := targetSelection ⟨[],rfl⟩
  have safe : child.term.label.OuterBarsSafe (fun payload=>payload≠Labelled.Label.atom 2) := by
    have same : child.term=result := Option.some.inj child.occurrence.lookup.symm
    rw [same]
    trivial
  obtain ⟨oldPosition,_oldNode,_oldLookup,trace,residual⟩ := all child safe
  have known : BetaNodeHistoryPreimage history [] [] :=
    .one (step:=turn) rfl (.context (by rintro ⟨p,h⟩;cases h)) (.nil result [])
  have same := trace.unique known
  subst oldPosition
  exact ⟨presentation,sourceSelection,targetSelection,edge,geometry,
    residual (sourceSelection ⟨[],rfl⟩)⟩
#print axioms PathSite.beta_uncreated_root_residuals
#print axioms actual_nonroot_beta_root_fragment
end Lamping.Checks.BetaUncreatedRootResiduals
