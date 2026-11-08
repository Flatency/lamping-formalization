import Lamping.Lamping.DegreeReadSafetyProfiles
import Lamping.Checks.BetaChainEvaluatedResiduals
namespace Lamping.Checks.DegreeReadSafetyProfilesChecks
open Graph Lambda Lambda.Labelled AG FanSuccessfulChains BetaChainEvaluatedResidualsChecks

private theorem old : Marked.RelativeOldHistory [[.fn]] [[.fn]]
    (Marked.mark [[.fn]] original.erase) FanSuccessfulReachable.endpoint :=
  .cons (.appL (.redRoot _ _ _)) (by decide) (.nil _)
private theorem selected (name : Path) (inside : name∈([[.fn]] : List Path)) :
    original.degreeAt name=some (.atom 2) := by
  have same := List.mem_singleton.mp inside
  subst name;rfl

/-- All four genuine READ labels, including the actual atom5 second slot. -/
theorem actual_four_safety_values :
    (rightEdges.map (fun path=>degreeReadSafe (.atom 2) (current.labelAt path)))=
      [False,True,True,False] := by
  change [degreeReadSafe (.atom 2) (some rightLabel),
    degreeReadSafe (.atom 2) (some (.atom 5)),
    degreeReadSafe (.atom 2) (some (.atom 6)),
    degreeReadSafe (.atom 2) (some functionLabel)]=[False,True,True,False]
  simp [degreeReadSafe,rightLabel,functionLabel,Label.outerBarsSafe_concat,Label.atom,Label.under,Label.over,Label.OuterBarsSafe]

theorem actual_one_producer_safety_profiles
    (targetSelection : OccurrenceFragmentSelection current site.reduce (.inl ())) :
    ∃localTarget,∃_localHistory : History [[.fn]] (initLabels original.erase) localTarget,
      ∃edge : BetaEdge site.net,
      ∃selection : SourceEdgeSelection (initLabels original.erase) site.net (.inl ()),
      ∃_geometry : SiteBetaGeometry site edge,
      ∃_left : EvaluatedChainResiduals site (localTarget:=localTarget) edge selection targetSelection right_lambda_chain,
      ∃_right : EvaluatedChainResiduals site (localTarget:=localTarget) edge selection targetSelection right_variable_chain,
        (∀(ordinal : Nat) (lm : {p : Path //p∈rightEdges}) (rm : {p : Path //p∈rightEdges}),
          rightEdges[ordinal]?=some lm.val→rightEdges[ordinal]?=some rm.val→
          (degreeReadSafe (.atom 2) (current.labelAt lm.val) ↔
            degreeReadSafe (.atom 2) (current.labelAt rm.val))) ∧
        rightEdges.map (fun path=>degreeReadSafe (.atom 2) (current.labelAt path))=[False,True,True,False] := by
  have matching := FanSuccessfulReachable.concrete.sourceIso.matches
    (encode_closed_matches FanSuccessfulReachable.term FanSuccessfulReachable.closed 0)
  have inputs := FanSuccessfulReachable.concrete.sourceIso.rootInputs
    (encode_closed_independence FanSuccessfulReachable.term FanSuccessfulReachable.closed 0).rootInputs
  obtain ⟨originalFlow⟩ := encode_flowBalance FanSuccessfulReachable.term 0
  have flow := FanSuccessfulReachable.concrete.sourceIso.flowBalance originalFlow
  obtain ⟨originalBalance⟩ := encode_indexed_balance FanSuccessfulReachable.term 0
  have balance := FanSuccessfulReachable.concrete.sourceIso.indexed_balance originalBalance
  have transparency := FanSuccessfulReachable.concrete.sourceIso.transparency
    (encode_closed_transparency FanSuccessfulReachable.term FanSuccessfulReachable.closed 0)
  obtain ⟨localTarget,labels,_erase,_matching,edge,selection,geometry,all⟩ :=
    site.beta_evaluated_chain_residuals sourceClosed matching inputs flow rfl balance rfl transparency
      FanSuccessfulReachable.relative (by simp [FanSuccessfulReachable.endpoint,Marked.Normal])
      actualHistory targetSelection
  obtain ⟨left⟩ := all right_lambda_chain
  obtain ⟨right⟩ := all right_variable_chain
  have statuses := left.degree_read_safety_of_target_images site matching flow rfl
    FanSuccessfulReachable.relative (by simp [FanSuccessfulReachable.endpoint,Marked.Normal])
    old actualHistory selected (initial.outerBarsSafe _) labels geometry right (by rfl)
  exact ⟨localTarget,labels,edge,selection,geometry,left,right,statuses,actual_four_safety_values⟩

theorem actual_nonempty_supply :
    ∃targetSelection : OccurrenceFragmentSelection current site.reduce (.inl ()),
      ∃localTarget,∃_localHistory : History [[.fn]] (initLabels original.erase) localTarget,
      ∃edge : BetaEdge site.net,
      ∃selection : SourceEdgeSelection (initLabels original.erase) site.net (.inl ()),
      ∃_geometry : SiteBetaGeometry site edge,
      ∃_left : EvaluatedChainResiduals site (localTarget:=localTarget) edge selection targetSelection right_lambda_chain,
      ∃_right : EvaluatedChainResiduals site (localTarget:=localTarget) edge selection targetSelection right_variable_chain,
        (∀(ordinal : Nat) (lm : {p : Path //p∈rightEdges}) (rm : {p : Path //p∈rightEdges}),
          rightEdges[ordinal]?=some lm.val→rightEdges[ordinal]?=some rm.val→
          (degreeReadSafe (.atom 2) (current.labelAt lm.val) ↔
            degreeReadSafe (.atom 2) (current.labelAt rm.val))) ∧
        rightEdges.map (fun path=>degreeReadSafe (.atom 2) (current.labelAt path))=[False,True,True,False] := by
  obtain ⟨targetSelection⟩ := FanSuccessfulReachable.beta_matches.occurrence_fragment_selection targetClosed
  exact ⟨targetSelection,actual_one_producer_safety_profiles targetSelection⟩
#print axioms actual_four_safety_values
#print axioms actual_one_producer_safety_profiles
#print axioms actual_nonempty_supply
end Lamping.Checks.DegreeReadSafetyProfilesChecks


