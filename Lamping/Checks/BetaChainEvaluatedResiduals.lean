import Lamping.Lamping.BetaChainEvaluatedResiduals
import Lamping.Checks.FanSuccessfulReachable

namespace Lamping.Checks.BetaChainEvaluatedResidualsChecks
open AG Graph Lambda Lambda.Labelled
open FanSuccessfulChains
noncomputable abbrev site := FanSuccessfulReachable.concrete.site

/-- A real closed physical beta producer supplies the entire marked chain,
including its nonfirst APP and variable FUNCTION reads. Two different starts
share the exact four-edge list; equality here is honest same-list integration. -/
theorem actual_ordered_chain_evaluators
    (targetSelection : OccurrenceFragmentSelection current site.reduce (.inl ())) :
    ∃localTarget,History [[.fn]] (initLabels original.erase) localTarget ∧
      ∃edge : BetaEdge site.net,∃selection : SourceEdgeSelection (initLabels original.erase) site.net (.inl ()),
        SiteBetaGeometry site edge ∧
        ∃left : EvaluatedChainResiduals site (localTarget:=localTarget) edge selection targetSelection right_lambda_chain,
          ∃right : EvaluatedChainResiduals site (localTarget:=localTarget) edge selection targetSelection right_variable_chain,
            left.blocks site=right.blocks site ∧(left.blocks site).length=4 ∧
              ∀member,selection.evalLabel edge (left.node member).label≠[] := by
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
  obtain ⟨localTarget,labels,_erase,_targetMatches,edge,selection,geometry,all⟩ :=
    site.beta_evaluated_chain_residuals sourceClosed matching inputs flow rfl balance rfl transparency
      FanSuccessfulReachable.relative (by simp [FanSuccessfulReachable.endpoint,Marked.Normal])
      actualHistory targetSelection
  obtain ⟨left⟩ := all right_lambda_chain
  obtain ⟨right⟩ := all right_variable_chain
  have equal := left.blocks_eq_of_target_images site geometry right (by rfl)
  exact ⟨localTarget,labels,edge,selection,geometry,left,right,equal,
    by simp only [EvaluatedChainResiduals.blocks,List.length_map,List.length_attach];rfl,left.nonempty⟩

/-- The selector itself is inhabited by actual Matches, not supplied as an oracle. -/
theorem actual_nonempty_physical_supply :
    ∃targetSelection : OccurrenceFragmentSelection current site.reduce (.inl ()),
      ∃localTarget,History [[.fn]] (initLabels original.erase) localTarget ∧
        ∃edge : BetaEdge site.net,∃selection : SourceEdgeSelection (initLabels original.erase) site.net (.inl ()),
          SiteBetaGeometry site edge ∧
          ∃out : EvaluatedChainResiduals site (localTarget:=localTarget) edge selection targetSelection right_lambda_chain,
            (out.blocks site).length=4 := by
  obtain ⟨targetSelection⟩ := FanSuccessfulReachable.beta_matches.occurrence_fragment_selection targetClosed
  obtain ⟨localTarget,labels,edge,selection,geometry,out,_other,_eq,length,_nonempty⟩ :=
    actual_ordered_chain_evaluators targetSelection
  exact ⟨targetSelection,localTarget,labels,edge,selection,geometry,out,length⟩

#print axioms actual_ordered_chain_evaluators
#print axioms actual_nonempty_physical_supply
end Lamping.Checks.BetaChainEvaluatedResidualsChecks
