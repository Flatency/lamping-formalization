import Lamping.Lamping.CoarseTrueWritingRoles
import Lamping.Checks.BetaChainEvaluatedResiduals
import Lamping.Checks.WritingLetterBlocks

namespace Lamping.Checks.CoarseTrueWritingRolesChecks
open AG Graph Lambda Lambda.Labelled
open FanSuccessfulChains BetaChainEvaluatedResidualsChecks

/-- ONE physical producer supplies both actual residuals. Starts differ;
the four literal member paths are the same, including nonfirst APP/FUNCTION. -/
theorem actual_four_slot_coarse_profiles
    (targetSelection : OccurrenceFragmentSelection current site.reduce (.inl ())) :
    ∃localTarget,History [[.fn]] (initLabels original.erase) localTarget ∧
      ∃edge : BetaEdge site.net,
        ∃selection : SourceEdgeSelection (initLabels original.erase) site.net (.inl ()),
          SiteBetaGeometry site edge ∧
          ∃left : EvaluatedChainResiduals site (localTarget:=localTarget) edge selection targetSelection right_lambda_chain,
            ∃right : EvaluatedChainResiduals site (localTarget:=localTarget) edge selection targetSelection right_variable_chain,
              rightEdges.attach.map (fun p=>(left.node p).label.letters.map coarseLetterTag)=
                rightEdges.attach.map (fun p=>(right.node p).label.letters.map coarseLetterTag) ∧
              (rightEdges.attach.map (fun p=>(left.node p).label.letters.map coarseLetterTag)).length=4 ∧
              (∃a fn arg,current.subterm rightEdges[1]=some (.app a fn arg)) ∧
              (∃a,current.subterm rightEdges[2]=some (.var a 0)) := by
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
  have profiles := left.coarse_true_role_profiles site matching flow rfl
    FanSuccessfulReachable.relative (by simp [FanSuccessfulReachable.endpoint,Marked.Normal])
    labels geometry right (by rfl)
  exact ⟨localTarget,labels,edge,selection,geometry,left,right,profiles,
    by simp only [List.length_map,List.length_attach];rfl,
    WritingLetterBlocksChecks.actual_nonfirst_APP_and_FUNCTION⟩

/-- The new direct call is inhabited by genuine target Matches. -/
theorem actual_nonempty_coarse_profiles :
    ∃targetSelection : OccurrenceFragmentSelection current site.reduce (.inl ()),
      ∃localTarget,History [[.fn]] (initLabels original.erase) localTarget ∧
        ∃edge : BetaEdge site.net,
          ∃selection : SourceEdgeSelection (initLabels original.erase) site.net (.inl ()),
            SiteBetaGeometry site edge ∧
            ∃left : EvaluatedChainResiduals site (localTarget:=localTarget) edge selection targetSelection right_lambda_chain,
              ∃right : EvaluatedChainResiduals site (localTarget:=localTarget) edge selection targetSelection right_variable_chain,
                rightEdges.attach.map (fun p=>(left.node p).label.letters.map coarseLetterTag)=
                  rightEdges.attach.map (fun p=>(right.node p).label.letters.map coarseLetterTag) ∧
                (rightEdges.attach.map (fun p=>(left.node p).label.letters.map coarseLetterTag)).length=4 := by
  obtain ⟨targetSelection⟩ := FanSuccessfulReachable.beta_matches.occurrence_fragment_selection targetClosed
  obtain ⟨localTarget,labels,edge,selection,geometry,left,right,eq,length,_slots⟩ :=
    actual_four_slot_coarse_profiles targetSelection
  exact ⟨targetSelection,localTarget,labels,edge,selection,geometry,left,right,eq,length⟩

#print axioms Lamping.AG.coarseLetterTag
#print axioms Lamping.AG.EvaluatedChainResiduals.coarse_true_role_profiles
#print axioms actual_four_slot_coarse_profiles
#print axioms actual_nonempty_coarse_profiles
end Lamping.Checks.CoarseTrueWritingRolesChecks
