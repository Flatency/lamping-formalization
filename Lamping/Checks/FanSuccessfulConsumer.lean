import Lamping.Checks.FanSuccessfulReachable
import Lamping.Lamping.FanControlJointRepresentation
namespace Lamping.Checks.FanSuccessfulConsumer
open AG Graph Lambda Lambda.Labelled FanSuccessfulReachable
open FanSuccessfulChains hiding current original

/-- Every compared occurrence is supplied by the actual matches on this trace. -/
theorem actual_selections :
    Nonempty (OccurrenceFragmentSelection current fanCro.site.net (.inl ())) ∧
    Nonempty (OccurrenceFragmentSelection current fanCro.site.reduce (.inl ())) :=
  ⟨actual_source_matches.occurrence_fragment_selection targetClosed,
    actual_final_matches.occurrence_fragment_selection targetClosed⟩

theorem actual_nonroot_pair {p q : Path} (hp : p≠[]) (hq : q≠[])
    (sourceLeft : OccurrenceFragment current fanCro.site.net (.inl ()) p)
    (targetLeft : OccurrenceFragment current fanCro.site.reduce (.inl ()) p)
    (sourceRight : OccurrenceFragment current fanCro.site.net (.inl ()) q)
    (targetRight : OccurrenceFragment current fanCro.site.reduce (.inl ()) q) :
    targetLeft.fragment.segments=targetRight.fragment.segments ↔
      sourceLeft.fragment.segments=sourceRight.fragment.segments := by
  obtain ⟨flow,_,_,_,_⟩ := lambda_certified
  obtain ⟨principal⟩ := fanCro.site.actionPrincipal_exists
  exact fanCro.site.fan_control_nonroot_occurrence_equality (Or.inr (Or.inl rfl))
    (fanCro.sourceIso.flowBalance flow) (.inl ()) rfl actual_source_matches actual_final_matches
    principal hp hq sourceLeft targetLeft sourceRight targetRight

theorem actual_body_pair
    (sourceLeft : OccurrenceFragment current fanCro.site.net (.inl ()) leftBody)
    (targetLeft : OccurrenceFragment current fanCro.site.reduce (.inl ()) leftBody)
    (sourceRight : OccurrenceFragment current fanCro.site.net (.inl ()) rightBody)
    (targetRight : OccurrenceFragment current fanCro.site.reduce (.inl ()) rightBody) :
    targetLeft.fragment.segments=targetRight.fragment.segments ↔
      sourceLeft.fragment.segments=sourceRight.fragment.segments :=
  actual_nonroot_pair (by decide) (by decide) sourceLeft targetLeft sourceRight targetRight

theorem actual_function_variable_pair
    (sourceLeft : OccurrenceFragment current fanCro.site.net (.inl ()) leftVar)
    (targetLeft : OccurrenceFragment current fanCro.site.reduce (.inl ()) leftVar)
    (sourceRight : OccurrenceFragment current fanCro.site.net (.inl ()) rightVar)
    (targetRight : OccurrenceFragment current fanCro.site.reduce (.inl ()) rightVar) :
    targetLeft.fragment.segments=targetRight.fragment.segments ↔
      sourceLeft.fragment.segments=sourceRight.fragment.segments :=
  actual_nonroot_pair (by decide) (by decide) sourceLeft targetLeft sourceRight targetRight

theorem actual_distinct_successful_occurrences :
    leftBody≠rightBody ∧leftVar≠rightVar ∧
    PrerequisiteChain current leftBody leftBodyEdges ∧
    PrerequisiteChain current rightBody rightBodyEdges ∧
    PrerequisiteChain current leftVar leftEdges ∧
    PrerequisiteChain current rightVar rightEdges :=
  ⟨by decide,by decide,left_body_chain,right_body_chain,left_variable_chain,right_variable_chain⟩

/-- The same INIT, labelled history and actual three-rule trace provide both
semantic graphs and arbitrary fragment choices at two different body/FUNCTION
positions. No source Joint or AuxiliarySeparation is assumed. -/
theorem actual_reachable_successful_fan_comparison :
    INIT original ∧Closed original.erase ∧History [[.fn]] original current ∧
    GraphTrace (ActualNet.initial term) (ActualNet.ofNet fanCro.site.reduce)
      [.beta 0,.fanAction .lam 0 1 (by decide),.fanAction .cro 0 1 (by decide)] ∧
    Matches fanCro.site.net (.inl ()) current.erase ∧
    Matches fanCro.site.reduce (.inl ()) current.erase ∧
    Nonempty (OccurrenceFragmentSelection current fanCro.site.net (.inl ())) ∧
    Nonempty (OccurrenceFragmentSelection current fanCro.site.reduce (.inl ())) ∧
    PrerequisiteChain current leftBody leftBodyEdges ∧
    PrerequisiteChain current rightBody rightBodyEdges ∧
    PrerequisiteChain current leftVar leftEdges ∧
    PrerequisiteChain current rightVar rightEdges ∧
    (∀ (sourceLeft : OccurrenceFragment current fanCro.site.net (.inl ()) leftBody)
       (targetLeft : OccurrenceFragment current fanCro.site.reduce (.inl ()) leftBody)
       (sourceRight : OccurrenceFragment current fanCro.site.net (.inl ()) rightBody)
       (targetRight : OccurrenceFragment current fanCro.site.reduce (.inl ()) rightBody),
       targetLeft.fragment.segments=targetRight.fragment.segments ↔
       sourceLeft.fragment.segments=sourceRight.fragment.segments) ∧
    (∀ (sourceLeft : OccurrenceFragment current fanCro.site.net (.inl ()) leftVar)
       (targetLeft : OccurrenceFragment current fanCro.site.reduce (.inl ()) leftVar)
       (sourceRight : OccurrenceFragment current fanCro.site.net (.inl ()) rightVar)
       (targetRight : OccurrenceFragment current fanCro.site.reduce (.inl ()) rightVar),
       targetLeft.fragment.segments=targetRight.fragment.segments ↔
       sourceLeft.fragment.segments=sourceRight.fragment.segments) := by
  obtain ⟨sourceExists,targetExists⟩ := actual_selections
  exact ⟨initial,sourceClosed,actualHistory,actual_three_step_trace,actual_source_matches,
    actual_final_matches,sourceExists,targetExists,left_body_chain,right_body_chain,
    left_variable_chain,right_variable_chain,actual_body_pair,actual_function_variable_pair⟩
#print axioms actual_nonroot_pair
#print axioms actual_distinct_successful_occurrences
#print axioms actual_reachable_successful_fan_comparison

/-- The two different successful body chains are transported using actual
selection data, not a premise asserting source REP. -/
theorem actual_successful_chain_transport
    (source : OccurrenceFragmentSelection current fanCro.site.net (.inl ()))
    (target : OccurrenceFragmentSelection current fanCro.site.reduce (.inl ())) :
    SameChainRepresentation target left_body_chain right_body_chain ↔
      SameChainRepresentation source left_body_chain right_body_chain := by
  obtain ⟨flow,_,_,_,_⟩ := lambda_certified
  obtain ⟨principal⟩ := fanCro.site.actionPrincipal_exists
  exact fanCro.site.fan_control_chain_representation (Or.inr (Or.inl rfl))
    (fanCro.sourceIso.flowBalance flow) (.inl ()) rfl actual_source_matches actual_final_matches
    principal source target left_body_chain right_body_chain

/-- A control-fan local iff does not assert that either Aux/Joint proposition
holds, and is not a fan-lambda preservation theorem. -/
theorem actual_joint_transport
    (source : OccurrenceFragmentSelection current fanCro.site.net (.inl ()))
    (target : OccurrenceFragmentSelection current fanCro.site.reduce (.inl ())) :
    JointRepresentation targetClosed target ↔JointRepresentation targetClosed source := by
  obtain ⟨flow,_,_,_,_⟩ := lambda_certified
  obtain ⟨principal⟩ := fanCro.site.actionPrincipal_exists
  exact fanCro.site.fan_control_joint_representation (Or.inr (Or.inl rfl))
    (fanCro.sourceIso.flowBalance flow) (.inl ()) rfl targetClosed
    actual_source_matches actual_final_matches principal source target

theorem actual_selected_transports :
    ∃ (source : OccurrenceFragmentSelection current fanCro.site.net (.inl ()))
      (target : OccurrenceFragmentSelection current fanCro.site.reduce (.inl ())),
      (SameChainRepresentation target left_body_chain right_body_chain ↔
        SameChainRepresentation source left_body_chain right_body_chain) ∧
      (JointRepresentation targetClosed target ↔JointRepresentation targetClosed source) := by
  obtain ⟨⟨source⟩,⟨target⟩⟩ := actual_selections
  exact ⟨source,target,actual_successful_chain_transport source target,actual_joint_transport source target⟩
#print axioms actual_successful_chain_transport
#print axioms actual_joint_transport
#print axioms actual_selected_transports
#print axioms successful_chain_representation_transport
#print axioms PathSite.fan_control_nonroot_occurrence_equality
#print axioms PathSite.fan_control_occurrence_equality
#print axioms PathSite.fan_control_chain_representation
#print axioms PathSite.fan_control_joint_representation
#print axioms PathSite.fan_control_access_kept
#print axioms OccurrenceFragment.head_root_iff
#print axioms OccurrenceFragment.ne_of_root_nonroot
#print axioms successful_chain_invariant_transport
#print axioms PathSite.fan_control_chain_invariant
#print axioms PathSite.fan_control_auxiliary_separation
end Lamping.Checks.FanSuccessfulConsumer
