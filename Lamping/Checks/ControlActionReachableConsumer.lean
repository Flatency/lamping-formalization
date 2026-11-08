import Lamping.Lamping.ControlActionJointRepresentation
import Lamping.Checks.FunctionWrappedReachable
import Lamping.Checks.BraFunctionReachable

namespace Lamping.Checks.ControlActionReachableConsumer.Cro
open AG Graph Lambda Lambda.Labelled FunctionWrappedReachable

theorem actual_source_matches : Matches croCro.site.net (.inl ()) current.erase := by
  obtain ⟨_,_,_,_,matching⟩ := lambda_certified
  exact croCro.sourceIso.matches matching

theorem actual_target_matches : Matches croCro.site.reduce (.inl ()) current.erase := by
  obtain ⟨_,_,_,_,matching⟩ := cro_certified
  exact matching

theorem actual_three_step_trace : GraphTrace (ActualNet.initial term) (ActualNet.ofNet croCro.site.reduce)
    [.beta 0,.croAction .lam 0 1 (by decide),.croAction .cro 0 1 (by decide)] :=
  .cons concrete.graph_step (.cons croLambda.graph_step (.cons croCro.graph_step (.refl _)))

theorem actual_selections :
    Nonempty (OccurrenceFragmentSelection current croCro.site.net (.inl ())) ∧
    Nonempty (OccurrenceFragmentSelection current croCro.site.reduce (.inl ())) :=
  ⟨actual_source_matches.occurrence_fragment_selection WrappedSuccessfulChains.targetClosed,
    actual_target_matches.occurrence_fragment_selection WrappedSuccessfulChains.targetClosed⟩

/-- Every actual selector pair is transported; source Joint truth is not assumed. -/
theorem actual_joint_transport
    (source : OccurrenceFragmentSelection current croCro.site.net (.inl ()))
    (target : OccurrenceFragmentSelection current croCro.site.reduce (.inl ())) :
    JointRepresentation WrappedSuccessfulChains.targetClosed target ↔JointRepresentation WrappedSuccessfulChains.targetClosed source := by
  obtain ⟨flow,_,_,_,matching⟩ := lambda_certified
  obtain ⟨principal⟩ := croCro.site.actionPrincipal_exists
  exact croCro.site.control_action_joint_representation (.cro .cro 0 1 (by decide))
    (Or.inr (Or.inl rfl)) (croCro.sourceIso.flowBalance flow) (.inl ()) rfl WrappedSuccessfulChains.targetClosed
    (croCro.sourceIso.matches matching) actual_target_matches principal source target

theorem actual_nonempty_bundle :
    INIT original ∧Closed original.erase ∧History [[.fn]] original current ∧
    GraphTrace (ActualNet.initial term) (ActualNet.ofNet croCro.site.reduce)
      [.beta 0,.croAction .lam 0 1 (by decide),.croAction .cro 0 1 (by decide)] ∧
    Matches croCro.site.net (.inl ()) current.erase ∧
    Matches croCro.site.reduce (.inl ()) current.erase ∧
    PrerequisiteChain current WrappedSuccessfulChains.bodyApp WrappedSuccessfulChains.bodyEdges ∧
    Nonempty (OccurrenceFragmentSelection current croCro.site.net (.inl ())) ∧
    Nonempty (OccurrenceFragmentSelection current croCro.site.reduce (.inl ())) ∧
    ∀ (source : OccurrenceFragmentSelection current croCro.site.net (.inl ()))
      (target : OccurrenceFragmentSelection current croCro.site.reduce (.inl ())),
      JointRepresentation WrappedSuccessfulChains.targetClosed target ↔JointRepresentation WrappedSuccessfulChains.targetClosed source := by
  exact ⟨WrappedSuccessfulChains.initial,WrappedSuccessfulChains.sourceClosed,WrappedSuccessfulChains.actualHistory,actual_three_step_trace,
    actual_source_matches,actual_target_matches,WrappedSuccessfulChains.body_chain,
    actual_selections.1,actual_selections.2,actual_joint_transport⟩
#print axioms actual_three_step_trace
#print axioms actual_selections
#print axioms actual_joint_transport
#print axioms actual_nonempty_bundle
end Lamping.Checks.ControlActionReachableConsumer.Cro

namespace Lamping.Checks.ControlActionReachableConsumer.Bra
open AG Graph Lambda Lambda.Labelled BraFunctionReachable

theorem actual_source_matches : Matches braCro.site.net (.inl ()) current.erase := by
  obtain ⟨_,_,_,_,matching⟩ := lambda_certified
  exact braCro.sourceIso.matches matching

theorem actual_target_matches : Matches braCro.site.reduce (.inl ()) current.erase := by
  obtain ⟨_,_,_,_,matching⟩ := cro_certified
  exact matching

theorem actual_three_step_trace : GraphTrace (ActualNet.initial term) (ActualNet.ofNet braCro.site.reduce)
    [.beta 0,.braAction .lam 0 1 (by decide),.braAction .cro 0 1 (by decide)] :=
  .cons concrete.graph_step (.cons braLambda.graph_step (.cons braCro.graph_step (.refl _)))

theorem actual_selections :
    Nonempty (OccurrenceFragmentSelection current braCro.site.net (.inl ())) ∧
    Nonempty (OccurrenceFragmentSelection current braCro.site.reduce (.inl ())) :=
  ⟨actual_source_matches.occurrence_fragment_selection BraSuccessfulChains.targetClosed,
    actual_target_matches.occurrence_fragment_selection BraSuccessfulChains.targetClosed⟩

/-- Every actual selector pair is transported; source Joint truth is not assumed. -/
theorem actual_joint_transport
    (source : OccurrenceFragmentSelection current braCro.site.net (.inl ()))
    (target : OccurrenceFragmentSelection current braCro.site.reduce (.inl ())) :
    JointRepresentation BraSuccessfulChains.targetClosed target ↔JointRepresentation BraSuccessfulChains.targetClosed source := by
  obtain ⟨flow,_,_,_,matching⟩ := lambda_certified
  obtain ⟨principal⟩ := braCro.site.actionPrincipal_exists
  exact braCro.site.control_action_joint_representation (.bra .cro 0 1 (by decide))
    (Or.inr (Or.inl rfl)) (braCro.sourceIso.flowBalance flow) (.inl ()) rfl BraSuccessfulChains.targetClosed
    (braCro.sourceIso.matches matching) actual_target_matches principal source target

theorem actual_nonempty_bundle :
    INIT original ∧Closed original.erase ∧History [[]] original current ∧
    GraphTrace (ActualNet.initial term) (ActualNet.ofNet braCro.site.reduce)
      [.beta 0,.braAction .lam 0 1 (by decide),.braAction .cro 0 1 (by decide)] ∧
    Matches braCro.site.net (.inl ()) current.erase ∧
    Matches braCro.site.reduce (.inl ()) current.erase ∧
    PrerequisiteChain current BraSuccessfulChains.bodyApp BraSuccessfulChains.bodyEdges ∧
    Nonempty (OccurrenceFragmentSelection current braCro.site.net (.inl ())) ∧
    Nonempty (OccurrenceFragmentSelection current braCro.site.reduce (.inl ())) ∧
    ∀ (source : OccurrenceFragmentSelection current braCro.site.net (.inl ()))
      (target : OccurrenceFragmentSelection current braCro.site.reduce (.inl ())),
      JointRepresentation BraSuccessfulChains.targetClosed target ↔JointRepresentation BraSuccessfulChains.targetClosed source := by
  exact ⟨BraSuccessfulChains.initial,BraSuccessfulChains.sourceClosed,BraSuccessfulChains.actualHistory,actual_three_step_trace,
    actual_source_matches,actual_target_matches,BraSuccessfulChains.body_chain,
    actual_selections.1,actual_selections.2,actual_joint_transport⟩
#print axioms actual_three_step_trace
#print axioms actual_selections
#print axioms actual_joint_transport
#print axioms actual_nonempty_bundle
end Lamping.Checks.ControlActionReachableConsumer.Bra

#print axioms Lamping.AG.PathSite.control_action_access_kept
#print axioms Lamping.AG.PathSite.control_action_nonroot_occurrence_equality
#print axioms Lamping.AG.PathSite.control_action_occurrence_equality
#print axioms Lamping.AG.PathSite.control_action_chain_representation
#print axioms Lamping.AG.PathSite.control_action_chain_invariant
#print axioms Lamping.AG.PathSite.control_action_auxiliary_separation
#print axioms Lamping.AG.PathSite.control_action_joint_representation
