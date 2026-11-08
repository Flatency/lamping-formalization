import Lamping.Lamping.NonBetaJointRepresentation
import Lamping.Checks.FanAppSuccessfulReachable
set_option maxHeartbeats 4000000
namespace Lamping.Checks.NonBetaJointRepresentationConsumer
open AG Graph Lambda Lambda.Labelled FanSuccessfulReachable
open FanSuccessfulChains hiding current original

noncomputable abbrev start := ActualNet.ofNet concrete.site.reduce
noncomputable abbrev lastStart := ActualNet.ofNet fanCro.site.reduce
noncomputable abbrev finish := ActualNet.ofNet FanAppSuccessfulReachable.fanApp.site.reduce
abbrev schemas : List Schema := [.fanAction .lam 0 1 (by decide),
  .fanAction .cro 0 1 (by decide),.fanAction .app 0 1 (by decide)]

/-- Only the actual nonbeta suffix; the original beta event is separate. -/
theorem actual_suffix : GraphTrace start finish schemas :=
  .cons actualFanPresentation.graph_step (.cons fanCro.graph_step
    (.cons FanAppSuccessfulReachable.fanApp.graph_step (.refl _)))

theorem actual_suffix_nonbeta : ∀s∈schemas,∀i,s≠.beta i := by
  intro s member i wrong
  simp only [schemas,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl|rfl|rfl <;> cases wrong

/-- SAME original INIT/history and genuine beta prefix, with no beta Joint claim. -/
theorem actual_prefix_and_suffix :
    INIT original ∧Closed original.erase ∧History [[.fn]] original current ∧
      GraphStep (.beta 0) (ActualNet.initial term) start ∧GraphTrace start finish schemas :=
  ⟨FanSuccessfulChains.initial,sourceClosed,actualHistory,concrete.graph_step,actual_suffix⟩

theorem actual_nonempty_selections :
    Nonempty (OccurrenceFragmentSelection current start.net (.inl ())) ∧
      Nonempty (OccurrenceFragmentSelection current finish.net (.inl ())) := by
  obtain ⟨_,_,_,_,matching⟩ := beta_certified
  exact ⟨matching.occurrence_fragment_selection targetClosed,
    FanAppSuccessfulReachable.actual_target_matches.occurrence_fragment_selection targetClosed⟩

/-- Direct NEW trace top, with all real source P06 supply and an honest IH. -/
theorem direct_suffix_joint
    (source : OccurrenceFragmentSelection current start.net (.inl ()))
    (target : OccurrenceFragmentSelection current finish.net (.inl ()))
    (sourceJoint : JointRepresentation targetClosed source) : JointRepresentation targetClosed target := by
  obtain ⟨flow,balance,inputs,oldT,matching⟩ := beta_certified
  exact actual_suffix.nonbeta_joint_representation_preserve actual_suffix_nonbeta flow (.inl ()) rfl
    balance rfl inputs oldT targetClosed matching source target sourceJoint

/-- Direct NEW actual step wrapper on the final fanAPP event, not its PathSite. -/
theorem direct_last_step_joint
    (source : OccurrenceFragmentSelection current lastStart.net (.inl ()))
    (target : OccurrenceFragmentSelection current finish.net (.inl ()))
    (sourceJoint : JointRepresentation targetClosed source) : JointRepresentation targetClosed target := by
  obtain ⟨flow,balance,inputs,oldT,matching⟩ := cro_certified
  exact FanAppSuccessfulReachable.fanApp.graph_step.nonbeta_joint_representation_preserve
    (by intro i wrong;cases wrong) flow (.inl ()) rfl balance rfl inputs oldT
    targetClosed matching source target sourceJoint

/-- Four independent legal selectors: transport the starting IH explicitly,
call the NEW suffix top on each consistent pair, then compare target properties. -/
theorem direct_four_choices
    (sourceFirst sourceSecond : OccurrenceFragmentSelection current start.net (.inl ()))
    (targetFirst targetSecond : OccurrenceFragmentSelection current finish.net (.inl ()))
    (sourceJoint : JointRepresentation targetClosed sourceFirst) :
    JointRepresentation targetClosed targetFirst ∧JointRepresentation targetClosed targetSecond ∧
      (JointRepresentation targetClosed targetFirst ↔JointRepresentation targetClosed targetSecond) := by
  obtain ⟨_,_,_,_,matching⟩ := beta_certified
  have secondJoint := (JointRepresentation.choice_independent matching targetClosed sourceFirst sourceSecond).mp sourceJoint
  exact ⟨direct_suffix_joint sourceFirst targetFirst sourceJoint,
    direct_suffix_joint sourceSecond targetSecond secondJoint,
    JointRepresentation.choice_independent FanAppSuccessfulReachable.actual_target_matches targetClosed targetFirst targetSecond⟩

/-- The zero-schema branch also calls NEW trace preservation for a genuine
boundary-fixing iso; no assumption that the carriers are definitionally equal. -/
theorem direct_iso_renaming {h : ActualNet (Boundary term)} (iso : NetIso start.net h.net)
    (source : OccurrenceFragmentSelection current start.net (.inl ()))
    (target : OccurrenceFragmentSelection current h.net (.inl ()))
    (sourceJoint : JointRepresentation targetClosed source) : JointRepresentation targetClosed target := by
  obtain ⟨flow,balance,inputs,oldT,matching⟩ := beta_certified
  have trace : GraphTrace start h [] := .iso iso
  exact trace.nonbeta_joint_representation_preserve (by intro s member;cases member)
    flow (.inl ()) rfl balance rfl inputs oldT targetClosed matching source target sourceJoint

#print axioms actual_suffix
#print axioms actual_suffix_nonbeta
#print axioms actual_prefix_and_suffix
#print axioms actual_nonempty_selections
#print axioms direct_suffix_joint
#print axioms direct_last_step_joint
#print axioms direct_four_choices
#print axioms direct_iso_renaming
#print axioms FanAppSuccessfulReachable.actual_four_step_trace
#print axioms FanSuccessfulReachable.beta_certified
#print axioms FanSuccessfulReachable.cro_certified
#print axioms FanAppSuccessfulReachable.actual_target_matches
end Lamping.Checks.NonBetaJointRepresentationConsumer
