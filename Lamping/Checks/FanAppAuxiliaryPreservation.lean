import Lamping.Lamping.FanAppAuxiliaryPreservation
import Lamping.Checks.FanAppAuxiliaryArgumentReachable
set_option maxHeartbeats 4000000
namespace Lamping.Checks.FanAppAuxiliaryPreservationConsumer
open AG Graph Lambda Lambda.Labelled
open FanAppAuxiliaryArgumentReachable

private theorem certified_inputs {g : ActualNet (Boundary Base.term)} (certificate : Base.Certified g) :
    RootInputs g.net (.inl ()) := by
  obtain ⟨_,_,inputs,_,_⟩ := certificate
  exact inputs

theorem actual_source_inputs : RootInputs fanApp.site.net (.inl ()) :=
  fanApp.sourceIso.rootInputs (certified_inputs cro_certified)

/-- The carrier and both nonempty actual selector spaces are the already
verified original five-event construction, without reinitializing syntax. -/
theorem actual_nonempty_selections :
    Nonempty (OccurrenceFragmentSelection Syntax.current fanApp.site.net (.inl ())) ∧
    Nonempty (OccurrenceFragmentSelection Syntax.current fanApp.site.reduce (.inl ())) :=
  Domain.actual_selections_nonempty

private theorem natural_endpoint_with_internal_principal
    {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
    {kept : K→Label signature} {i j : Nat} {lt : i<j}
    (site : PathSite (.fanAction .app i j lt) kept (B:=B) (W:=W) (V:=V))
    {current : LTerm} {root : B} {boundary : B→Bool}
    (sourceMatches : Matches site.net root current.erase) (targetMatches : Matches site.reduce root current.erase)
    (flow : FlowBalance site.net boundary) (positive : boundary root=true)
    (inputs : RootInputs site.net root) (closed : Closed current.erase)
    (source : OccurrenceFragmentSelection current site.net root)
    (target : OccurrenceFragmentSelection current site.reduce root)
    (joint : JointRepresentation closed source) (left right : SyntaxIncidence.Edge current)
    (leftAux : AuxiliaryAt current left.val) (rightAux : AuxiliaryAt current right.val)
    (sameLabel : SyntaxIncidence.label current left=SyntaxIncidence.label current right)
    (sourceIso : SuccessfulEndpointIso current closed (SyntaxIncidence.source current left) (SyntaxIncidence.source current right))
    (targetIso : SuccessfulEndpointIso current closed (SyntaxIncidence.target current closed left) (SyntaxIncidence.target current closed right)) :
    (target left).fragment.segments=(target right).fragment.segments := by
  obtain ⟨principal⟩ := site.actionPrincipal_exists
  exact site.fan_app_auxiliary_endpoint_equality sourceMatches targetMatches flow positive inputs principal closed
    source target joint left right leftAux rightAux sameLabel sourceIso targetIso

/-- This real ARG-KC success-domain invocation has a conditional SOURCE IH.
The selfpair is not a proof of distinct-position REP or actual Joint truth. -/
theorem direct_natural_endpoint
    (source : OccurrenceFragmentSelection Syntax.current fanApp.site.net (.inl ()))
    (target : OccurrenceFragmentSelection Syntax.current fanApp.site.reduce (.inl ()))
    (sourceJoint : JointRepresentation Syntax.targetClosed source) (branch : Bool) :
    (target (Syntax.innerPosition branch)).fragment.segments=
      (target (Syntax.innerPosition branch)).fragment.segments := by
  exact natural_endpoint_with_internal_principal fanApp.site actual_source_matches actual_target_matches
    (fanApp.sourceIso.flowBalance Domain.fourthFlow) rfl actual_source_inputs Syntax.targetClosed
    source target sourceJoint (Syntax.innerPosition branch) (Syntax.innerPosition branch)
    (Syntax.auxiliary_argument branch) (Syntax.auxiliary_argument branch) rfl
    (Syntax.same_pair_successful_endpoint_isos branch).1 (Syntax.same_pair_successful_endpoint_isos branch).2

/-- Direct complete natural Aux-preservation call. No finish, role, Bool,
piece equality, or target invariant is supplied by this Check. -/
theorem direct_natural_auxiliary
    (source : OccurrenceFragmentSelection Syntax.current fanApp.site.net (.inl ()))
    (target : OccurrenceFragmentSelection Syntax.current fanApp.site.reduce (.inl ()))
    (sourceJoint : JointRepresentation Syntax.targetClosed source) :
    AuxiliarySeparation Syntax.targetClosed target := by
  obtain ⟨principal⟩ := fanApp.site.actionPrincipal_exists
  exact fanApp.site.fan_app_auxiliary_separation_preserve actual_source_matches actual_target_matches
    (fanApp.sourceIso.flowBalance Domain.fourthFlow) rfl actual_source_inputs principal Syntax.targetClosed
    source target sourceJoint

theorem actual_direct_supply
    (source : OccurrenceFragmentSelection Syntax.current fanApp.site.net (.inl ()))
    (target : OccurrenceFragmentSelection Syntax.current fanApp.site.reduce (.inl ()))
    (sourceJoint : JointRepresentation Syntax.targetClosed source) :
    AuxiliarySeparation Syntax.targetClosed target ∧
      ∀branch,(target (Syntax.innerPosition branch)).fragment.segments=
        (target (Syntax.innerPosition branch)).fragment.segments :=
  ⟨direct_natural_auxiliary source target sourceJoint,direct_natural_endpoint source target sourceJoint⟩

#print axioms actual_source_inputs
#print axioms actual_nonempty_selections
#print axioms direct_natural_endpoint
#print axioms direct_natural_auxiliary
#print axioms actual_direct_supply
#print axioms FanAppAuxiliaryArgumentReachable.actual_five_step_trace
#print axioms FanAppAuxiliaryArgumentReachable.actual_source_matches
#print axioms FanAppAuxiliaryArgumentReachable.actual_target_matches
#print axioms Syntax.actualHistory
#print axioms Syntax.initial
#print axioms Syntax.two_actual_successful_endpoints
#print axioms Domain.actual_selected_argument_domain
#print axioms Domain.actual_argument_kept_copied_cut
end Lamping.Checks.FanAppAuxiliaryPreservationConsumer
