import Lamping.Lamping.CancellationRepresentationTrace
import Lamping.Lamping.UnaryChainJointRepresentation
import Lamping.Lamping.FanControlJointRepresentation
import Lamping.Lamping.FanAppJointPreservation
import Lamping.Lamping.FanLambdaAuxiliaryPreservation
import Lamping.Lamping.ActionMatching
import Lamping.Lamping.GraphRootInputPreservation
set_option maxHeartbeats 4000000
namespace Lamping.AG
open Graph Lambda Lambda.Labelled
section
variable {s : Schema} {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K→Label signature}
variable (site : PathSite s kept (B:=B) (W:=W) (V:=V))
/-- Finite existing-rule dispatch only. No physical low or beta preservation. -/
private theorem PathSite.nonbeta_local_joint
    (notBeta : ∀i,s≠.beta i) {boundary : B→Bool}
    (flow : FlowBalance site.net boundary) (root : B) (positive : boundary root=true)
    (inputs : RootInputs site.net root) (oldT : Transparency site.net root)
    {current : LTerm} (closed : Closed current.erase)
    (sourceMatches : Matches site.net root current.erase)
    (targetMatches : Matches site.reduce root current.erase)
    (source : OccurrenceFragmentSelection current site.net root)
    (target : OccurrenceFragmentSelection current site.reduce root)
    (sourceJoint : JointRepresentation closed source) : JointRepresentation closed target := by
  obtain ⟨principal⟩ := site.actionPrincipal_exists
  cases s with
  | beta i => exact False.elim (notBeta i rfl)
  | fanCancel i => exact (site.cancellation_joint_representation (.fan i) flow root positive closed sourceMatches targetMatches source target).mpr sourceJoint
  | croCancel i => exact (site.cancellation_joint_representation (.cro i) flow root positive closed sourceMatches targetMatches source target).mpr sourceJoint
  | braCancel i => exact (site.cancellation_joint_representation (.bra i) flow root positive closed sourceMatches targetMatches source target).mpr sourceJoint
  | croAction f i j lt =>
    exact (site.unary_joint_representation (.cro f i j lt) (by intro bad;cases bad)
      flow root positive closed sourceMatches targetMatches principal source target).mpr sourceJoint
  | braAction f i j lt =>
    exact (site.unary_joint_representation (.bra f i j lt) (by intro bad;cases bad)
      flow root positive closed sourceMatches targetMatches principal source target).mpr sourceJoint
  | fanAction f i j lt =>
    cases f with
    | app => exact site.fan_app_joint_representation_preserve sourceMatches targetMatches flow positive inputs principal closed source target sourceJoint
    | lam => exact site.fan_lambda_joint_representation_preserve sourceMatches targetMatches flow positive oldT principal closed source target sourceJoint
    | fan => exact (site.fan_control_joint_representation (Or.inl rfl) flow root positive closed sourceMatches targetMatches principal source target).mpr sourceJoint
    | cro => exact (site.fan_control_joint_representation (Or.inr (Or.inl rfl)) flow root positive closed sourceMatches targetMatches principal source target).mpr sourceJoint
    | bra => exact (site.fan_control_joint_representation (Or.inr (Or.inr rfl)) flow root positive closed sourceMatches targetMatches principal source target).mpr sourceJoint
end
section
variable {B : Type} [FiniteNames B]
/-- The actual target match is derived from source P06 data, not an input. -/
private theorem GraphStep.nonbeta_matches
    {s : Schema} {g h : ActualNet B} (step : GraphStep s g h) (notBeta : ∀i,s≠.beta i)
    {boundary : B→Bool} {heights : B→Int} {root : B}
    (flow : FlowBalance g.net boundary) (positive : boundary root=true)
    (balance : IndexedLevelBalance g.net heights) (rootDepth : heights root=0)
    (inputs : RootInputs g.net root) (oldT : Transparency g.net root)
    {t : Term} (matching : Matches g.net root t) : Matches h.net root t := by
  cases s with
  | beta i => exact False.elim (notBeta i rfl)
  | fanCancel i => exact step.cancellation_matches_rootInputs (.fan i) flow positive inputs balance rootDepth oldT matching
  | croCancel i => exact step.cancellation_matches_rootInputs (.cro i) flow positive inputs balance rootDepth oldT matching
  | braCancel i => exact step.cancellation_matches_rootInputs (.bra i) flow positive inputs balance rootDepth oldT matching
  | fanAction f i j lt => exact step.action_matches_rootInputs (.fan f i j lt) flow positive balance rootDepth inputs oldT matching
  | croAction f i j lt => exact step.action_matches_rootInputs (.cro f i j lt) flow positive balance rootDepth inputs oldT matching
  | braAction f i j lt => exact step.action_matches_rootInputs (.bra f i j lt) flow positive balance rootDepth inputs oldT matching

/-- Actual nonbeta preservation uses BOTH boundary-fixing isomorphisms.
The only Joint premise is the honest SOURCE induction hypothesis. -/
theorem GraphStep.nonbeta_joint_representation_preserve
    {s : Schema} {g h : ActualNet B}
    (step : GraphStep s g h) (notBeta : ∀i,s≠.beta i)
    {boundary : B→Bool} {heights : B→Int}
    (flow : FlowBalance g.net boundary) (root : B) (positive : boundary root=true)
    (balance : IndexedLevelBalance g.net heights) (rootDepth : heights root=0)
    (inputs : RootInputs g.net root) (oldT : Transparency g.net root)
    {current : LTerm} (closed : Closed current.erase) (matching : Matches g.net root current.erase)
    (source : OccurrenceFragmentSelection current g.net root)
    (target : OccurrenceFragmentSelection current h.net root)
    (sourceJoint : JointRepresentation closed source) : JointRepresentation closed target := by
  have nextMatches := step.nonbeta_matches notBeta flow positive balance rootDepth inputs oldT matching
  cases step with
  | atSite kept site sourceIso targetIso =>
    have localSourceMatches := sourceIso.matches matching
    have localTargetMatches := targetIso.symm.matches nextMatches
    obtain ⟨localSource⟩ := localSourceMatches.occurrence_fragment_selection closed
    obtain ⟨localTarget⟩ := localTargetMatches.occurrence_fragment_selection closed
    have localJoint := (sourceIso.joint_representation matching closed source localSource).mpr sourceJoint
    have changed := site.nonbeta_local_joint notBeta (sourceIso.flowBalance flow) root positive
      (sourceIso.rootInputs inputs) (sourceIso.transparency oldT) closed localSourceMatches localTargetMatches
      localSource localTarget localJoint
    exact (targetIso.joint_representation localTargetMatches closed localTarget target).mpr changed

/-- All intermediate matching, flow, balance, inputs, T and Joint witnesses
are derived from the actual trace. Zero steps transport the real carrier iso. -/
theorem GraphTrace.nonbeta_joint_representation_preserve
    {g h : ActualNet B} {schemas : List Schema}
    (trace : GraphTrace g h schemas) (nonBetas : ∀s∈schemas,∀i,s≠.beta i)
    {boundary : B→Bool} {heights : B→Int}
    (flow : FlowBalance g.net boundary) (root : B) (positive : boundary root=true)
    (balance : IndexedLevelBalance g.net heights) (rootDepth : heights root=0)
    (inputs : RootInputs g.net root) (oldT : Transparency g.net root)
    {current : LTerm} (closed : Closed current.erase) (matching : Matches g.net root current.erase)
    (source : OccurrenceFragmentSelection current g.net root)
    (target : OccurrenceFragmentSelection current h.net root)
    (sourceJoint : JointRepresentation closed source) : JointRepresentation closed target := by
  induction trace with
  | iso same => exact (same.joint_representation matching closed source target).mpr sourceJoint
  | @cons g middle final s ss step tail ih =>
    have head := nonBetas s List.mem_cons_self
    have nextMatches := step.nonbeta_matches head flow positive balance rootDepth inputs oldT matching
    have nextInputs := step.rootInputs flow positive balance rootDepth inputs oldT matching
    have nextT := step.transparency_indexed flow positive balance rootDepth oldT
    obtain ⟨nextFlow⟩ := step.flowBalance flow
    obtain ⟨nextBalance⟩ := step.indexed_balance balance
    obtain ⟨middleSelection⟩ := nextMatches.occurrence_fragment_selection closed
    have nextJoint := step.nonbeta_joint_representation_preserve head flow root positive balance rootDepth
      inputs oldT closed matching source middleSelection sourceJoint
    exact ih (fun schema member=>nonBetas schema (List.mem_cons_of_mem _ member))
      nextFlow nextBalance nextInputs nextT nextMatches middleSelection target nextJoint
end
end Lamping.AG
#print axioms Lamping.AG.GraphStep.nonbeta_joint_representation_preserve
#print axioms Lamping.AG.GraphTrace.nonbeta_joint_representation_preserve
