import Lamping.Lamping.BetaPositiveTerminalChainReflection
import Lamping.Checks.TerminalPredecessorDirection
import Lamping.Lamping.InitialJointRepresentation
import Lamping.Lamping.JointRepresentationTransport

namespace Lamping.Checks.BetaPositiveTerminalChainReflectionChecks
open Graph Lambda Lambda.Labelled AG FanSuccessfulChains
open TerminalPredecessorDirectionChecks.Fan
noncomputable abbrev site := FanSuccessfulReachable.concrete.site

/-- The actual reachable Fan selfpair supplies every hypothesis internally:
initial SOURCE REP, beta corridor/history, true atom6 APP-FN read followed by
false marked binder FN, a positive terminal cut and a strictly smaller
identity singleton witness. It does not prove the general inverse witness. -/
theorem actual_fan_positive_terminal_reflection :
    1<max edges.length edges.length ∧
    cut.before.map current.labelAt=cut.before.map current.labelAt ∧
    ChainIncidenceIsomorphic (chainSyntaxIncidence current targetClosed edges)
      (chainSyntaxIncidence current targetClosed edges) ∧
    cut.before.length=1 ∧cut.after=[] ∧
    PrerequisiteReadsDirected current [.fn,.body,.fn] xVar true ∧
    PrerequisiteReadsDirected current [.fn] [.fn] false ∧
    degreeReadSafe degree (current.labelAt xVar) ∧
    ¬node.label.OuterBarsSafe (fun payload=>payload≠degree) := by
  have originalMatches := encode_closed_matches FanSuccessfulReachable.term FanSuccessfulReachable.closed 0
  have matching := FanSuccessfulReachable.concrete.sourceIso.matches originalMatches
  obtain ⟨sourceSelection⟩ := matching.occurrence_fragment_selection sourceClosed
  obtain ⟨originalSelection,initialJoint⟩ := encode_initial_joint_realization original sourceClosed initial 0
  have sourceJoint := (FanSuccessfulReachable.concrete.sourceIso.joint_representation
    originalMatches sourceClosed originalSelection sourceSelection).mpr initialJoint
  obtain ⟨targetSelection⟩ := FanSuccessfulReachable.beta_matches.occurrence_fragment_selection targetClosed
  have inputs := FanSuccessfulReachable.concrete.sourceIso.rootInputs
    (encode_closed_independence FanSuccessfulReachable.term FanSuccessfulReachable.closed 0).rootInputs
  obtain ⟨originalFlow⟩ := encode_flowBalance FanSuccessfulReachable.term 0
  have flow := FanSuccessfulReachable.concrete.sourceIso.flowBalance originalFlow
  obtain ⟨originalBalance⟩ := encode_indexed_balance FanSuccessfulReachable.term 0
  have balance := FanSuccessfulReachable.concrete.sourceIso.indexed_balance originalBalance
  have transparency := FanSuccessfulReachable.concrete.sourceIso.transparency
    (encode_closed_transparency FanSuccessfulReachable.term FanSuccessfulReachable.closed 0)
  have actual := site.beta_positive_terminal_chain_reflection sourceClosed matching inputs flow rfl
    balance rfl transparency FanSuccessfulReachable.relative
    (by simp [FanSuccessfulReachable.endpoint,Marked.Normal]) actualHistory old selected
    (initial.outerBarsSafe _) (.nil _) initial sourceSelection sourceJoint.1 targetSelection
    chain chain rfl cut cut rfl rfl (by decide) ⟨ChainIncidenceIso.refl _⟩
  exact ⟨actual.1,actual.2.1,actual.2.2,rfl,rfl,⟨Or.inl ⟨_,_,_,rfl,rfl⟩,rfl⟩,
    reading,beforeSafe _ (by simp),marked⟩

#print axioms actual_fan_positive_terminal_reflection
end Lamping.Checks.BetaPositiveTerminalChainReflectionChecks
