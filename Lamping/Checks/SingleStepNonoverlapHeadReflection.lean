import Lamping.Lamping.SingleStepNonoverlapHeadReflection
import Lamping.Checks.FanSuccessfulReachable
import Lamping.Checks.FanBodyBindingIdentityReachable
import Lamping.Lamping.InitialJointRepresentation

namespace Lamping.Checks.SingleStepNonoverlapHeadReflectionChecks
open Graph Lambda Lambda.Labelled AG

/-- Actual result-lambda terminal singleton in the existing closed wrapped
INIT. SOURCE Joint is realized on the same physical presentation. -/
theorem actual_result_lambda :
    ∃ sourceSelection : OccurrenceFragmentSelection FanSuccessfulChains.original
        FanSuccessfulReachable.concrete.site.net (.inl ()),
      ∃ targetSelection : OccurrenceFragmentSelection FanSuccessfulChains.current
        FanSuccessfulReachable.concrete.site.reduce (.inl ()),
      JointRepresentation FanSuccessfulChains.sourceClosed sourceSelection ∧
      SameChainRepresentation targetSelection FanSuccessfulChains.outer_stop FanSuccessfulChains.outer_stop ∧
      FanSuccessfulChains.current.labelAt [.fn]=FanSuccessfulChains.current.labelAt [.fn] := by
  have originalMatches := encode_closed_matches FanSuccessfulReachable.term FanSuccessfulReachable.closed 0
  have matching := FanSuccessfulReachable.concrete.sourceIso.matches originalMatches
  obtain ⟨originalSelection,initialJoint⟩ := encode_initial_joint_realization FanSuccessfulChains.original
    FanSuccessfulChains.sourceClosed FanSuccessfulChains.initial 0
  obtain ⟨sourceSelection⟩ := matching.occurrence_fragment_selection FanSuccessfulChains.sourceClosed
  have joint := (FanSuccessfulReachable.concrete.sourceIso.joint_representation originalMatches
    FanSuccessfulChains.sourceClosed originalSelection sourceSelection).mpr initialJoint
  obtain ⟨targetSelection⟩ := FanSuccessfulReachable.beta_matches.occurrence_fragment_selection FanSuccessfulChains.targetClosed
  obtain ⟨oldFlow⟩ := encode_flowBalance FanSuccessfulReachable.term 0
  obtain ⟨oldBalance⟩ := encode_indexed_balance FanSuccessfulReachable.term 0
  have read : PrerequisiteReadsDirected FanSuccessfulChains.current [.fn] [.fn] false :=
    ⟨Or.inr ⟨_,_,rfl,rfl⟩,rfl⟩
  have created : BetaCreatedIncoming
      (.lam (.atom 3) (.app (.atom 4) (.app (.atom 5) (.var (.atom 6) 0) (.var (.atom 7) 1)) (.var (.atom 8) 1)))
      [.fn] [.fn] := Or.inl rfl
  have reflected := FanSuccessfulReachable.concrete.site.one_step_nonoverlap_false_head_labels
    FanSuccessfulChains.initial (.nil _) FanSuccessfulChains.sourceClosed matching
    (FanSuccessfulReachable.concrete.sourceIso.rootInputs (encode_closed_independence FanSuccessfulReachable.term FanSuccessfulReachable.closed 0).rootInputs)
    (FanSuccessfulReachable.concrete.sourceIso.flowBalance oldFlow) rfl
    (FanSuccessfulReachable.concrete.sourceIso.indexed_balance oldBalance) rfl
    (FanSuccessfulReachable.concrete.sourceIso.transparency (encode_closed_transparency FanSuccessfulReachable.term FanSuccessfulReachable.closed 0))
    FanSuccessfulReachable.relative (by simp [FanSuccessfulReachable.endpoint,Marked.Normal])
    FanSuccessfulChains.actualStep (by rfl) (by intro stamp eq;cases eq)
    sourceSelection joint targetSelection read read FanSuccessfulChains.outer_stop FanSuccessfulChains.outer_stop
    created created rfl
  exact ⟨sourceSelection,targetSelection,joint,rfl,reflected⟩

private theorem copySourceClosed : Closed FanBodyBindingIdentityReachable.original.erase :=
  by simpa only [FanBodyBindingIdentityReachable.original,erase_initLabels] using FanBodyBindingIdentityReachable.closed

private def copyStop : PrerequisiteChain FanBodyBindingIdentityReachable.current [.fn] [[.fn]] :=
  .redex_lam (p:=[]) rfl

/-- Actual strict argument-copy lambda at FUNCTION in (lambda x.x x) I.
This directly calls the new top with real selectors and honest INIT Joint;
the comparison is a selfpair, not a distinct physical-image claim. -/
theorem actual_copy_lambda :
    ∃ sourceSelection : OccurrenceFragmentSelection FanBodyBindingIdentityReachable.original
        FanBodyBindingIdentityReachable.concrete.site.net (.inl ()),
      ∃ targetSelection : OccurrenceFragmentSelection FanBodyBindingIdentityReachable.current
        FanBodyBindingIdentityReachable.concrete.site.reduce (.inl ()),
      JointRepresentation copySourceClosed sourceSelection ∧
      SameChainRepresentation targetSelection copyStop copyStop ∧
      BetaCreatedIncoming (.app (.atom 2) (.var (.atom 3) 0) (.var (.atom 4) 0)) [] [.fn] ∧
      FanBodyBindingIdentityReachable.current.labelAt [.fn]=FanBodyBindingIdentityReachable.current.labelAt [.fn] := by
  have originalMatches := encode_closed_matches FanBodyBindingIdentityReachable.term FanBodyBindingIdentityReachable.closed 0
  have matching := FanBodyBindingIdentityReachable.concrete.sourceIso.matches originalMatches
  obtain ⟨originalSelection,initialJoint⟩ := encode_initial_joint_realization FanBodyBindingIdentityReachable.original
    copySourceClosed FanBodyBindingIdentityReachable.initial 0
  obtain ⟨sourceSelection⟩ := matching.occurrence_fragment_selection (current:=FanBodyBindingIdentityReachable.original) copySourceClosed
  have joint := (FanBodyBindingIdentityReachable.concrete.sourceIso.joint_representation originalMatches
    copySourceClosed originalSelection sourceSelection).mpr initialJoint
  obtain ⟨targetSelection⟩ := FanBodyBindingIdentityReachable.beta_matches.occurrence_fragment_selection FanBodyBindingIdentityReachable.currentClosed
  obtain ⟨oldFlow⟩ := encode_flowBalance FanBodyBindingIdentityReachable.term 0
  obtain ⟨oldBalance⟩ := encode_indexed_balance FanBodyBindingIdentityReachable.term 0
  have read : PrerequisiteReadsDirected FanBodyBindingIdentityReachable.current [.fn] [.fn] false :=
    ⟨Or.inr ⟨_,_,rfl,rfl⟩,rfl⟩
  have chain : PrerequisiteChain FanBodyBindingIdentityReachable.current [.fn] [[.fn]] := .redex_lam (p:=[]) rfl
  have created : BetaCreatedIncoming (.app (.atom 2) (.var (.atom 3) 0) (.var (.atom 4) 0)) [] [.fn] :=
    betaCreatedIncoming_iff.mpr (Or.inr ⟨[.fn],rfl,rfl⟩)
  have reflected := FanBodyBindingIdentityReachable.concrete.site.one_step_nonoverlap_false_head_labels
    FanBodyBindingIdentityReachable.initial (.nil _) copySourceClosed matching
    (FanBodyBindingIdentityReachable.concrete.sourceIso.rootInputs (encode_closed_independence FanBodyBindingIdentityReachable.term FanBodyBindingIdentityReachable.closed 0).rootInputs)
    (FanBodyBindingIdentityReachable.concrete.sourceIso.flowBalance oldFlow) rfl
    (FanBodyBindingIdentityReachable.concrete.sourceIso.indexed_balance oldBalance) rfl
    (FanBodyBindingIdentityReachable.concrete.sourceIso.transparency (encode_closed_transparency FanBodyBindingIdentityReachable.term FanBodyBindingIdentityReachable.closed 0))
    FanBodyBindingIdentityReachable.relative (by simp [FanBodyBindingIdentityReachable.endpoint,Marked.Normal])
    FanBodyBindingIdentityReachable.actualStep (by rfl) (by intro stamp eq;cases eq)
    sourceSelection joint targetSelection read read chain chain created created rfl
  exact ⟨sourceSelection,targetSelection,joint,rfl,created,reflected⟩

#print axioms actual_result_lambda
#print axioms actual_copy_lambda
end Lamping.Checks.SingleStepNonoverlapHeadReflectionChecks
