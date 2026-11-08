import Lamping.Lamping.ReachableJointRepresentation
import Lamping.Checks.FunctionWrappedReachable
import Lamping.Checks.WrappedSuccessfulChains

namespace Lamping.Checks.ReachableJointRepresentation
open AG Graph Lambda Lambda.Labelled
private noncomputable abbrev site := FunctionWrappedReachable.concrete.site
private noncomputable abbrev graph := ActualNet.ofNet site.reduce
private abbrev original := WrappedSuccessfulChains.original

theorem actual_closed_joint_and_family_projection :
    ∃current : LTerm,∃raw : ParallelHistory original.erase current.erase,
      ∃actual : LabelledGraphProjection (ActualNet.initial original.erase) graph (.inl ()) [.beta 0] original current raw,
      ∃selection : OccurrenceFragmentSelection current graph.net (.inl ()),
      ∃observed : ParallelHistory original.erase current.erase,
        INIT original ∧Closed original.erase ∧
        GraphTrace (ActualNet.initial original.erase) graph [.beta 0] ∧
        site.betaSyntaxFiber (.inl ()) original.erase=[[.fn]] ∧
        JointRepresentation (actual.label_history.closed WrappedSuccessfulChains.sourceClosed) selection ∧
        actual.SourceChainREP ∧ParallelHistory.Observable observed ∧raw.derivation=observed.derivation ∧
        PermEq raw observed ∧History observed.derivation.paths original current ∧CompleteDerivation observed ∧
        RootInputs graph.net (.inl ()) ∧Matches graph.net (.inl ()) current.erase ∧
        (∀{p q : Path} {es fs : List Path}
          (first : PrerequisiteChain current p es) (second : PrerequisiteChain current q fs),
          SameChainRepresentation selection first second →
          ChainIncidenceIsomorphic
            (chainSyntaxIncidence current (actual.label_history.closed WrappedSuccessfulChains.sourceClosed) es)
            (chainSyntaxIncidence current (actual.label_history.closed WrappedSuccessfulChains.sourceClosed) fs)) := by
  have trace : GraphTrace (ActualNet.initial original.erase) graph [.beta 0] :=
    .cons FunctionWrappedReachable.actual_beta_step (.iso (NetIso.refl _))
  obtain ⟨current,raw,actual,_rawLabels,_inputs,matching⟩ :=
    initial_labelled_trace_projection original WrappedSuccessfulChains.sourceClosed graph [.beta 0] trace
  obtain ⟨selection⟩ := matching.occurrence_fragment_selection
    (actual.label_history.closed WrappedSuccessfulChains.sourceClosed)
  obtain ⟨observed,observable,same,permutation,labels,complete,inputs,finalMatches⟩ :=
    actual.complete_family_projection WrappedSuccessfulChains.initial WrappedSuccessfulChains.sourceClosed
  refine ⟨current,raw,actual,selection,observed,WrappedSuccessfulChains.initial,
    WrappedSuccessfulChains.sourceClosed,trace,FunctionWrappedReachable.actual_fiber,
    actual.initial_joint_representation WrappedSuccessfulChains.initial WrappedSuccessfulChains.sourceClosed selection,
    actual.initial_source_chain_rep WrappedSuccessfulChains.initial WrappedSuccessfulChains.sourceClosed,
    observable,same,permutation,labels,complete,inputs,finalMatches,?_⟩
  intro p q es fs first second physical
  exact actual.actual_chain_representation_inverse WrappedSuccessfulChains.initial
    WrappedSuccessfulChains.sourceClosed selection first second physical

#print axioms actual_closed_joint_and_family_projection
end Lamping.Checks.ReachableJointRepresentation
