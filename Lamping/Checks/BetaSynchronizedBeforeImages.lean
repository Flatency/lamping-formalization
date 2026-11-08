import Lamping.Lamping.BetaSynchronizedBeforeImages
import Lamping.Checks.BetaBeforeBlockImages
import Lamping.Lamping.InitialJointRepresentation
import Lamping.Lamping.JointRepresentationTransport
namespace Lamping.Checks.BetaSynchronizedBeforeImagesChecks
open Graph Lambda Lambda.Labelled AG BetaBeforeBlockImagesChecks

private def segment : PrerequisitePrefix target [.arg] [[.arg]] [] :=
  .lam (parent:=[]) (step:=.arg) rfl (by decide) .refl
private def reading : PrerequisiteReadsDirected target [] [.fn] true :=
  ⟨Or.inl ⟨_,_,_,rfl,rfl⟩,rfl⟩
private def spine : DirectedMarkerSpine [[.fn]] source (.atom 2) true [[.fn]] target
    ([[.arg]].map target.labelAt) [.fn] :=
  old.directed_marker_spine WrappedSuccessfulChains.actualHistory selected
    (WrappedSuccessfulChains.initial.outerBarsSafe _) segment reading rfl marked beforeSafe

private theorem safeBefore : ∀e∈([[.arg]] : List Path),degreeReadSafe (.atom 2) (target.labelAt e) := by
  intro e member value same
  have eq:=List.mem_singleton.mp member;subst e
  change some (Label.atom 9)=some value at same
  have eq := Option.some.inj same;subst value
  trivial

private def cut : ActualUnsafeMarkerCut [[.fn]] [[.fn]] source target (.atom 2) [.arg] [[.arg],[.fn]] where
  before := [[.arg]]
  edge := [.fn]
  after := []
  reader := []
  node := functionTerm
  forward := true
  split := rfl
  segment := segment
  remaining := .redex_app rfl
  reading := reading
  lookup := rfl
  safeBefore := safeBefore
  marked := marked
  spine := spine
  leaf := spine.leaf_output rfl

def variableChain : PrerequisiteChain target [.arg,.body] [[.arg],[.fn]] :=
  .var (parent:=[.arg]) (rest:=[]) rfl rfl rfl rfl targetChain
private def variableSegment : PrerequisitePrefix target [.arg,.body] [[.arg]] [] :=
  .var (parent:=[.arg]) (rest:=[]) rfl rfl rfl rfl segment
private def variableSpine : DirectedMarkerSpine [[.fn]] source (.atom 2) true [[.fn]] target
    ([[.arg]].map target.labelAt) [.fn] :=
  old.directed_marker_spine WrappedSuccessfulChains.actualHistory selected
    (WrappedSuccessfulChains.initial.outerBarsSafe _) variableSegment reading rfl marked beforeSafe
private def variableCut : ActualUnsafeMarkerCut [[.fn]] [[.fn]] source target (.atom 2)
    [.arg,.body] [[.arg],[.fn]] where
  before := [[.arg]]
  edge := [.fn]
  after := []
  reader := []
  node := functionTerm
  forward := true
  split := rfl
  segment := variableSegment
  remaining := .redex_app rfl
  reading := reading
  lookup := rfl
  safeBefore := safeBefore
  marked := marked
  spine := variableSpine
  leaf := variableSpine.leaf_output rfl

/-- A real physical beta site and actual initial Joint supply the inputs.
The two successful chains have distinct lambda and variable starts
but the same nonempty READ list. The BEFORE list has one real block. -/
theorem actual_nonempty_before_pair :
    ∃ sourceSelection : OccurrenceFragmentSelection source site.net (.inl ()),
    ∃ targetSelection : OccurrenceFragmentSelection target site.reduce (.inl ()),
      JointRepresentation WrappedSuccessfulChains.sourceClosed sourceSelection ∧
      (canonicalChainImage targetSelection targetChain).take 1=
        (canonicalChainImage targetSelection variableChain).take 1 ∧
      ((canonicalChainImage targetSelection targetChain).take 1).length=1 ∧
      ((canonicalChainImage targetSelection variableChain).take 1).length=1 := by
  have originalMatches : Matches FunctionWrappedReachable.net (.inl ()) source.erase :=
    encode_closed_matches FunctionWrappedReachable.term FunctionWrappedReachable.closed 0
  have matching := FunctionWrappedReachable.concrete.sourceIso.matches originalMatches
  obtain ⟨originalSelection,initialJoint⟩ := encode_initial_joint_realization source
    WrappedSuccessfulChains.sourceClosed WrappedSuccessfulChains.initial 0
  obtain ⟨sourceSelection⟩ := matching.occurrence_fragment_selection WrappedSuccessfulChains.sourceClosed
  have joint := (FunctionWrappedReachable.concrete.sourceIso.joint_representation originalMatches
    WrappedSuccessfulChains.sourceClosed originalSelection sourceSelection).mpr initialJoint
  obtain ⟨targetSelection⟩ := FunctionWrappedReachable.beta_matches.occurrence_fragment_selection
    WrappedSuccessfulChains.targetClosed
  have inputs := FunctionWrappedReachable.concrete.sourceIso.rootInputs
    (encode_closed_independence FunctionWrappedReachable.term FunctionWrappedReachable.closed 0).rootInputs
  obtain ⟨originalFlow⟩ := encode_flowBalance FunctionWrappedReachable.term 0
  have flow := FunctionWrappedReachable.concrete.sourceIso.flowBalance originalFlow
  obtain ⟨originalBalance⟩ := encode_indexed_balance FunctionWrappedReachable.term 0
  have balance := FunctionWrappedReachable.concrete.sourceIso.indexed_balance originalBalance
  have transparency := FunctionWrappedReachable.concrete.sourceIso.transparency
    (encode_closed_transparency FunctionWrappedReachable.term FunctionWrappedReachable.closed 0)
  have physical := site.beta_synchronized_before_images WrappedSuccessfulChains.sourceClosed matching
    inputs flow rfl balance rfl transparency FunctionWrappedReachable.relative
    (by simp [FunctionWrappedReachable.endpoint,Marked.Normal]) WrappedSuccessfulChains.actualHistory old
    selected (WrappedSuccessfulChains.initial.outerBarsSafe _) (.nil source) WrappedSuccessfulChains.initial
    sourceSelection targetSelection joint.1 targetChain variableChain cut variableCut rfl rfl rfl
  refine ⟨sourceSelection,targetSelection,joint,physical,?_,?_⟩ <;>
    simp only [List.length_take,canonicalChainImage_length] <;> rfl

theorem actual_distinct_starts : ([Step.arg] : Path)≠[.arg,.body] := by decide
#print axioms variableChain
#print axioms actual_nonempty_before_pair
#print axioms actual_distinct_starts
end Lamping.Checks.BetaSynchronizedBeforeImagesChecks
