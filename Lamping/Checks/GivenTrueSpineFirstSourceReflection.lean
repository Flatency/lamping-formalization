import Lamping.Lamping.GivenTrueSpineFirstSourceReflection
import Lamping.Checks.BetaBeforeBlockImages
import Lamping.Lamping.InitialJointRepresentation
import Lamping.Lamping.JointRepresentationTransport

namespace Lamping.Checks.GivenTrueSpineFirstSourceReflectionChecks
open AG Graph Lambda Lambda.Labelled BetaBeforeBlockImagesChecks

private def chain : PrerequisiteChain target [] [[.fn]] := .redex_app rfl
private def member : {p : Path //p∈[[.fn]]} := ⟨[.fn],by decide⟩

theorem actual_initial_whole_first_source_reflection
    (targetSelection : OccurrenceFragmentSelection target site.reduce (.inl ())) :
    ∃ sourceSelection : OccurrenceFragmentSelection source site.net (.inl ()),
      JointRepresentation WrappedSuccessfulChains.sourceClosed sourceSelection ∧
      ∃localTarget,∃localHistory : History [[.fn]] (initLabels source.erase) localTarget,
      ∃edge : BetaEdge site.net,
      ∃selection : SourceEdgeSelection (initLabels source.erase) site.net (.inl ()),
      ∃_siteGeometry : SiteBetaGeometry site edge,
      ∃out : EvaluatedChainResiduals site (localTarget:=localTarget) edge selection targetSelection chain,
      ∃spine : DirectedMarkerSpine [[.fn]] source (.atom 2) true [[.fn]] target [] [.fn],
      ∃leaf snapshot,∃geometry : SpineIncidenceProvenance [[.fn]] source (.atom 2) true spine
        (by rfl : target.subterm [.fn]=some functionTerm) leaf snapshot,
      ∃pair : PairedSpineReannotation geometry localHistory (erase_initLabels source.erase).symm,
        out.node member=pair.current ∧
        leaf.firstNode.label=leaf.firstNode.label := by
  have originalMatches : Matches FunctionWrappedReachable.net (.inl ()) source.erase :=
    encode_closed_matches FunctionWrappedReachable.term FunctionWrappedReachable.closed 0
  have matching := FunctionWrappedReachable.concrete.sourceIso.matches originalMatches
  obtain ⟨initialSelection,initialJoint⟩ := encode_initial_joint_realization source
    WrappedSuccessfulChains.sourceClosed WrappedSuccessfulChains.initial 0
  obtain ⟨sourceSelection⟩ := matching.occurrence_fragment_selection WrappedSuccessfulChains.sourceClosed
  have joint := (FunctionWrappedReachable.concrete.sourceIso.joint_representation originalMatches
    WrappedSuccessfulChains.sourceClosed initialSelection sourceSelection).mpr initialJoint
  have inputs := FunctionWrappedReachable.concrete.sourceIso.rootInputs
    (encode_closed_independence FunctionWrappedReachable.term FunctionWrappedReachable.closed 0).rootInputs
  obtain ⟨originalFlow⟩ := encode_flowBalance FunctionWrappedReachable.term 0
  have flow := FunctionWrappedReachable.concrete.sourceIso.flowBalance originalFlow
  obtain ⟨originalBalance⟩ := encode_indexed_balance FunctionWrappedReachable.term 0
  have balance := FunctionWrappedReachable.concrete.sourceIso.indexed_balance originalBalance
  have transparency := FunctionWrappedReachable.concrete.sourceIso.transparency
    (encode_closed_transparency FunctionWrappedReachable.term FunctionWrappedReachable.closed 0)
  obtain ⟨localTarget,localHistory,_erase,_targetMatches,edge,selection,siteGeometry,all⟩ :=
    site.beta_evaluated_chain_residuals WrappedSuccessfulChains.sourceClosed matching inputs flow rfl balance rfl
      transparency FunctionWrappedReachable.relative
      (by simp [FunctionWrappedReachable.endpoint,Marked.Normal]) WrappedSuccessfulChains.actualHistory targetSelection
  obtain ⟨out⟩ := all chain
  have spine : DirectedMarkerSpine [[.fn]] source (.atom 2) true [[.fn]] target [] [.fn] :=
    old.directed_marker_spine WrappedSuccessfulChains.actualHistory selected
      (WrappedSuccessfulChains.initial.outerBarsSafe _) (start:=[]) (before:=[]) .refl
      ⟨Or.inl ⟨_,_,_,rfl,rfl⟩,rfl⟩ rfl marked (by intro e inside;cases inside)
  obtain ⟨leaf,snapshot,⟨geometry⟩⟩ := spine.incidence_leaf_output WrappedSuccessfulChains.sourceClosed
    (by rfl : target.subterm [.fn]=some functionTerm)
  obtain ⟨pair⟩ := geometry.paired_reannotation localHistory (erase_initLabels source.erase).symm
  have same := out.given_true_spine_first_source_labels site member member
    (ordinal:=0) rfl rfl pair pair matching selected (WrappedSuccessfulChains.initial.outerBarsSafe _)
    (.nil source) WrappedSuccessfulChains.initial WrappedSuccessfulChains.sourceClosed
    sourceSelection joint.1 siteGeometry out (by rfl)
  have lookup : out.node member=pair.current :=
    Option.some.inj ((out.lookup member).symm.trans pair.currentLookup)
  exact ⟨sourceSelection,joint,localTarget,localHistory,edge,selection,siteGeometry,out,
    spine,leaf,snapshot,geometry,pair,lookup,same⟩

theorem actual_nonempty_first_source_reflection :
    ∃targetSelection : OccurrenceFragmentSelection target site.reduce (.inl ()),
      ∃sourceSelection : OccurrenceFragmentSelection source site.net (.inl ()),
        JointRepresentation WrappedSuccessfulChains.sourceClosed sourceSelection ∧
        ∃localTarget,∃localHistory : History [[.fn]] (initLabels source.erase) localTarget,
        ∃edge : BetaEdge site.net,
        ∃selection : SourceEdgeSelection (initLabels source.erase) site.net (.inl ()),
        ∃_siteGeometry : SiteBetaGeometry site edge,
        ∃out : EvaluatedChainResiduals site (localTarget:=localTarget) edge selection targetSelection chain,
        ∃spine : DirectedMarkerSpine [[.fn]] source (.atom 2) true [[.fn]] target [] [.fn],
        ∃leaf snapshot,∃geometry : SpineIncidenceProvenance [[.fn]] source (.atom 2) true spine
          (by rfl : target.subterm [.fn]=some functionTerm) leaf snapshot,
        ∃pair : PairedSpineReannotation geometry localHistory (erase_initLabels source.erase).symm,
          out.node member=pair.current ∧leaf.firstNode.label=leaf.firstNode.label := by
  obtain ⟨targetSelection⟩ := FunctionWrappedReachable.beta_matches.occurrence_fragment_selection
    WrappedSuccessfulChains.targetClosed
  exact ⟨targetSelection,actual_initial_whole_first_source_reflection targetSelection⟩

#print axioms actual_initial_whole_first_source_reflection
#print axioms actual_nonempty_first_source_reflection
end Lamping.Checks.GivenTrueSpineFirstSourceReflectionChecks

