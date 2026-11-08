import Lamping.Lamping.GivenFalseSpineFirstSourceReflection
import Lamping.Checks.BetaChainEvaluatedResiduals
import Lamping.Lamping.InitialJointRepresentation
import Lamping.Lamping.JointRepresentationTransport

namespace Lamping.Checks.GivenFalseSpineFirstSourceReflectionChecks
open AG Graph Lambda Lambda.Labelled FanSuccessfulChains BetaChainEvaluatedResidualsChecks

private abbrev rightCurrent : LTerm := .lam rightLabel callerBody
private def member : {p : Path //p∈rightEdges} := ⟨right,by decide⟩
private theorem old : Marked.RelativeOldHistory [[.fn]] [[.fn]]
    (Marked.mark [[.fn]] original.erase) FanSuccessfulReachable.endpoint :=
  .cons (.appL (.redRoot _ _ _)) (by decide) (.nil _)
private theorem selected (name : Path) (inside : name∈([[.fn]] : List Path)) :
    original.degreeAt name=some (.atom 2) := by
  have same := List.mem_singleton.mp inside
  subst name;rfl
private theorem marked : ¬rightCurrent.label.OuterBarsSafe (fun x=>x≠Label.atom 2) := by
  change ¬rightLabel.OuterBarsSafe (fun x=>x≠Label.atom 2)
  simp [rightLabel,Label.outerBarsSafe_concat,Label.atom,Label.under,Label.OuterBarsSafe]

/-- Two different actual starts share four reads. Their first FALSE marked ARG
lambda is the SAME leaf; SOURCE FIRST equality is honestly reflexive, while
its proof below directly invokes the new full high theorem. -/
theorem actual_false_first_source_reflection
    (targetSelection : OccurrenceFragmentSelection current site.reduce (.inl ())) :
    ∃sourceSelection : OccurrenceFragmentSelection original site.net (.inl ()),
      JointRepresentation sourceClosed sourceSelection ∧
      ∃localTarget,∃localHistory : History [[.fn]] (initLabels original.erase) localTarget,
      ∃edge : BetaEdge site.net,
      ∃selection : SourceEdgeSelection (initLabels original.erase) site.net (.inl ()),
      ∃_siteGeometry : SiteBetaGeometry site edge,
      ∃left : EvaluatedChainResiduals site (localTarget:=localTarget) edge selection targetSelection right_lambda_chain,
      ∃right : EvaluatedChainResiduals site (localTarget:=localTarget) edge selection targetSelection right_variable_chain,
      ∃spine : DirectedMarkerSpine [[.fn]] original (.atom 2) false [[.fn]] current [] FanSuccessfulChains.right,
      ∃leaf snapshot,∃geometry : SpineIncidenceProvenance [[.fn]] original (.atom 2) false spine
        (by rfl : current.subterm FanSuccessfulChains.right=some rightCurrent) leaf snapshot,
      ∃pair : PairedSpineReannotation geometry localHistory (erase_initLabels original.erase).symm,
        left.node member=pair.current ∧right.node member=pair.current ∧
        FanSuccessfulChains.right≠rightVar ∧(left.blocks site).length=4 ∧
        leaf.firstNode.label=leaf.firstNode.label := by
  have originalMatches : Matches FanSuccessfulReachable.net (.inl ()) original.erase :=
    encode_closed_matches FanSuccessfulReachable.term FanSuccessfulReachable.closed 0
  have matching := FanSuccessfulReachable.concrete.sourceIso.matches originalMatches
  obtain ⟨initialSelection,initialJoint⟩ := encode_initial_joint_realization original sourceClosed initial 0
  obtain ⟨sourceSelection⟩ := matching.occurrence_fragment_selection sourceClosed
  have joint := (FanSuccessfulReachable.concrete.sourceIso.joint_representation originalMatches
    sourceClosed initialSelection sourceSelection).mpr initialJoint
  obtain ⟨localTarget,localHistory,edge,selection,siteGeometry,left,right,_blocks,length,_nonempty⟩ :=
    actual_ordered_chain_evaluators targetSelection
  have spine : DirectedMarkerSpine [[.fn]] original (.atom 2) false [[.fn]] current [] FanSuccessfulChains.right :=
    old.directed_marker_spine actualHistory selected (initial.outerBarsSafe _)
      (start:=FanSuccessfulChains.right) (before:=[]) .refl
      ⟨Or.inr ⟨_,_,rfl,rfl⟩,rfl⟩ rfl marked (by intro e inside;cases inside)
  obtain ⟨leaf,snapshot,⟨geometry⟩⟩ := spine.incidence_leaf_output sourceClosed
    (by rfl : current.subterm FanSuccessfulChains.right=some rightCurrent)
  obtain ⟨pair⟩ := geometry.paired_reannotation localHistory (erase_initLabels original.erase).symm
  have same := left.given_false_spine_first_source_labels site member member
    (ordinal:=0) rfl rfl pair pair matching selected (initial.outerBarsSafe _)
    (.nil original) initial sourceClosed sourceSelection joint.1 siteGeometry right (by rfl)
  have leftLookup : left.node member=pair.current :=
    Option.some.inj ((left.lookup member).symm.trans pair.currentLookup)
  have rightLookup : right.node member=pair.current :=
    Option.some.inj ((right.lookup member).symm.trans pair.currentLookup)
  exact ⟨sourceSelection,joint,localTarget,localHistory,edge,selection,siteGeometry,left,right,
    spine,leaf,snapshot,geometry,pair,leftLookup,rightLookup,by decide,length,same⟩

theorem actual_nonempty_false_first_source_reflection :
    ∃targetSelection : OccurrenceFragmentSelection current site.reduce (.inl ()),
      ∃sourceSelection : OccurrenceFragmentSelection original site.net (.inl ()),
      JointRepresentation sourceClosed sourceSelection ∧
      ∃localTarget,∃localHistory : History [[.fn]] (initLabels original.erase) localTarget,
      ∃edge : BetaEdge site.net,
      ∃selection : SourceEdgeSelection (initLabels original.erase) site.net (.inl ()),
      ∃_siteGeometry : SiteBetaGeometry site edge,
      ∃left : EvaluatedChainResiduals site (localTarget:=localTarget) edge selection targetSelection right_lambda_chain,
      ∃right : EvaluatedChainResiduals site (localTarget:=localTarget) edge selection targetSelection right_variable_chain,
      ∃spine : DirectedMarkerSpine [[.fn]] original (.atom 2) false [[.fn]] current [] FanSuccessfulChains.right,
      ∃leaf snapshot,∃geometry : SpineIncidenceProvenance [[.fn]] original (.atom 2) false spine
        (by rfl : current.subterm FanSuccessfulChains.right=some rightCurrent) leaf snapshot,
      ∃pair : PairedSpineReannotation geometry localHistory (erase_initLabels original.erase).symm,
        left.node member=pair.current ∧right.node member=pair.current ∧
        FanSuccessfulChains.right≠rightVar ∧(left.blocks site).length=4 ∧
        leaf.firstNode.label=leaf.firstNode.label := by
  obtain ⟨targetSelection⟩ := FanSuccessfulReachable.beta_matches.occurrence_fragment_selection targetClosed
  exact ⟨targetSelection,actual_false_first_source_reflection targetSelection⟩

#print axioms actual_false_first_source_reflection
#print axioms actual_nonempty_false_first_source_reflection
end Lamping.Checks.GivenFalseSpineFirstSourceReflectionChecks
