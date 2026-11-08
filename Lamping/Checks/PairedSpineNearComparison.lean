import Lamping.Lamping.PairedSpineNearComparison
import Lamping.Checks.InteriorSourceBlockEndpoints
import Lamping.Checks.WholeSpineNearBoundary

namespace Lamping.Checks.PairedSpineNearComparisonChecks
open Graph Lambda Lambda.Labelled AG
private abbrev nodeAt (term : LTerm) (path : Path) : LTerm:=
  (term.subterm path).getD (.var (.atom 0) 0)
private def labelSafeDecision (allowed : Label → Prop) [DecidablePred allowed] :
    (label : Label) → Decidable (label.OuterBarsSafe allowed)
  | .single (.atom _) => isTrue True.intro
  | .single (.over d) => show Decidable (allowed d) from inferInstance
  | .single (.under d) => show Decidable (allowed d) from inferInstance
  | .cons (.atom _) rest => labelSafeDecision allowed rest
  | .cons (.over d) rest =>
    letI:=labelSafeDecision allowed rest
    show Decidable (allowed d ∧rest.OuterBarsSafe allowed) from inferInstance
  | .cons (.under d) rest =>
    letI:=labelSafeDecision allowed rest
    show Decidable (allowed d ∧rest.OuterBarsSafe allowed) from inferInstance

private def termSafeDecision (allowed : Label → Prop) [DecidablePred allowed] :
    (term : LTerm) → Decidable (term.OuterBarsSafe allowed)
  | .var label _ => labelSafeDecision allowed label
  | .lam label body =>
    letI:=labelSafeDecision allowed label
    letI:=termSafeDecision allowed body
    show Decidable (label.OuterBarsSafe allowed ∧body.OuterBarsSafe allowed) from inferInstance
  | .app label fn arg =>
    letI:=labelSafeDecision allowed label
    letI:=termSafeDecision allowed fn
    letI:=termSafeDecision allowed arg
    show Decidable (label.OuterBarsSafe allowed ∧fn.OuterBarsSafe allowed ∧arg.OuterBarsSafe allowed) from inferInstance

namespace CopiedSource
open InteriorSourceBlockEndpointsChecks.CopiedSource
abbrev leftNode : LTerm:=nodeAt leftTarget [.fn,.fn]
abbrev rightNode : LTerm:=nodeAt rightTarget [.arg,.fn]

theorem full_global_head_equality : leftNode.label=rightNode.label:=by rfl

theorem sourceSafe : source.OuterBarsSafe (fun d=>d≠Label.atom 15):=by
  letI:=termSafeDecision (fun d=>d≠Label.atom 15) source
  decide

theorem leftMarked : ¬leftNode.label.OuterBarsSafe (fun d=>d≠Label.atom 15):=by
  letI:=labelSafeDecision (fun d=>d≠Label.atom 15) leftNode.label
  decide

theorem rightMarked : ¬rightNode.label.OuterBarsSafe (fun d=>d≠Label.atom 15):=by
  letI:=labelSafeDecision (fun d=>d≠Label.atom 15) rightNode.label
  decide

theorem leftReading : PrerequisiteReadsDirected leftTarget [.fn] [.fn,.fn] true:=
  ⟨Or.inl ⟨_,_,_,rfl,rfl⟩,rfl⟩
theorem rightReading : PrerequisiteReadsDirected rightTarget [.arg] [.arg,.fn] true:=
  ⟨Or.inl ⟨_,_,_,rfl,rfl⟩,rfl⟩

def leftSpine : DirectedMarkerSpine F source (.atom 15) true [[.fn,.arg],[.fn]] leftTarget [] [.fn,.fn]:=
  leftOld.directed_marker_spine leftLabels selected sourceSafe .refl leftReading rfl leftMarked (by simp)
def rightSpine : DirectedMarkerSpine F source (.atom 15) true [[.arg,.arg],[.arg]] rightTarget [] [.arg,.fn]:=
  rightOld.directed_marker_spine rightLabels selected sourceSafe .refl rightReading rfl rightMarked (by simp)

section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable {g : Net signature N B W} {root : B}

/-- Two DISTINCT actual SOURCE near cells, from the same closed original INIT
and two different real OLD schedules. SOURCE REP is an honest condition. -/
theorem actual_nonreflexive_near
    (matching : Matches g root source.erase)
    (sourceSelection : OccurrenceFragmentSelection source g root)
    (representation : ChainRepresentationInvariant (prefixHistory.closed originalClosed) sourceSelection)
    (selection : SourceEdgeSelection localSource g root) (physical : BetaEdge g) :
    INIT original ∧History [[.arg],[.arg],[.arg,.arg],[]] original source ∧
    (4 : Nat)≠16 ∧selection.atomWord 4=selection.atomWord 16 ∧
      ∃leftPosition rightPosition : Position source.erase,
        leftPosition.val≠rightPosition.val ∧
        (sourceSelection leftPosition).fragment.segments=(sourceSelection rightPosition).fragment.segments := by
  obtain ⟨ll,ls,⟨lg⟩⟩:=leftSpine.incidence_leaf_output (prefixHistory.closed originalClosed)
    (by rfl : leftTarget.subterm [.fn,.fn]=some leftNode)
  obtain ⟨rl,rs,⟨rg⟩⟩:=rightSpine.incidence_leaf_output (prefixHistory.closed originalClosed)
    (by rfl : rightTarget.subterm [.arg,.fn]=some rightNode)
  obtain ⟨lp⟩:=lg.paired_reannotation leftLocalLabels (erase_initLabels _).symm
  obtain ⟨rp⟩:=rg.paired_reannotation rightLocalLabels (erase_initLabels _).symm
  obtain ⟨ln⟩:=Lamping.AG.PairedSpineReannotation.near_first_atom lp selected
  obtain ⟨rn⟩:=Lamping.AG.PairedSpineReannotation.near_first_atom rp selected
  have lcurrent : lp.current=leftLocalNode:=Option.some.inj (lp.currentLookup.symm.trans (by rfl))
  have rcurrent : rp.current=rightLocalNode:=Option.some.inj (rp.currentLookup.symm.trans (by rfl))
  have la : ln.atom=4 := by
    have head:=congrArg List.head? ln.word
    rw [lcurrent] at head
    change some (Letter.atom 4)=some (.atom ln.atom) at head
    exact (Letter.atom.inj (Option.some.inj head)).symm
  have ra : rn.atom=16 := by
    have head:=congrArg List.head? rn.word
    rw [rcurrent] at head
    change some (Letter.atom 16)=some (.atom rn.atom) at head
    exact (Letter.atom.inj (Option.some.inj head)).symm
  have separate : ln.position.val≠rn.position.val := by
    intro same
    have leftAt:=ln.basisLookup
    rw [same,rn.basisLookup] at leftAt
    have nodes : rn.basisNode=ln.basisNode:=Option.some.inj leftAt
    have labs:=congrArg LTerm.label nodes
    rw [ln.basisAtomic,rn.basisAtomic,la,ra] at labs
    cases labs
  have compared:=paired_spine_near_evaluations lp rp ln rn leftOld rightOld leftLabels rightLabels
    selected sourceSafe full_global_head_equality prefixHistory initial (prefixHistory.closed originalClosed)
    matching sourceSelection representation selection physical
  refine ⟨initial,prefixHistory,by decide,?_,ln.position,rn.position,separate,compared.2.1⟩
  simpa only [la,ra] using compared.1
end
end CopiedSource

namespace Nested
open UniformOldNodeLabelSuffixChecks
open DirectedMarkerSpineIncidenceChecks.Nested
private def member : {p : Path // p∈[[.fn]]}:=⟨[.fn],by decide⟩

/-- Actual forward schedule; no producer or pair is chosen twice. -/
theorem forward_given_member_comparison
    {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
    {kept : K→Graph.Label signature} {i : Nat}
    (site : PathSite (.beta i) kept (B:=B) (W:=W) (V:=V)) {root : B}
    (matching : Matches site.net root sourceWrapped.erase) (inputs : RootInputs site.net root)
    {boundary : B→Bool} (flow : FlowBalance site.net boundary) (positive : boundary root=true)
    {heights : B→Int} (balance : IndexedLevelBalance site.net heights) (rootDepth : heights root=0)
    (transparency : Transparency site.net root)
    {endpoint : Marked}
    (relative : Marked.RelativeHistory [[.fn],[.fn]]
      (Marked.mark (site.betaSyntaxFiber root sourceWrapped.erase) sourceWrapped.erase) endpoint)
    (normal : Marked.Normal endpoint)
    (sourceSelection : OccurrenceFragmentSelection sourceWrapped site.net root)
    (representation : ChainRepresentationInvariant sourceClosed sourceSelection)
    (targetSelection : OccurrenceFragmentSelection targetForward site.reduce root) :
    INIT originalWrapped ∧History [[.fn],[.fn],[.fn,.arg],[.fn],[.fn]] originalWrapped targetForward ∧
    ∃leaf snapshot,∃geometry : SpineIncidenceProvenance family sourceWrapped (.atom 10) true
      forwardSpine (by rfl : targetForward.subterm [.fn]=some target) leaf snapshot,
      2≤geometry.creationFrames.length ∧leaf.after≠[] ∧
      ∃localTarget,∃localHistory : History [[.fn],[.fn]] (initLabels sourceWrapped.erase) localTarget,
      ∃edge : BetaEdge site.net,
      ∃selection : SourceEdgeSelection (initLabels sourceWrapped.erase) site.net root,
      SiteBetaGeometry site edge ∧
      ∃evaluation : EvaluatedChainResiduals site (localTarget:=localTarget) edge selection targetSelection (successful_readings.1),
      ∃pair : PairedSpineReannotation geometry localHistory (erase_initLabels sourceWrapped.erase).symm,
      pair.localTailPieces≠[] ∧
      ∃near : SpinePhysicalNearBoundary pair sourceSelection selection edge,
        evaluation.node member=pair.current ∧
        selection.atomWord near.first.atom=selection.atomWord near.first.atom ∧
        (orientPhysical true (selection.evalLabel edge (evaluation.node member).label)).head?=
          (orientPhysical true ((sourceSelection near.first.position).fragment.segments)).head? := by
  obtain ⟨leaf,snapshot,geometry,multiple,after,_⟩:=PairedMarkerSpineReannotationChecks.Nested.forward_multiple_frames
  obtain ⟨localTarget,localHistory,_erase,_matching,edge,selection,siteGeometry,all⟩:=
    site.beta_evaluated_chain_residuals sourceClosed matching inputs flow positive balance rootDepth transparency
      relative normal labelsForward targetSelection
  obtain ⟨evaluation⟩:=all (successful_readings.1)
  obtain ⟨pair⟩:=geometry.paired_reannotation localHistory (erase_initLabels _).symm
  obtain ⟨near,same,head,_residual,_nonempty⟩:=
    evaluation.given_spine_near_boundary member pair selected matching sourceSelection
  have compared:=paired_spine_near_evaluations pair pair near.first near.first oldForward oldForward
    labelsForward labelsForward selected sourceSafe rfl globalPrefix initial sourceClosed
    matching sourceSelection representation selection edge
  exact ⟨initial,globalPrefix.append labelsForward,leaf,snapshot,geometry,multiple,after,
    localTarget,localHistory,edge,selection,siteGeometry,evaluation,pair,pair.tails_nonempty multiple,
    near,same,compared.1,head⟩

/-- Actual reverse schedule; no producer or pair is chosen twice. -/
theorem reverse_given_member_comparison
    {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
    {kept : K→Graph.Label signature} {i : Nat}
    (site : PathSite (.beta i) kept (B:=B) (W:=W) (V:=V)) {root : B}
    (matching : Matches site.net root sourceWrapped.erase) (inputs : RootInputs site.net root)
    {boundary : B→Bool} (flow : FlowBalance site.net boundary) (positive : boundary root=true)
    {heights : B→Int} (balance : IndexedLevelBalance site.net heights) (rootDepth : heights root=0)
    (transparency : Transparency site.net root)
    {endpoint : Marked}
    (relative : Marked.RelativeHistory [[.fn,.arg],[.fn]]
      (Marked.mark (site.betaSyntaxFiber root sourceWrapped.erase) sourceWrapped.erase) endpoint)
    (normal : Marked.Normal endpoint)
    (sourceSelection : OccurrenceFragmentSelection sourceWrapped site.net root)
    (representation : ChainRepresentationInvariant sourceClosed sourceSelection)
    (targetSelection : OccurrenceFragmentSelection targetReverse site.reduce root) :
    INIT originalWrapped ∧History [[.fn],[.fn],[.fn,.arg],[.fn,.arg],[.fn]] originalWrapped targetReverse ∧
    ∃leaf snapshot,∃geometry : SpineIncidenceProvenance family sourceWrapped (.atom 10) false
      reverseSpine (by rfl : targetReverse.subterm [.fn]=some reverseResult) leaf snapshot,
      2≤geometry.creationFrames.length ∧leaf.after≠[] ∧
      ∃localTarget,∃localHistory : History [[.fn,.arg],[.fn]] (initLabels sourceWrapped.erase) localTarget,
      ∃edge : BetaEdge site.net,
      ∃selection : SourceEdgeSelection (initLabels sourceWrapped.erase) site.net root,
      SiteBetaGeometry site edge ∧
      ∃evaluation : EvaluatedChainResiduals site (localTarget:=localTarget) edge selection targetSelection (successful_readings.2),
      ∃pair : PairedSpineReannotation geometry localHistory (erase_initLabels sourceWrapped.erase).symm,
      pair.localTailPieces≠[] ∧
      ∃near : SpinePhysicalNearBoundary pair sourceSelection selection edge,
        evaluation.node member=pair.current ∧
        selection.atomWord near.first.atom=selection.atomWord near.first.atom ∧
        (orientPhysical false (selection.evalLabel edge (evaluation.node member).label)).head?=
          (orientPhysical false ((sourceSelection near.first.position).fragment.segments)).head? := by
  obtain ⟨leaf,snapshot,geometry,multiple,after,_⟩:=PairedMarkerSpineReannotationChecks.Nested.reverse_multiple_frames
  obtain ⟨localTarget,localHistory,_erase,_matching,edge,selection,siteGeometry,all⟩:=
    site.beta_evaluated_chain_residuals sourceClosed matching inputs flow positive balance rootDepth transparency
      relative normal labelsReverse targetSelection
  obtain ⟨evaluation⟩:=all (successful_readings.2)
  obtain ⟨pair⟩:=geometry.paired_reannotation localHistory (erase_initLabels _).symm
  obtain ⟨near,same,head,_residual,_nonempty⟩:=
    evaluation.given_spine_near_boundary member pair selected matching sourceSelection
  have compared:=paired_spine_near_evaluations pair pair near.first near.first oldReverse oldReverse
    labelsReverse labelsReverse selected sourceSafe rfl globalPrefix initial sourceClosed
    matching sourceSelection representation selection edge
  exact ⟨initial,globalPrefix.append labelsReverse,leaf,snapshot,geometry,multiple,after,
    localTarget,localHistory,edge,selection,siteGeometry,evaluation,pair,pair.tails_nonempty multiple,
    near,same,compared.1,head⟩
end Nested

#print axioms CopiedSource.full_global_head_equality
#print axioms CopiedSource.sourceSafe
#print axioms CopiedSource.leftMarked
#print axioms CopiedSource.rightMarked
#print axioms CopiedSource.leftReading
#print axioms CopiedSource.rightReading
#print axioms CopiedSource.leftSpine
#print axioms CopiedSource.rightSpine
#print axioms CopiedSource.actual_nonreflexive_near
#print axioms Nested.forward_given_member_comparison
#print axioms Nested.reverse_given_member_comparison
end Lamping.Checks.PairedSpineNearComparisonChecks
