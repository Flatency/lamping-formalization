import Lamping.Lamping.SpinePhysicalEvaluation
import Lamping.Checks.PairedMarkerSpineReannotation

namespace Lamping.Checks.SpinePhysicalEvaluationChecks
open Graph Lambda Lambda.Labelled AG
open UniformOldNodeLabelSuffixChecks
open DirectedMarkerSpineIncidenceChecks.Nested

private def singletonMember : {p : Path // p∈[[.fn]]} := ⟨[.fn],by decide⟩

/-- A real forward Nested schedule with at least two creation frames.
The physical configuration is an honest premise; the actual WHOLE-chain member
and its SAME producer residual, complete local tails and base formula are consumed. -/
theorem actual_forward_multiple_frame_physical_fold
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
    (targetSelection : OccurrenceFragmentSelection targetForward site.reduce root) :
    ∃leaf snapshot,∃geometry : SpineIncidenceProvenance family sourceWrapped (.atom 10) true
      forwardSpine (by rfl : targetForward.subterm [.fn]=some target) leaf snapshot,
      2≤geometry.creationFrames.length ∧leaf.after≠[] ∧
      ∃localTarget,∃localHistory : History [[.fn],[.fn]] (initLabels sourceWrapped.erase) localTarget,
        ∃edge : BetaEdge site.net,
          ∃selection : SourceEdgeSelection (initLabels sourceWrapped.erase) site.net root,
            SiteBetaGeometry site edge ∧
            ∃paired : PairedSpineReannotation geometry localHistory (erase_initLabels sourceWrapped.erase).symm,
              paired.localTailPieces≠[] ∧
              orientPhysical true (selection.evalLabel edge paired.current.label)=
                orientPhysical true (selection.evalLabel edge paired.base.current.label)++
                  (paired.localTailPieces.map
                    (interpretReadLetters selection.atomWord edge.principal edge.reverseRoute true)).flatten ∧
              ExactPhysicalDirectedFormula selection edge paired.base.middle leaf.site paired.base.alpha true
                paired.base.firstNode paired.base.lastNode paired.base.marker paired.base.current ∧
              BetaPathResidual site edge
                ((targetSelection (actualChainPosition (successful_readings.1) singletonMember)).fragment.segments.map (plugEnd _ _).invFun)
                (selection.evalLabel edge paired.current.label) ∧
              selection.evalLabel edge paired.current.label≠[] := by
  obtain ⟨leaf,snapshot,geometry,multiple,after,_continuation⟩ :=
    PairedMarkerSpineReannotationChecks.Nested.forward_multiple_frames
  obtain ⟨localTarget,localHistory,edge,selection,siteGeometry,evaluation,paired,same,full,formula,
      residual,nonempty⟩ :=
    site.beta_spine_head_physical_fold sourceClosed matching inputs flow positive balance rootDepth
      transparency relative normal labelsForward targetSelection (successful_readings.1) singletonMember geometry
  have tails : paired.localTailPieces≠[] := by
    intro empty
    have count := paired.tail_count
    simp only [empty,List.length_nil] at count
    omega
  rw [same] at full residual nonempty
  exact ⟨leaf,snapshot,geometry,multiple,after,localTarget,localHistory,edge,selection,siteGeometry,
    paired,tails,full,formula,residual,nonempty⟩

/-- A real reverse Nested schedule with at least two creation frames.
The physical configuration is an honest premise; the actual WHOLE-chain member
and its SAME producer residual, complete local tails and base formula are consumed. -/
theorem actual_reverse_multiple_frame_physical_fold
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
    (targetSelection : OccurrenceFragmentSelection targetReverse site.reduce root) :
    ∃leaf snapshot,∃geometry : SpineIncidenceProvenance family sourceWrapped (.atom 10) false
      reverseSpine (by rfl : targetReverse.subterm [.fn]=some reverseResult) leaf snapshot,
      2≤geometry.creationFrames.length ∧leaf.after≠[] ∧
      ∃localTarget,∃localHistory : History [[.fn,.arg],[.fn]] (initLabels sourceWrapped.erase) localTarget,
        ∃edge : BetaEdge site.net,
          ∃selection : SourceEdgeSelection (initLabels sourceWrapped.erase) site.net root,
            SiteBetaGeometry site edge ∧
            ∃paired : PairedSpineReannotation geometry localHistory (erase_initLabels sourceWrapped.erase).symm,
              paired.localTailPieces≠[] ∧
              orientPhysical false (selection.evalLabel edge paired.current.label)=
                orientPhysical false (selection.evalLabel edge paired.base.current.label)++
                  (paired.localTailPieces.map
                    (interpretReadLetters selection.atomWord edge.principal edge.reverseRoute false)).flatten ∧
              ExactPhysicalDirectedFormula selection edge paired.base.middle leaf.site paired.base.alpha false
                paired.base.firstNode paired.base.lastNode paired.base.marker paired.base.current ∧
              BetaPathResidual site edge
                ((targetSelection (actualChainPosition (successful_readings.2) singletonMember)).fragment.segments.map (plugEnd _ _).invFun)
                (selection.evalLabel edge paired.current.label) ∧
              selection.evalLabel edge paired.current.label≠[] := by
  obtain ⟨leaf,snapshot,geometry,multiple,after,_continuation⟩ :=
    PairedMarkerSpineReannotationChecks.Nested.reverse_multiple_frames
  obtain ⟨localTarget,localHistory,edge,selection,siteGeometry,evaluation,paired,same,full,formula,
      residual,nonempty⟩ :=
    site.beta_spine_head_physical_fold sourceClosed matching inputs flow positive balance rootDepth
      transparency relative normal labelsReverse targetSelection (successful_readings.2) singletonMember geometry
  have tails : paired.localTailPieces≠[] := by
    intro empty
    have count := paired.tail_count
    simp only [empty,List.length_nil] at count
    omega
  rw [same] at full residual nonempty
  exact ⟨leaf,snapshot,geometry,multiple,after,localTarget,localHistory,edge,selection,siteGeometry,
    paired,tails,full,formula,residual,nonempty⟩

#print axioms EvaluatedChainResiduals.spine_head_physical_fold
#print axioms PathSite.beta_spine_head_physical_fold
#print axioms actual_forward_multiple_frame_physical_fold
#print axioms actual_reverse_multiple_frame_physical_fold
end Lamping.Checks.SpinePhysicalEvaluationChecks
