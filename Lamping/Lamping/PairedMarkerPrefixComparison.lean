import Lamping.Lambda.OriginDirectedMarkerPrefix
import Lamping.Lamping.PairedMarkerDirectedEvaluation

namespace Lamping.AG
open Graph Lambda Lambda.Labelled
section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable {g : Net signature N B W} {root : B}

theorem global_leaf_marker_kind
    (leaf : DirectedMarkerLeafOutput F source degree forward ps word) :
    leaf.marker=originMarker leaf.site leaf.first degree :=
  leaf.origin.formula_marker leaf.event.turn leaf.event.redex leaf.reading leaf.lookup leaf.firstLookup leaf.formula

theorem paired_leaf_marker_kind
    {leaf : DirectedMarkerLeafOutput F source degree forward ps word}
    (paired : PairedMarkerEventGeometry leaf localSource localTarget) :
    paired.marker=originMarker leaf.site leaf.first paired.alpha :=
  paired.origin.formula_marker paired.turn paired.redex paired.reading paired.lookup paired.firstLookup paired.formula

/-- Equal global kinds synchronize the local physical marker blocks, while
local degree payloads remain arbitrary and need not be equal. -/
theorem origin_marker_sourceWords
    (atoms : Nat → List (Endpoint g)) (overWord underWord : List (Endpoint g))
    (same : originMarker leftSite leftFirst degree=originMarker rightSite rightFirst degree) :
    (originMarker leftSite leftFirst leftAlpha).sourceWord atoms overWord underWord=
      (originMarker rightSite rightFirst rightAlpha).sourceWord atoms overWord underWord := by
  unfold originMarker at same ⊢
  by_cases left : leftFirst=leftSite ∨leftFirst=leftSite++[.fn,.body]
  · by_cases right : rightFirst=rightSite ∨rightFirst=rightSite++[.fn,.body]
    · simp only [if_pos left,if_pos right,Letter.sourceWord]
    · simp only [if_pos left,if_neg right] at same
      cases same
  · by_cases right : rightFirst=rightSite ∨rightFirst=rightSite++[.fn,.body]
    · simp only [if_neg left,if_pos right] at same
      cases same
    · simp only [if_neg left,if_neg right,Letter.sourceWord]

theorem paired_marker_route_evaluations
    (left : DirectedMarkerLeafOutput F source degree forward ps leftWord)
    (right : DirectedMarkerLeafOutput F source degree forward ps rightWord)
    (leftPaired : PairedMarkerEventGeometry left (initLabels source.erase) localTarget)
    (rightPaired : PairedMarkerEventGeometry right (initLabels source.erase) localTarget)
    (selection : SourceEdgeSelection (initLabels source.erase) g root)
    (physical : BetaEdge g) (sameWord : leftWord=rightWord) :
    leftPaired.marker.sourceWord selection.atomWord physical.principal physical.reverseRoute=
      rightPaired.marker.sourceWord selection.atomWord physical.principal physical.reverseRoute := by
  obtain ⟨_leftTail,_rightTail,_leftKind,_rightKind,_firstLabels,markers,_fullTails⟩ :=
    left.compare_full_tails right sameWord
  have kinds := (global_leaf_marker_kind left).symm.trans (markers.trans (global_leaf_marker_kind right))
  rw [paired_leaf_marker_kind leftPaired,paired_leaf_marker_kind rightPaired]
  exact origin_marker_sourceWords selection.atomWord physical.principal physical.reverseRoute kinds

/-- Compare the actual FIRST+marker physical prefixes. This does not
compare the LAST/full tail or any unknown global continuation. -/
theorem paired_marker_physical_prefixes
    (left : DirectedMarkerLeafOutput F source degree forward ps leftWord)
    (right : DirectedMarkerLeafOutput F source degree forward ps rightWord)
    (leftPaired : PairedMarkerEventGeometry left (initLabels source.erase) localTarget)
    (rightPaired : PairedMarkerEventGeometry right (initLabels source.erase) localTarget)
    (matching : Matches g root source.erase)
    (selected : ∀name∈F,source.degreeAt name=some degree)
    (sourceSafe : source.OuterBarsSafe (fun x=>x≠degree))
    (prefixHistory : History prior original source) (initial : INIT original)
    (closed : Closed source.erase)
    (sourceSelection : OccurrenceFragmentSelection source g root)
    (representation : ChainRepresentationInvariant closed sourceSelection)
    (selection : SourceEdgeSelection (initLabels source.erase) g root)
    (physical : BetaEdge g) (sameWord : leftWord=rightWord) :
    orientPhysical forward (selection.evalLabel physical leftPaired.firstNode.label)++
        orientPhysical forward (leftPaired.marker.sourceWord selection.atomWord physical.principal physical.reverseRoute)=
      orientPhysical forward (selection.evalLabel physical rightPaired.firstNode.label)++
        orientPhysical forward (rightPaired.marker.sourceWord selection.atomWord physical.principal physical.reverseRoute) := by
  have first := paired_marker_first_oriented_evaluations left right leftPaired rightPaired
    matching selected sourceSafe prefixHistory initial closed sourceSelection representation selection physical sameWord
  have marker := paired_marker_route_evaluations left right leftPaired rightPaired selection physical sameWord
  rw [first,marker]
end
#print axioms global_leaf_marker_kind
#print axioms paired_leaf_marker_kind
#print axioms origin_marker_sourceWords
#print axioms paired_marker_route_evaluations
#print axioms paired_marker_physical_prefixes
end Lamping.AG
