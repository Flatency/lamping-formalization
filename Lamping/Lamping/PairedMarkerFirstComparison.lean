import Lamping.Lamping.PairedMarkerFirstFragment
import Lamping.Lambda.MarkerLeafSourceFirstChains
import Lamping.Lamping.ActualChainLabelConverse
import Lamping.Lamping.FanLambdaSlotSynchronization

namespace Lamping.AG
open Graph Lambda Lambda.Labelled
section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable {g : Net signature N B W} {root : B}

/-- Compare the physical FIRST blocks through TWO actual original-source
two-edge chains. Each FIRST coordinate is aligned only with its OWN event
trace. Source REP is a legitimate induction hypothesis, not asserted truth. -/
theorem paired_marker_first_evaluations
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
    selection.evalLabel physical leftPaired.firstNode.label=
      selection.evalLabel physical rightPaired.firstNode.label := by
  obtain ⟨ln,rn,lr,rr,lf,rf,lo,ro,_lc,_rc,lat,rat,lTrace,rTrace,_lFunction,_rFunction,
      lChain,rChain,_firstLabels,labels⟩ := left.compare_source_first_two_chains right selected sourceSafe sameWord
  have iso := actual_chain_iso_of_labels prefixHistory initial closed lChain rChain labels
  have images : SameChainRepresentation sourceSelection lChain rChain := (representation lChain rChain).mpr iso
  let lp : Position source.erase := ⟨lf,by rw [←LTerm.erase_subterm,lat];rfl⟩
  let rp : Position source.erase := ⟨rf,by rw [←LTerm.erase_subterm,rat];rfl⟩
  have lSlot : ([lf,ln++[.fn]] : List Path)[0]?=some lp.val := rfl
  have rSlot : ([rf,rn++[.fn]] : List Path)[0]?=some rp.val := rfl
  have pieces := same_chain_representation_slot sourceSelection lChain rChain images lp rp lSlot rSlot
  obtain ⟨leftPosition,leftNode,_leftLookup,leftTrace,leftEvaluation,_leftEmpty,_leftNonempty⟩ :=
    paired_marker_first_fragment left leftPaired matching selected sourceSelection selection physical
  obtain ⟨rightPosition,rightNode,_rightLookup,rightTrace,rightEvaluation,_rightEmpty,_rightNonempty⟩ :=
    paired_marker_first_fragment right rightPaired matching selected sourceSelection selection physical
  have leftCoordinate : leftPosition=lp := Subtype.ext (leftTrace.unique lTrace)
  have rightCoordinate : rightPosition=rp := Subtype.ext (rightTrace.unique rTrace)
  rw [leftCoordinate] at leftEvaluation
  rw [rightCoordinate] at rightEvaluation
  exact leftEvaluation.trans (pieces.trans rightEvaluation.symm)
end
#print axioms paired_marker_first_evaluations
end Lamping.AG
