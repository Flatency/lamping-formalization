import Lamping.Lamping.WholeSpineNearBoundary
import Lamping.Lamping.WritingLetterBlocks
import Lamping.Lamping.PairedMarkerFirstSourceReflection

namespace Lamping.AG
open Graph Lambda Lambda.Labelled

theorem EvaluatedChainResiduals.given_true_spine_first_source_labels
    {K B W V : Type}
    [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
    {kept : K → Graph.Label signature} {i : Nat}
    (site : PathSite (.beta i) kept (B:=B) (W:=W) (V:=V))
    {root : B} {original source target localTarget leftCurrent rightCurrent : LTerm}
    {F ps prior : List Path} {degree : Label}
    {edge : BetaEdge site.net}
    {selection : SourceEdgeSelection (initLabels source.erase) site.net root}
    {targetSelection : OccurrenceFragmentSelection target site.reduce root}
    {ls rs : Path} {les res : List Path}
    {leftChain : PrerequisiteChain target ls les}
    {rightChain : PrerequisiteChain target rs res}
    (leftMember : {p : Path //p∈les}) (rightMember : {p : Path //p∈res})
    {ordinal : Nat}
    (leftAt : les[ordinal]?=some leftMember.val)
    (rightAt : res[ordinal]?=some rightMember.val)
    {leftBefore rightBefore : List (Option Label)}
    {leftSpine : DirectedMarkerSpine F source degree true ps target leftBefore leftMember.val}
    {rightSpine : DirectedMarkerSpine F source degree true ps target rightBefore rightMember.val}
    {leftLookup : target.subterm leftMember.val=some leftCurrent}
    {rightLookup : target.subterm rightMember.val=some rightCurrent}
    {leftLeaf : DirectedMarkerLeafOutput F source degree true ps (leftCurrent.label.readLetters true)}
    {rightLeaf : DirectedMarkerLeafOutput F source degree true ps (rightCurrent.label.readLetters true)}
    {leftSnapshot : IncomingIncidenceSnapshot target leftMember.val}
    {rightSnapshot : IncomingIncidenceSnapshot target rightMember.val}
    {leftGeometry : SpineIncidenceProvenance F source degree true leftSpine leftLookup leftLeaf leftSnapshot}
    {rightGeometry : SpineIncidenceProvenance F source degree true rightSpine rightLookup rightLeaf rightSnapshot}
    {localHistory : History ps (initLabels source.erase) localTarget}
    (leftPair : PairedSpineReannotation leftGeometry localHistory (erase_initLabels source.erase).symm)
    (rightPair : PairedSpineReannotation rightGeometry localHistory (erase_initLabels source.erase).symm)
    (matching : Matches site.net root source.erase)
    (selected : ∀name∈F,source.degreeAt name=some degree)
    (sourceSafe : source.OuterBarsSafe (fun d=>d≠degree))
    (prefixHistory : History prior original source) (initial : INIT original)
    (closed : Closed source.erase)
    (sourceSelection : OccurrenceFragmentSelection source site.net root)
    (representation : ChainRepresentationInvariant closed sourceSelection)
    (geometry : SiteBetaGeometry site edge)
    (left : EvaluatedChainResiduals site (localTarget:=localTarget) edge selection targetSelection leftChain)
    (right : EvaluatedChainResiduals site (localTarget:=localTarget) edge selection targetSelection rightChain)
    (same : SameChainRepresentation targetSelection leftChain rightChain) :
    leftLeaf.firstNode.label=rightLeaf.firstNode.label := by
  have blocks := left.blocks_eq_of_target_images site geometry right same
  have lb : ordinal<les.length := List.getElem?_eq_some_iff.mp leftAt |>.1
  have rb : ordinal<res.length := List.getElem?_eq_some_iff.mp rightAt |>.1
  have lab : ordinal<les.attach.length := by simpa using lb
  have rab : ordinal<res.attach.length := by simpa using rb
  have lm : les.attach[ordinal]=leftMember := by
    apply Subtype.ext
    simpa only [List.getElem_attach] using (List.getElem?_eq_some_iff.mp leftAt).2
  have rm : res.attach[ordinal]=rightMember := by
    apply Subtype.ext
    simpa only [List.getElem_attach] using (List.getElem?_eq_some_iff.mp rightAt).2
  have slot : selection.evalLabel edge (left.node leftMember).label=
      selection.evalLabel edge (right.node rightMember).label := by
    have atSlot := congrArg (fun xs : List (List (Endpoint site.net))=>xs[ordinal]?) blocks
    simpa only [EvaluatedChainResiduals.blocks,List.getElem?_map,List.getElem?_eq_getElem lab,
      List.getElem?_eq_getElem rab,Option.map_some,Option.some.injEq,lm,rm] using atSlot
  have leftCurrentEq : left.node leftMember=leftPair.current :=
    Option.some.inj ((left.lookup leftMember).symm.trans leftPair.currentLookup)
  have rightCurrentEq : right.node rightMember=rightPair.current :=
    Option.some.inj ((right.lookup rightMember).symm.trans rightPair.currentLookup)
  have lr := left.writing_letter_blocks_regular site (init_is_INIT source.erase) localHistory leftMember
  have rr := right.writing_letter_blocks_regular site (init_is_INIT source.erase) localHistory rightMember
  have perLetter := proper_ended_control_blocks_unique lr.2.2 rr.2.2
    (lr.2.1.trans (slot.trans rr.2.1.symm))
  obtain ⟨ln⟩ := Lamping.AG.PairedSpineReannotation.near_first_atom leftPair selected
  obtain ⟨rn⟩ := Lamping.AG.PairedSpineReannotation.near_first_atom rightPair selected
  have lw : (left.node leftMember).label.letters=
      [.atom ln.atom]++ln.baseTail++leftPair.localTailPieces.flatten := by
    simpa only [Label.readLetters,if_true] using leftCurrentEq ▸ ln.word
  have rw : (right.node rightMember).label.letters=
      [.atom rn.atom]++rn.baseTail++rightPair.localTailPieces.flatten := by
    simpa only [Label.readLetters,if_true] using rightCurrentEq ▸ rn.word
  have first : selection.atomWord ln.atom=selection.atomWord rn.atom := by
    have heads := congrArg List.head? perLetter
    simpa only [lw,rw,List.singleton_append,List.cons_append,List.map_cons,List.head?_cons,
      Letter.sourceWord,Option.some.injEq] using heads
  apply paired_marker_first_source_labels_of_evaluations leftLeaf rightLeaf leftPair.base rightPair.base
    matching selected sourceSafe prefixHistory initial closed sourceSelection representation selection edge
  rw [ln.firstAtomic,rn.firstAtomic]
  exact first

#print axioms EvaluatedChainResiduals.given_true_spine_first_source_labels

end Lamping.AG

