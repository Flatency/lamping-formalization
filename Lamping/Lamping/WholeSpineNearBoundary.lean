import Lamping.Lamping.SpinePhysicalEvaluation
namespace Lamping.AG
open Graph Lambda Lambda.Labelled
section
variable {source target localTarget current : LTerm} {F ps : List Path} {degree : Lambda.Labelled.Label}
variable {forward : Bool} {before : List (Option Lambda.Labelled.Label)} {p : Path}
variable {spine : DirectedMarkerSpine F source degree forward ps target before p}
variable {lookup : target.subterm p=some current}
variable {leaf : DirectedMarkerLeafOutput F source degree forward ps (current.label.readLetters forward)}
variable {snapshot : IncomingIncidenceSnapshot target p}
variable {geometry : SpineIncidenceProvenance F source degree forward spine lookup leaf snapshot}
variable {localHistory : History ps (initLabels source.erase) localTarget}
/-- Derived coordinates and the whole reading prefix for THIS reannotation. -/
structure SpineNearFirstAtom
    (pair : PairedSpineReannotation geometry localHistory (erase_initLabels source.erase).symm) where
  position : Position source.erase
  oldNode : LTerm
  basisNode : LTerm
  atom : Nat
  oldLookup : source.subterm position.val=some oldNode
  basisLookup : (initLabels source.erase).subterm position.val=some basisNode
  trace : BetaNodeHistoryPreimage leaf.event.labels leaf.first position.val
  oldLabel : oldNode.label=leaf.firstNode.label
  basisAtomic : basisNode.label=Lambda.Labelled.Label.atom atom
  firstAtomic : pair.base.firstNode.label=Lambda.Labelled.Label.atom atom
  baseTail : List Letter
  tailSpec : SpineReannotation.TailSpecification pair.base.middle leaf.site pair.base.alpha forward
    pair.base.lastNode pair.base.marker baseTail
  word : pair.current.label.readLetters forward=[.atom atom]++baseTail++pair.localTailPieces.flatten

/-- Safe earliest FIRST is an actual atom of the local INIT basis. Later
frames remain the exact chronological tails, in either reading direction. -/
theorem PairedSpineReannotation.near_first_atom
    (pair : PairedSpineReannotation geometry localHistory (erase_initLabels source.erase).symm)
    (selected : ∀name∈F,source.degreeAt name=some degree) : Nonempty (SpineNearFirstAtom pair) := by
  obtain ⟨oldPosition,oldNode,basisNode,oldLookup,basisLookup,oldLabel,localLabel,trace⟩:=
    leaf.event.beforeOld.marker_free_paired_origin (DegreeAligned.initial source F) leaf.event.labels
      pair.base.prefixLabels (erase_initLabels source.erase).symm selected
      leaf.firstLookup pair.base.firstLookup leaf.firstSafe
  obtain ⟨n,atomic⟩:=(init_is_INIT source.erase).1 _ (LTerm.label_mem_of_subterm basisLookup)
  let position : Position source.erase:=⟨oldPosition,by rw [←LTerm.erase_subterm,oldLookup];rfl⟩
  have firstAtomic : pair.base.firstNode.label=Lambda.Labelled.Label.atom n:=localLabel.symm.trans atomic
  obtain ⟨tail,spec,equation⟩:=SpineReannotation.full_tail pair.base.formula
  have whole:=pair.wordFold
  rw [equation,firstAtomic] at whole
  have atomRead : (Lambda.Labelled.Label.atom n).readLetters forward=[Letter.atom n]:=by cases forward <;> rfl
  rw [atomRead] at whole
  exact ⟨⟨position,oldNode,basisNode,n,oldLookup,basisLookup,trace,oldLabel,atomic,firstAtomic,tail,spec,whole⟩⟩
end
section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable {g : Net signature N B W} {root : B}
variable {source target localTarget current : LTerm} {F ps : List Path} {degree : Lambda.Labelled.Label}
variable {forward : Bool} {before : List (Option Lambda.Labelled.Label)} {p : Path}
variable {spine : DirectedMarkerSpine F source degree forward ps target before p}
variable {lookup : target.subterm p=some current}
variable {leaf : DirectedMarkerLeafOutput F source degree forward ps (current.label.readLetters forward)}
variable {snapshot : IncomingIncidenceSnapshot target p}
variable {geometry : SpineIncidenceProvenance F source degree forward spine lookup leaf snapshot}
variable {localHistory : History ps (initLabels source.erase) localTarget}

structure SpinePhysicalNearBoundary
    (pair : PairedSpineReannotation geometry localHistory (erase_initLabels source.erase).symm)
    (sourceSelection : OccurrenceFragmentSelection source g root)
    (selection : SourceEdgeSelection (initLabels source.erase) g root) (physical : BetaEdge g) where
  first : SpineNearFirstAtom pair
  atomValue : selection.atomWord first.atom=(sourceSelection first.position).fragment.segments
  firstValue : selection.evalLabel physical pair.base.firstNode.label=
    (sourceSelection first.position).fragment.segments
  full : orientPhysical forward (selection.evalLabel physical pair.current.label)=
    orientPhysical forward ((sourceSelection first.position).fragment.segments)++
      interpretReadLetters selection.atomWord physical.principal physical.reverseRoute forward
        (first.baseTail++pair.localTailPieces.flatten)
  nonempty : orientPhysical forward ((sourceSelection first.position).fragment.segments)≠[]
  head : (orientPhysical forward (selection.evalLabel physical pair.current.label)).head?=
    (orientPhysical forward ((sourceSelection first.position).fragment.segments)).head?

private theorem orient_nonempty (d : Bool) {xs : List (Endpoint g)} (positive : xs≠[]) :
    orientPhysical d xs≠[] := by
  cases d with
  | true => exact positive
  | false =>
    intro empty
    have length:=congrArg List.length empty
    simp only [orientPhysical,Bool.false_eq_true,if_false,reverseEdges,List.length_map,List.length_reverse,List.length_nil] at length
    exact positive (List.length_eq_zero_iff.mp length)

theorem PairedSpineReannotation.physical_near_boundary
    (pair : PairedSpineReannotation geometry localHistory (erase_initLabels source.erase).symm)
    (selected : ∀name∈F,source.degreeAt name=some degree)
    (matching : Matches g root source.erase)
    (sourceSelection : OccurrenceFragmentSelection source g root)
    (selection : SourceEdgeSelection (initLabels source.erase) g root) (physical : BetaEdge g) :
    Nonempty (SpinePhysicalNearBoundary pair sourceSelection selection physical) := by
  obtain ⟨first⟩:=Lamping.AG.PairedSpineReannotation.near_first_atom pair selected
  obtain ⟨env,ctx,occurrence⟩:=SourceSubterm.of_lookup (initLabels source.erase) first.basisLookup [] .external
  have localMatching : Matches g root (initLabels source.erase).erase:=by simpa only [erase_initLabels] using matching
  have atomValue:=selection.atomWord_occurrence_segments (init_is_INIT _) localMatching matching
    occurrence first.basisAtomic (sourceSelection first.position)
  have firstValue : selection.evalLabel physical pair.base.firstNode.label=(sourceSelection first.position).fragment.segments:=by
    rw [first.firstAtomic]
    exact atomValue
  have physicalWord:=congrArg (interpretReadLetters selection.atomWord physical.principal physical.reverseRoute forward) first.word
  have full : orientPhysical forward (selection.evalLabel physical pair.current.label)=
      orientPhysical forward ((sourceSelection first.position).fragment.segments)++
        interpretReadLetters selection.atomWord physical.principal physical.reverseRoute forward
          (first.baseTail++pair.localTailPieces.flatten) := by
    rw [SourceEdgeSelection.interpret_read_label] at physicalWord
    simp only [interpretReadLetters_append] at physicalWord
    have one : interpretReadLetters selection.atomWord physical.principal physical.reverseRoute forward [.atom first.atom]=
        orientPhysical forward (selection.atomWord first.atom):=by
      simp only [interpretReadLetters,List.flatMap_cons,List.flatMap_nil,Letter.sourceWord,List.append_nil]
    rw [one,atomValue] at physicalWord
    simpa only [interpretReadLetters_append,List.append_assoc] using physicalWord
  have fragmentNonempty : (sourceSelection first.position).fragment.segments≠[]:=by
    intro empty
    have start:=(sourceSelection first.position).fragment.start
    rw [empty] at start;cases start
  have nonempty:=orient_nonempty forward fragmentNonempty
  have head : (orientPhysical forward (selection.evalLabel physical pair.current.label)).head?=
      (orientPhysical forward ((sourceSelection first.position).fragment.segments)).head? :=by
    rw [full]
    cases h : orientPhysical forward ((sourceSelection first.position).fragment.segments) with
    | nil => exact False.elim (nonempty h)
    | cons a rest => rfl
  exact ⟨⟨first,atomValue,firstValue,full,nonempty,head⟩⟩
end
section
variable {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K→Graph.Label signature} {i : Nat}
variable {site : PathSite (.beta i) kept (B:=B) (W:=W) (V:=V)}
/-- No producer or reannotation is rerun: both are GIVEN and share ONE
history, physical edge, selector and actual complete-chain member. -/
theorem EvaluatedChainResiduals.given_spine_near_boundary
    {root : B} {source target localTarget current : LTerm} {ps F : List Path}
    {degree : Lambda.Labelled.Label} {forward : Bool} {start : Path} {es : List Path}
    {chain : PrerequisiteChain target start es} (member : {p : Path // p∈es})
    {before : List (Option Lambda.Labelled.Label)}
    {spine : DirectedMarkerSpine F source degree forward ps target before member.val}
    {lookup : target.subterm member.val=some current}
    {leaf : DirectedMarkerLeafOutput F source degree forward ps (current.label.readLetters forward)}
    {snapshot : IncomingIncidenceSnapshot target member.val}
    {geometry : SpineIncidenceProvenance F source degree forward spine lookup leaf snapshot}
    {localHistory : History ps (initLabels source.erase) localTarget}
    (pair : PairedSpineReannotation geometry localHistory (erase_initLabels source.erase).symm)
    (selected : ∀name∈F,source.degreeAt name=some degree)
    (matching : Matches site.net root source.erase)
    (sourceSelection : OccurrenceFragmentSelection source site.net root)
    {edge : BetaEdge site.net}
    {selection : SourceEdgeSelection (initLabels source.erase) site.net root}
    {targetSelection : OccurrenceFragmentSelection target site.reduce root}
    (evaluation : EvaluatedChainResiduals site (localTarget:=localTarget) edge selection targetSelection chain) :
    ∃near : SpinePhysicalNearBoundary pair sourceSelection selection edge,
      evaluation.node member=pair.current ∧
      (orientPhysical forward (selection.evalLabel edge (evaluation.node member).label)).head?=
        (orientPhysical forward ((sourceSelection near.first.position).fragment.segments)).head? ∧
      BetaPathResidual site edge
        ((targetSelection (actualChainPosition chain member)).fragment.segments.map (plugEnd _ _).invFun)
        (selection.evalLabel edge (evaluation.node member).label) ∧
      selection.evalLabel edge (evaluation.node member).label≠[] := by
  obtain ⟨near⟩:=Lamping.AG.PairedSpineReannotation.physical_near_boundary pair selected matching sourceSelection selection edge
  have same : evaluation.node member=pair.current:=Option.some.inj ((evaluation.lookup member).symm.trans pair.currentLookup)
  exact ⟨near,same,by rw [same];exact near.head,evaluation.residual member,evaluation.nonempty member⟩
end
end Lamping.AG
