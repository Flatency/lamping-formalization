import Lamping.Lamping.WholeSpineNearBoundary
import Lamping.Lambda.UniformOldOuterImageAlignment
import Lamping.Lamping.PairedMarkerFirstComparison

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
variable {pair : PairedSpineReannotation geometry localHistory (erase_initLabels source.erase).symm}

/-- The full original image is recovered at THIS actual old coordinate. -/
theorem SpineNearFirstAtom.original_full_image (near : SpineNearFirstAtom pair) :
    near.oldNode.label=initialRelabelling source 0 near.atom := by
  let s:=initialRelabelling source 0
  have basis : ((initLabels source.erase).relabel s).subterm near.position.val=
      some (near.basisNode.relabel s) := by
    rw [LTerm.subterm_relabel,near.basisLookup];rfl
  have factor : (initLabels source.erase).relabel s=source:=initialRelabelling_factor source 0
  rw [factor,near.oldLookup] at basis
  have same : near.oldNode=near.basisNode.relabel s:=Option.some.inj basis
  calc
    near.oldNode.label=(near.basisNode.relabel s).label:=congrArg LTerm.label same
    _=near.basisNode.label.relabel s:=by cases near.basisNode <;> rfl
    _=initialRelabelling source 0 near.atom:=by rw [near.basisAtomic];rfl
end

section
variable {source leftTarget rightTarget leftLocalTarget rightLocalTarget leftCurrent rightCurrent : LTerm}
variable {F leftPs rightPs : List Path} {degree : Lambda.Labelled.Label} {forward : Bool}
variable {leftBefore rightBefore : List (Option Lambda.Labelled.Label)} {lp rp : Path}
variable {leftSpine : DirectedMarkerSpine F source degree forward leftPs leftTarget leftBefore lp}
variable {rightSpine : DirectedMarkerSpine F source degree forward rightPs rightTarget rightBefore rp}
variable {leftLookup : leftTarget.subterm lp=some leftCurrent}
variable {rightLookup : rightTarget.subterm rp=some rightCurrent}
variable {leftLeaf : DirectedMarkerLeafOutput F source degree forward leftPs (leftCurrent.label.readLetters forward)}
variable {rightLeaf : DirectedMarkerLeafOutput F source degree forward rightPs (rightCurrent.label.readLetters forward)}
variable {leftSnapshot : IncomingIncidenceSnapshot leftTarget lp}
variable {rightSnapshot : IncomingIncidenceSnapshot rightTarget rp}
variable {leftGeometry : SpineIncidenceProvenance F source degree forward leftSpine leftLookup leftLeaf leftSnapshot}
variable {rightGeometry : SpineIncidenceProvenance F source degree forward rightSpine rightLookup rightLeaf rightSnapshot}
variable {leftHistory : History leftPs (initLabels source.erase) leftLocalTarget}
variable {rightHistory : History rightPs (initLabels source.erase) rightLocalTarget}
variable (leftPair : PairedSpineReannotation leftGeometry leftHistory (erase_initLabels source.erase).symm)
variable (rightPair : PairedSpineReannotation rightGeometry rightHistory (erase_initLabels source.erase).symm)
variable (leftNear : SpineNearFirstAtom leftPair) (rightNear : SpineNearFirstAtom rightPair)
variable {leftMarked rightMarked : Marked}

/-- Equal CURRENT heads align their first opaque SOURCE images; their earliest
leaf words and their chronological frame lists are not identified. -/
theorem paired_spine_near_source_images
    (leftOld : Marked.RelativeOldHistory F leftPs (Marked.mark F source.erase) leftMarked)
    (rightOld : Marked.RelativeOldHistory F rightPs (Marked.mark F source.erase) rightMarked)
    (leftLabels : History leftPs source leftTarget) (rightLabels : History rightPs source rightTarget)
    (selected : ∀name∈F,source.degreeAt name=some degree)
    (sourceSafe : source.OuterBarsSafe (fun x=>x≠degree))
    (sameCurrent : leftCurrent.label=rightCurrent.label) :
    initialRelabelling source 0 leftNear.atom=initialRelabelling source 0 rightNear.atom := by
  have keys:=leftOld.local_outer_image_alignment rightOld leftLabels rightLabels
    leftHistory rightHistory selected sourceSafe leftLookup rightLookup
    leftPair.currentLookup rightPair.currentLookup sameCurrent
  have directed :
      (leftPair.current.label.readLetters forward).map (Letter.outerImageKey (initialRelabelling source 0))=
      (rightPair.current.label.readLetters forward).map (Letter.outerImageKey (initialRelabelling source 0)) := by
    cases forward with
    | true => exact keys
    | false => simpa only [Label.readLetters,Bool.false_eq_true,if_false,List.map_reverse] using congrArg List.reverse keys
  rw [leftNear.word,rightNear.word] at directed
  simp only [List.map_append,List.map_cons,List.singleton_append] at directed
  exact Sum.inl.inj (List.cons.inj directed).1

variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable {g : Net signature N B W} {root : B}

/-- Two independently supplied real SOURCE two-edge chains compare the near
blocks using only honest SOURCE REP, never equal earliest leaf words. -/
theorem paired_spine_near_evaluations
    (leftOld : Marked.RelativeOldHistory F leftPs (Marked.mark F source.erase) leftMarked)
    (rightOld : Marked.RelativeOldHistory F rightPs (Marked.mark F source.erase) rightMarked)
    (leftLabels : History leftPs source leftTarget) (rightLabels : History rightPs source rightTarget)
    (selected : ∀name∈F,source.degreeAt name=some degree)
    (sourceSafe : source.OuterBarsSafe (fun x=>x≠degree))
    (sameCurrent : leftCurrent.label=rightCurrent.label)
    {prior : List Path} {original : LTerm}
    (prefixHistory : History prior original source) (initial : INIT original)
    (closed : Closed source.erase) (matching : Matches g root source.erase)
    (sourceSelection : OccurrenceFragmentSelection source g root)
    (representation : ChainRepresentationInvariant closed sourceSelection)
    (selection : SourceEdgeSelection (initLabels source.erase) g root) (physical : BetaEdge g) :
    selection.atomWord leftNear.atom=selection.atomWord rightNear.atom ∧
      (sourceSelection leftNear.position).fragment.segments=(sourceSelection rightNear.position).fragment.segments ∧
      orientPhysical forward (selection.evalLabel physical leftPair.base.firstNode.label)=
        orientPhysical forward (selection.evalLabel physical rightPair.base.firstNode.label) := by
  have imageEq:=paired_spine_near_source_images leftPair rightPair leftNear rightNear
    leftOld rightOld leftLabels rightLabels selected sourceSafe sameCurrent
  have oldLabel : leftNear.oldNode.label=rightNear.oldNode.label:=
    leftNear.original_full_image.trans (imageEq.trans rightNear.original_full_image.symm)
  obtain ⟨ln,lr,lf,lo,lb,lc,lat,llab,lfn,ltrace,_lstart,_lfunction,lchain⟩:=
    leftLeaf.source_first_two_chain selected sourceSafe
  obtain ⟨rn,rr,rf,ro,rb,rc,rat,rlab,rfn,rtrace,_rstart,_rfunction,rchain⟩:=
    rightLeaf.source_first_two_chain selected sourceSafe
  have leftAt : leftNear.position.val=lf:=leftNear.trace.unique ltrace
  have rightAt : rightNear.position.val=rf:=rightNear.trace.unique rtrace
  have leftNodeEq : leftNear.oldNode=lo:=by
    have atNear:=leftNear.oldLookup
    rw [leftAt,lat] at atNear
    exact (Option.some.inj atNear).symm
  have rightNodeEq : rightNear.oldNode=ro:=by
    have atNear:=rightNear.oldLookup
    rw [rightAt,rat] at atNear
    exact (Option.some.inj atNear).symm
  have labels : [lf,ln++[.fn]].map source.labelAt=[rf,rn++[.fn]].map source.labelAt:=by
    simp only [List.map_cons,List.map_nil,LTerm.labelAt,lat,rat,lfn,rfn,Option.map_some]
    change [some lo.label,some degree]=[some ro.label,some degree]
    rw [←leftNodeEq,←rightNodeEq,oldLabel]
  have iso:=actual_chain_iso_of_labels prefixHistory initial closed lchain rchain labels
  have whole:SameChainRepresentation sourceSelection lchain rchain:=(representation lchain rchain).mpr iso
  have lpSlot : ([lf,ln++[.fn]] : List Path)[0]?=some leftNear.position.val:=by rw [leftAt];rfl
  have rpSlot : ([rf,rn++[.fn]] : List Path)[0]?=some rightNear.position.val:=by rw [rightAt];rfl
  have pieces:=same_chain_representation_slot sourceSelection lchain rchain whole leftNear.position rightNear.position lpSlot rpSlot
  obtain ⟨leftPhysical⟩:=Lamping.AG.PairedSpineReannotation.physical_near_boundary leftPair selected matching sourceSelection selection physical
  obtain ⟨rightPhysical⟩:=Lamping.AG.PairedSpineReannotation.physical_near_boundary rightPair selected matching sourceSelection selection physical
  have leftSame : leftPhysical.first.position=leftNear.position:=
    Subtype.ext (leftPhysical.first.trace.unique leftNear.trace)
  have rightSame : rightPhysical.first.position=rightNear.position:=
    Subtype.ext (rightPhysical.first.trace.unique rightNear.trace)
  have leftAtom : leftPhysical.first.atom=leftNear.atom:=by
    have a:=leftPhysical.first.firstAtomic
    rw [leftNear.firstAtomic] at a
    simpa only [Label.atom,Label.single.injEq,Letter.atom.injEq] using a.symm
  have rightAtom : rightPhysical.first.atom=rightNear.atom:=by
    have a:=rightPhysical.first.firstAtomic
    rw [rightNear.firstAtomic] at a
    simpa only [Label.atom,Label.single.injEq,Letter.atom.injEq] using a.symm
  have leftPiece : (sourceSelection leftPhysical.first.position).fragment.segments=
      (sourceSelection leftNear.position).fragment.segments:=
    congrArg (fun position : Position source.erase=>(sourceSelection position).fragment.segments) leftSame
  have rightPiece : (sourceSelection rightPhysical.first.position).fragment.segments=
      (sourceSelection rightNear.position).fragment.segments:=
    congrArg (fun position : Position source.erase=>(sourceSelection position).fragment.segments) rightSame
  have leftValue : selection.atomWord leftNear.atom=(sourceSelection leftNear.position).fragment.segments:=
    (congrArg selection.atomWord leftAtom.symm).trans (leftPhysical.atomValue.trans leftPiece)
  have rightValue : selection.atomWord rightNear.atom=(sourceSelection rightNear.position).fragment.segments:=
    (congrArg selection.atomWord rightAtom.symm).trans (rightPhysical.atomValue.trans rightPiece)
  refine ⟨leftValue.trans (pieces.trans rightValue.symm),pieces,?_⟩
  have leftFirst : selection.evalLabel physical leftPair.base.firstNode.label=(sourceSelection leftNear.position).fragment.segments:=
    leftPhysical.firstValue.trans leftPiece
  have rightFirst : selection.evalLabel physical rightPair.base.firstNode.label=(sourceSelection rightNear.position).fragment.segments:=
    rightPhysical.firstValue.trans rightPiece
  rw [leftFirst,rightFirst,pieces]
end

#print axioms SpineNearFirstAtom.original_full_image
#print axioms paired_spine_near_source_images
#print axioms paired_spine_near_evaluations
end Lamping.AG
