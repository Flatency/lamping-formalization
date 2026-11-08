import Lamping.Lamping.PairedMarkerFirstComparison

namespace Lamping.AG
open Graph Lambda Lambda.Labelled

/-- Reflect only the FIRST SOURCE label, using two genuine complete SOURCE
chains and the common selected FUNCTION degree. Local atom identity and
creation-frame correspondence are not conclusions. -/
theorem paired_marker_first_source_labels_of_evaluations
    {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
    {g : Net signature N B W} {root : B}
    {F ps prior : List Path} {original source localTarget : LTerm}
    {degree : Label} {forward : Bool} {leftWord rightWord : List Letter}
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
    (physical : BetaEdge g)
    (sameFirstEvaluation :
      selection.evalLabel physical leftPaired.firstNode.label=
        selection.evalLabel physical rightPaired.firstNode.label) :
    left.firstNode.label=right.firstNode.label := by
  obtain ⟨ln,lr,lf,lo,lb,lc,lat,llab,lfn,ltrace,_lstart,_lfunction,lchain⟩ :=
    left.source_first_two_chain selected sourceSafe
  obtain ⟨rn,rr,rf,ro,rb,rc,rat,rlab,rfn,rtrace,_rstart,_rfunction,rchain⟩ :=
    right.source_first_two_chain selected sourceSafe
  obtain ⟨la,_ld,_larg,latRedex⟩ := LTerm.degreeAt_redex (selected ln lc)
  obtain ⟨ra,_rd,_rarg,ratRedex⟩ := LTerm.degreeAt_redex (selected rn rc)
  have lSingle := PrerequisiteChain.redex_lam latRedex
  have rSingle := PrerequisiteChain.redex_lam ratRedex
  have singleLabels : [ln++[.fn]].map source.labelAt=[rn++[.fn]].map source.labelAt := by
    simp only [List.map_cons,List.map_nil,LTerm.labelAt,lfn,rfn,Option.map_some,LTerm.label]
  have singletonIso := actual_chain_iso_of_labels prefixHistory initial closed lSingle rSingle singleLabels
  have singletonImages := (representation lSingle rSingle).mpr singletonIso
  let lfp : Position source.erase := ⟨ln++[.fn],by rw [←LTerm.erase_subterm,lfn];rfl⟩
  let rfp : Position source.erase := ⟨rn++[.fn],by rw [←LTerm.erase_subterm,rfn];rfl⟩
  have functionPieces := same_chain_representation_slot sourceSelection lSingle rSingle
    singletonImages lfp rfp (n:=0) rfl rfl
  let lp : Position source.erase := ⟨lf,by rw [←LTerm.erase_subterm,lat];rfl⟩
  let rp : Position source.erase := ⟨rf,by rw [←LTerm.erase_subterm,rat];rfl⟩
  obtain ⟨leftPosition,_leftNode,_leftLookup,leftTrace,leftEvaluation,_leftEmpty,_leftNonempty⟩ :=
    paired_marker_first_fragment left leftPaired matching selected sourceSelection selection physical
  obtain ⟨rightPosition,_rightNode,_rightLookup,rightTrace,rightEvaluation,_rightEmpty,_rightNonempty⟩ :=
    paired_marker_first_fragment right rightPaired matching selected sourceSelection selection physical
  have leftCoordinate : leftPosition=lp := Subtype.ext (leftTrace.unique ltrace)
  have rightCoordinate : rightPosition=rp := Subtype.ext (rightTrace.unique rtrace)
  rw [leftCoordinate] at leftEvaluation
  rw [rightCoordinate] at rightEvaluation
  have firstPieces := leftEvaluation.symm.trans (sameFirstEvaluation.trans rightEvaluation)
  have images : SameChainRepresentation sourceSelection lchain rchain := by
    apply List.ext_getElem
    · rw [canonicalChainImage_length,canonicalChainImage_length]
      rfl
    · intro i hi hj
      have bound : i<2 := by simpa only [canonicalChainImage_length,List.length_cons,List.length_nil] using hi
      have slots : (canonicalChainImage sourceSelection lchain)[i]?=
          (canonicalChainImage sourceSelection rchain)[i]? := by
        have cases : i=0 ∨ i=1 := by omega
        rcases cases with rfl | rfl
        · rw [canonical_chain_slot sourceSelection lchain lp (n:=0) rfl,
            canonical_chain_slot sourceSelection rchain rp (n:=0) rfl]
          exact congrArg some firstPieces
        · rw [canonical_chain_slot sourceSelection lchain lfp (n:=1) rfl,
            canonical_chain_slot sourceSelection rchain rfp (n:=1) rfl]
          exact congrArg some functionPieces
      exact Option.some.inj (by simpa only [List.getElem?_eq_getElem hi,List.getElem?_eq_getElem hj] using slots)
  obtain ⟨iso⟩ := (representation lchain rchain).mp images
  have allLabels := actual_chain_labels_forward prefixHistory initial closed lchain rchain iso
  have firstLabel : lo.label=ro.label := by
    have heads := congrArg List.head? allLabels
    simpa only [List.map_cons,List.head?_cons,LTerm.labelAt,lat,rat,Option.map_some,
      Option.some.injEq] using heads
  exact llab.symm.trans (firstLabel.trans rlab)

#print axioms paired_marker_first_source_labels_of_evaluations
end Lamping.AG
