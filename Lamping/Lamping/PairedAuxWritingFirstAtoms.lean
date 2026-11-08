import Lamping.Lambda.AuxWritingFirstAtomOrigin
import Lamping.Lamping.AuxiliaryEndpointReflection
namespace Lamping.AG
open Graph Lambda Lambda.Labelled
open SyntaxIncidence InteriorSourceBlock

/-- Compare the actual writing-FIRST blocks. Only the CURRENT source iso is
needed: each original arrival is an actual selected APP or selected binder. -/
theorem paired_aux_writing_first_atom_words
    {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
    {g : Net signature N B W} {root : B}
    {original source current localTarget : LTerm}
    {leftNode rightNode leftLocal rightLocal : LTerm}
    {prior ps F : List Path} {degree : Lambda.Labelled.Label} {marked : Marked}
    {leftAtom rightAtom : Nat} {leftKind rightKind : Bool}
    {leftPayload rightPayload : Lambda.Labelled.Label}
    {leftTail rightTail : List Letter}
    (initial : INIT original)
    (prefixHistory : History prior original source)
    (old : Marked.RelativeOldHistory F ps (Marked.mark F source.erase) marked)
    (labels : History ps source current)
    (localHistory : History ps (initLabels source.erase) localTarget)
    (selected : ∀name∈F,source.degreeAt name=some degree)
    (sourceSafe : source.OuterBarsSafe (fun payload=>payload≠degree))
    (closed : Closed source.erase)
    (left right : SyntaxIncidence.Edge current)
    (leftLookup : current.subterm left.val=some leftNode)
    (rightLookup : current.subterm right.val=some rightNode)
    (leftAux : AuxiliaryAt current left.val)
    (rightAux : AuxiliaryAt current right.val)
    (sameLabel : SyntaxIncidence.label current left=SyntaxIncidence.label current right)
    (leftLocalLookup : localTarget.subterm left.val=some leftLocal)
    (rightLocalLookup : localTarget.subterm right.val=some rightLocal)
    (leftWindow : leftLocal.label.letters=
       [.atom leftAtom,bar leftKind leftPayload]++leftTail)
    (rightWindow : rightLocal.label.letters=
       [.atom rightAtom,bar rightKind rightPayload]++rightTail)
    (currentSourceIso : SuccessfulEndpointIso current (labels.closed closed)
       (SyntaxIncidence.source current left) (SyntaxIncidence.source current right))
    (matching : Matches g root source.erase)
    (sourceSelection : OccurrenceFragmentSelection source g root)
    (sourceAux : AuxiliarySeparation closed sourceSelection)
    (selection : SourceEdgeSelection (initLabels source.erase) g root) :
    selection.atomWord leftAtom=selection.atomWord rightAtom := by
  have nodeEq : leftNode.label=rightNode.label := by
    rw [SyntaxIncidence.label_of_lookup current left leftLookup,
      SyntaxIncidence.label_of_lookup current right rightLookup] at sameLabel
    exact sameLabel
  obtain ⟨lp,lpEq⟩ : ∃lp : ProperPosition current,SyntaxIncidence.source current left=some lp := by
    cases atSource : SyntaxIncidence.source current left with
    | none =>
      obtain ⟨es,available⟩:=currentSourceIso.left_available
      rw [atSource] at available
      exact False.elim available
    | some p => exact ⟨p,rfl⟩
  obtain ⟨rp,rpEq⟩ : ∃rp : ProperPosition current,SyntaxIncidence.source current right=some rp := by
    cases atSource : SyntaxIncidence.source current right with
    | none =>
      obtain ⟨es,available⟩:=currentSourceIso.right_available
      rw [atSource] at available
      exact False.elim available
    | some p => exact ⟨p,rfl⟩
  have lsSpec : Source current left.val (some lp):=lpEq ▸ SyntaxIncidence.source_spec current left
  have rsSpec : Source current right.val (some rp):=rpEq ▸ SyntaxIncidence.source_spec current right
  obtain ⟨oldLP,lpTrace,lpos,lenv,lctx,lbasis,locc,latom,lold,laux,lselected,lsource,ltarget⟩:=
    aux_writing_first_atom_origin old labels localHistory leftLookup leftAux leftLocalLookup leftWindow lp lsSpec
  obtain ⟨oldRP,rpTrace,rpos,renv,rctx,rbasis,rocc,ratom,rold,raux,rselected,rsource,rtarget⟩:=
    aux_writing_first_atom_origin old labels localHistory rightLookup rightAux rightLocalLookup rightWindow rp rsSpec
  have sameKind : ∃kind,ProperKind current lp kind ∧ProperKind current rp kind := by
    obtain ⟨ls,lr,lk⟩:=Lambda.Labelled.Source.actual_kind lsSpec
    obtain ⟨rs,rr,rk⟩:=Lambda.Labelled.Source.actual_kind rsSpec
    have role:=(prefixHistory.append labels).incoming_role_eq_of_label initial leftLookup rightLookup nodeEq
    have steps : ls=rs:=Option.some.inj (lr.symm.trans (role.trans rr))
    exact ⟨departureApp ls,lk,by simpa only [←steps] using rk⟩
  rw [lpEq,rpEq] at currentSourceIso
  obtain ⟨les,res,lc,rc,iso⟩:=currentSourceIso
  have oldParentIso:=same_kind_old_endpoint_iso initial prefixHistory old labels selected sourceSafe
    closed (labels.closed closed) lp rp oldLP oldRP lpTrace rpTrace lc rc iso sameKind
  have keys:=old.local_outer_image_alignment old labels labels localHistory localHistory
    selected sourceSafe leftLookup rightLookup leftLocalLookup rightLocalLookup nodeEq
  rw [leftWindow,rightWindow] at keys
  simp only [List.map_cons,List.cons_append,List.nil_append] at keys
  have firstEq := (List.cons.inj keys).1
  have barEq := (List.cons.inj (List.cons.inj keys).2).1
  have imageEq : initialRelabelling source 0 leftAtom=initialRelabelling source 0 rightAtom := Sum.inl.inj firstEq
  have kindEq : leftKind=rightKind := by
    cases leftKind <;> cases rightKind <;> simp_all [bar,Letter.outerImageKey]
  let le : SyntaxIncidence.Edge source:=⟨lpos,by rw [←LTerm.erase_subterm,lold];rfl⟩
  let re : SyntaxIncidence.Edge source:=⟨rpos,by rw [←LTerm.erase_subterm,rold];rfl⟩
  have lFull : SyntaxIncidence.label source le=initialRelabelling source 0 leftAtom := by
    rw [SyntaxIncidence.label_of_lookup source le lold,label_relabel,latom];rfl
  have rFull : SyntaxIncidence.label source re=initialRelabelling source 0 rightAtom := by
    rw [SyntaxIncidence.label_of_lookup source re rold,label_relabel,ratom];rfl
  have oldLabel : SyntaxIncidence.label source le=SyntaxIncidence.label source re:=lFull.trans (imageEq.trans rFull.symm)
  have oldSourceIso : SuccessfulEndpointIso source closed
      (SyntaxIncidence.source source le) (SyntaxIncidence.source source re) := by
    rw [SyntaxIncidence.source_eq_of_spec source le lsource,SyntaxIncidence.source_eq_of_spec source re rsource]
    exact oldParentIso
  have oldTargetIso : SuccessfulEndpointIso source closed
      (SyntaxIncidence.target source closed le) (SyntaxIncidence.target source closed re) := by
    rw [SyntaxIncidence.target_eq_of_spec source closed le ltarget,
      SyntaxIncidence.target_eq_of_spec source closed re rtarget,←kindEq]
    exact SelectedRedex.endpoint_iso closed selected lselected rselected (!leftKind)
  have pieces : (sourceSelection le).fragment.segments=(sourceSelection re).fragment.segments := by
    apply Classical.byContradiction
    intro different
    exact sourceAux le re laux raux oldLabel different ⟨oldSourceIso,oldTargetIso⟩
  have localMatching : Matches g root (initLabels source.erase).erase := by simpa only [erase_initLabels] using matching
  have lEval:=selection.atomWord_occurrence_segments (init_is_INIT _) localMatching matching locc latom (sourceSelection le)
  have rEval:=selection.atomWord_occurrence_segments (init_is_INIT _) localMatching matching rocc ratom (sourceSelection re)
  exact lEval.trans (pieces.trans rEval.symm)
end Lamping.AG
#print axioms Lamping.AG.paired_aux_writing_first_atom_words
