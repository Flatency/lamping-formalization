import Lamping.Lamping.PairedAuxWritingFirstAtoms
import Lamping.Lambda.DirectedOuterAtomCells
import Lamping.Lamping.DirectedPhysicalLabelEvaluation

namespace Lamping.AG
open Graph Lambda Lambda.Labelled

private theorem word_last_atom {stamp : Label} {pre : List Letter}
    (eq : stamp.letters=pre++[.atom n]) : stamp.lastAtom=some n := by
  induction pre generalizing stamp with
  | nil =>
    have same : stamp=Label.atom n := Label.letters_injective eq
    rw [same];rfl
  | cons head rest ih =>
    cases stamp with
    | single letter =>
      have empty : rest++[Letter.atom n]=[] := (List.cons.inj eq).2.symm
      have impossible := (List.append_eq_nil_iff.mp empty).2
      cases impossible
    | cons letter tail => exact ih (stamp:=tail) (List.cons.inj eq).2

private theorem same_ordinal_atom
    {word : List Letter} {lp rp lt rt : List Letter} {n m : Nat}
    (left : word=lp++(.atom n::lt)) (right : word=rp++(.atom m::rt))
    (length : lp.length=rp.length) : n=m := by
  have equal := left.symm.trans right
  clear left right
  induction lp generalizing rp with
  | nil =>
    have empty : rp=[] := List.length_eq_zero_iff.mp length.symm
    subst rp
    exact Letter.atom.inj (List.cons.inj equal).1
  | cons a lp ih =>
    cases rp with
    | nil => simp at length
    | cons b rp => exact ih (by simpa using length) (List.cons.inj equal).2

private theorem ordered_key_fold {X : Type} (s : Nat→Lambda.Labelled.Label)
    (blocks : Letter→List X)
    (bars : ∀kind left right,blocks (readingBar kind left)=blocks (readingBar kind right))
    {xs ys : List Letter}
    (same : xs.map (Letter.outerImageKey s)=ys.map (Letter.outerImageKey s))
    (atoms : ∀lp rp n m lt rt,
      xs=lp++(.atom n::lt) →ys=rp++(.atom m::rt) →lp.length=rp.length →s n=s m →
      blocks (.atom n)=blocks (.atom m)) : xs.flatMap blocks=ys.flatMap blocks := by
  have go (tail : List Letter) : ∀lp rp other,
      lp.length=rp.length →xs=lp++tail →ys=rp++other →
      tail.map (Letter.outerImageKey s)=other.map (Letter.outerImageKey s) →
      tail.flatMap blocks=other.flatMap blocks := by
    induction tail with
    | nil =>
      intro lp rp other _ _ _ eq
      cases other with
      | nil => rfl
      | cons b bs => simp at eq
    | cons a tail ih =>
      intro lp rp other length leftSplit rightSplit eq
      cases other with
      | nil => simp at eq
      | cons b rest =>
        have pair:=List.cons.inj eq
        have head : blocks a=blocks b := by
          cases a with
          | atom n =>
            cases b with
            | atom m => exact atoms lp rp n m tail rest leftSplit rightSplit length (Sum.inl.inj pair.1)
            | over d => cases pair.1
            | under d => cases pair.1
          | over d =>
            cases b with
            | atom m => cases pair.1
            | over e => exact bars true d e
            | under e => cases Sum.inr.inj pair.1
          | under d =>
            cases b with
            | atom m => cases pair.1
            | over e => cases Sum.inr.inj pair.1
            | under e => exact bars false d e
        have ls : xs=(lp++[a])++tail := by simpa only [List.append_assoc,List.singleton_append] using leftSplit
        have rs : ys=(rp++[b])++rest := by simpa only [List.append_assoc,List.singleton_append] using rightSplit
        have tailEq:=ih (lp++[a]) (rp++[b]) rest (by simpa using length) ls rs pair.2
        simp only [List.flatMap_cons,head,tailEq]
  exact go xs [] [] ys rfl rfl rfl same
private theorem local_last_basis
    {source localTarget node : LTerm} {ps : List Path} {p : Path} {n : Nat}
    (history : History ps (initLabels source.erase) localTarget)
    (lookup : localTarget.subterm p=some node) (last : node.label.lastAtom=some n) :
    ∃oldPosition env ctx basis,
      SourceSubterm [] .external (initLabels source.erase) oldPosition env ctx basis ∧
      basis.label=Label.atom n ∧BetaNodeHistoryPreimage history p oldPosition := by
  obtain ⟨oldPosition,_old,_atOld,trace⟩:=history.node_preimage_from_lookup lookup
  obtain ⟨basis,atBasis,lastAtom,_tag⟩:=trace.lastAtom_constructor lookup
  obtain ⟨m,atomic⟩:=(init_is_INIT source.erase).1 basis.label (LTerm.label_mem_of_subterm atBasis)
  have equal : n=m := by
    have atoms:=last.symm.trans lastAtom
    simpa only [atomic,Label.lastAtom,Label.atom,Option.some.injEq] using atoms
  subst m
  obtain ⟨env,ctx,occurrence⟩:=SourceSubterm.of_lookup _ atBasis [] .external
  exact ⟨oldPosition,env,ctx,basis,occurrence,atomic,trace⟩

private theorem actual_local_reannotation
    {source current localTarget node localNode : LTerm} {ps : List Path} {p : Path}
    (labels : History ps source current)
    (localHistory : History ps (initLabels source.erase) localTarget)
    (lookup : current.subterm p=some node) (localLookup : localTarget.subterm p=some localNode) :
    localNode.relabel (initialRelabelling source 0)=node := by
  have transported:=localHistory.relabel (initialRelabelling source 0)
  have factor : (initLabels source.erase).relabel (initialRelabelling source 0)=source:=
    initialRelabelling_factor source 0
  rw [factor] at transported
  have whole:=transported.deterministic labels
  have atSame:=congrArg (fun term : LTerm=>term.subterm p) whole
  change (localTarget.relabel (initialRelabelling source 0)).subterm p=current.subterm p at atSame
  rw [LTerm.subterm_relabel,localLookup,Option.map_some,lookup] at atSame
  exact Option.some.inj atSame

theorem marked_auxiliary_whole_evaluations
    {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
    {g : Net signature N B W} {root : B}
    {original source current localTarget : LTerm}
    {prior ps F : List Path} {degree : Lambda.Labelled.Label} {marked : Marked}
    (initial : INIT original)
    (prefixHistory : History prior original source)
    (old : Marked.RelativeOldHistory F ps (Marked.mark F source.erase) marked)
    (labels : History ps source current)
    (selected : ∀name∈F,source.degreeAt name=some degree)
    (sourceSafe : source.OuterBarsSafe (fun x=>x≠degree))
    (closed : Closed source.erase)
    (matching : Matches g root source.erase)
    (sourceSelection : OccurrenceFragmentSelection source g root)
    (sourceJoint : JointRepresentation closed sourceSelection)
    (localHistory : History ps (initLabels source.erase) localTarget)
    (left right : SyntaxIncidence.Edge current)
    {leftNode rightNode localLeft localRight : LTerm}
    (leftLookup : current.subterm left.val=some leftNode)
    (rightLookup : current.subterm right.val=some rightNode)
    (leftLocal : localTarget.subterm left.val=some localLeft)
    (rightLocal : localTarget.subterm right.val=some localRight)
    (leftAux : AuxiliaryAt current left.val)
    (rightAux : AuxiliaryAt current right.val)
    (sameLabel : SyntaxIncidence.label current left=SyntaxIncidence.label current right)
    (leftMarked : ¬(SyntaxIncidence.label current left).OuterBarsSafe (fun x=>x≠degree))
    (sourceIso : SuccessfulEndpointIso current (labels.closed closed)
      (SyntaxIncidence.source current left) (SyntaxIncidence.source current right))
    (targetIso : SuccessfulEndpointIso current (labels.closed closed)
      (SyntaxIncidence.target current (labels.closed closed) left)
      (SyntaxIncidence.target current (labels.closed closed) right))
    (selection : SourceEdgeSelection (initLabels source.erase) g root)
    (physical : BetaEdge g) :
    selection.evalLabel physical localLeft.label=selection.evalLabel physical localRight.label := by
  have nodeEq : leftNode.label=rightNode.label := by
    rw [SyntaxIncidence.label_of_lookup current left leftLookup,
      SyntaxIncidence.label_of_lookup current right rightLookup] at sameLabel
    exact sameLabel
  have actualLeft:=actual_local_reannotation labels localHistory leftLookup leftLocal
  have leftUnsafe : ¬leftNode.label.OuterBarsSafe (fun x=>x≠degree) := by
    simpa only [SyntaxIncidence.label_of_lookup current left leftLookup] using leftMarked
  obtain ⟨oldLeft,oldRight,_oldLN,_oldRN,_oldLA,_oldRA,lt,rt,_laux,_raux,_labels,_full,_si,_ti,oldEq⟩:=
    uniform_old_equal_auxiliary_source_pieces initial prefixHistory old labels selected sourceSafe closed
      sourceSelection sourceJoint left right leftAux rightAux sameLabel sourceIso targetIso
  have lastWords (n m : Nat) (leftLast : localLeft.label.lastAtom=some n)
      (rightLast : localRight.label.lastAtom=some m) : selection.atomWord n=selection.atomWord m := by
    obtain ⟨lp,le,lc,lbasis,locc,latom,ltrace⟩:=local_last_basis localHistory leftLocal leftLast
    obtain ⟨rp,re,rc,rbasis,rocc,ratom,rtrace⟩:=local_last_basis localHistory rightLocal rightLast
    have leftCoordinate : lp=oldLeft.val := (NonterminalFarBoundary.local_trace_global localHistory labels ltrace).unique lt
    have rightCoordinate : rp=oldRight.val := (NonterminalFarBoundary.local_trace_global localHistory labels rtrace).unique rt
    have locc' : SourceSubterm [] .external (initLabels source.erase) oldLeft.val le lc lbasis := leftCoordinate ▸ locc
    have rocc' : SourceSubterm [] .external (initLabels source.erase) oldRight.val re rc rbasis := rightCoordinate ▸ rocc
    have localMatching : Matches g root (initLabels source.erase).erase := by simpa only [erase_initLabels] using matching
    have lEval:=selection.atomWord_occurrence_segments (init_is_INIT _) localMatching matching locc' latom (sourceSelection oldLeft)
    have rEval:=selection.atomWord_occurrence_segments (init_is_INIT _) localMatching matching rocc' ratom (sourceSelection oldRight)
    exact lEval.trans (oldEq.trans rEval.symm)
  obtain ⟨cells⟩:=old.directed_outer_atom_cells old labels labels localHistory localHistory
    selected sourceSafe leftLookup rightLookup leftLocal rightLocal nodeEq true
  have words : interpretReadLetters selection.atomWord physical.principal physical.reverseRoute true
      (localLeft.label.readLetters true)=
    interpretReadLetters selection.atomWord physical.principal physical.reverseRoute true
      (localRight.label.readLetters true) := by
    apply ordered_key_fold (initialRelabelling source 0)
      (fun letter=>orientPhysical true (letter.sourceWord selection.atomWord physical.principal physical.reverseRoute))
      (by intro kind a b;cases kind <;> rfl) cells.keyEq
    intro before rightBefore n m after rightAfter leftSplit rightSplit lengths _image
    obtain ⟨cell⟩:=cells.leftCells before n after leftSplit
    have atomSame:=same_ordinal_atom cell.rightSplit rightSplit (cell.beforeLength.symm.trans lengths)
    have atomEq : selection.atomWord n=selection.atomWord cell.rightAtom := by
      have windows:=cell.writing_windows
      rcases cell with ⟨other,rb,ra,lsp,rsp,_bl,_al,_rbc,_rac,image,_bk,_ak,shape⟩
      cases shape with
      | singleton =>
        have single : localLeft.label=Label.atom n := Label.letters_injective (by simpa only [Label.readLetters,if_true] using lsp)
        have last : localLeft.label.lastAtom=some n := by rw [single];rfl
        obtain ⟨lp,env,ctx,basis,occurrence,atomic,_trace⟩:=local_last_basis localHistory leftLocal last
        have factor : (initLabels source.erase).relabel (initialRelabelling source 0)=source:=initialRelabelling_factor source 0
        have atOld : source.subterm lp=some (basis.relabel (initialRelabelling source 0)) := by
          simpa only [factor] using InteriorSourceBlock.lookup_relabel occurrence.lookup (initialRelabelling source 0)
        have safe : (basis.relabel (initialRelabelling source 0)).label.OuterBarsSafe (fun x=>x≠degree) :=
          (LTerm.outerBarsSafe_iff _ _).mp sourceSafe _ (LTerm.label_mem_of_subterm atOld)
        have stampEq : leftNode.label=(basis.relabel (initialRelabelling source 0)).label := by
          rw [←actualLeft]
          simp only [InteriorSourceBlock.label_relabel,single,atomic]
        exact False.elim (leftUnsafe (stampEq ▸ safe))
      | first kind ld rd lr rr =>
        have lw : localLeft.label.letters=[.atom n,InteriorSourceBlock.bar kind ld]++lr := by
          simpa only [Label.readLetters,if_true,readingBar,InteriorSourceBlock.bar,List.nil_append] using lsp
        have rw : localRight.label.letters=[.atom other,InteriorSourceBlock.bar kind rd]++rr := by
          simpa only [Label.readLetters,if_true,readingBar,InteriorSourceBlock.bar,List.nil_append] using rsp
        exact paired_aux_writing_first_atom_words initial prefixHistory old labels localHistory selected sourceSafe closed
          left right leftLookup rightLookup leftAux rightAux sameLabel leftLocal rightLocal lw rw sourceIso
          matching sourceSelection sourceJoint.2 selection
      | last kind ld rd lb rb =>
        have ll : localLeft.label.lastAtom=some n := by
          apply word_last_atom (pre:=lb++[readingBar kind ld])
          simpa only [Label.readLetters,if_true,List.append_assoc,List.singleton_append] using lsp
        have rl : localRight.label.lastAtom=some other := by
          apply word_last_atom (pre:=rb++[readingBar kind rd])
          simpa only [Label.readLetters,if_true,List.append_assoc,List.singleton_append] using rsp
        exact lastWords n other ll rl
      | interior nk fk lnd rnd lfd rfd lb rb la ra =>
        have lw : localLeft.label.letters=lb++[InteriorSourceBlock.bar nk lnd,.atom n,InteriorSourceBlock.bar fk lfd]++la := by
          simpa [List.append_assoc,readingBar,InteriorSourceBlock.bar] using windows.1
        have rw : localRight.label.letters=rb++[InteriorSourceBlock.bar nk rnd,.atom other,InteriorSourceBlock.bar fk rfd]++ra := by
          simpa [List.append_assoc,readingBar,InteriorSourceBlock.bar] using windows.2
        obtain ⟨comparison⟩:=InteriorSourceBlock.actual_old_interior_atom_comparison closed selected
          old localHistory leftLocal lw old localHistory rightLocal rw image
        exact comparison.atom_words_equal matching sourceSelection selection sourceJoint.2
    exact congrArg (orientPhysical true) (by simpa only [atomSame] using atomEq)
  rw [SourceEdgeSelection.interpret_read_label,SourceEdgeSelection.interpret_read_label] at words
  simpa only [orientPhysical,if_true] using words

end Lamping.AG
#print axioms Lamping.AG.marked_auxiliary_whole_evaluations
