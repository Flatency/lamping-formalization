import Lamping.Lamping.GivenParentCanonicalFarComparison
import Lamping.Lamping.PairedSpineNearComparison
import Lamping.Lamping.NonterminalFarBoundary
import Lamping.Lambda.DirectedOuterAtomCells
import Lamping.Lamping.BetaChainEvaluatedResiduals

namespace Lamping.AG
open Graph Lambda Lambda.Labelled SyntaxIncidence

variable {original source current localTarget node localNode : LTerm}
variable {prior ps F : List Path} {degree : Lambda.Labelled.Label} {marked : Marked}
variable {p start ls rs : Path} {edges les res : List Path}

private theorem actual_local_image
    (labels : History ps source current)
    (localHistory : History ps (initLabels source.erase) localTarget)
    (globalAt : current.subterm p=some node)
    (localAt : localTarget.subterm p=some localNode) :
    localNode.label.relabel (initialRelabelling source 0)=node.label := by
  have transported:=localHistory.relabel (initialRelabelling source 0)
  have factor : (initLabels source.erase).relabel (initialRelabelling source 0)=source :=
    initialRelabelling_factor source 0
  rw [factor] at transported
  have whole:=transported.deterministic labels
  have atSame:=congrArg (fun t : LTerm=>t.subterm p) whole
  change (localTarget.relabel (initialRelabelling source 0)).subterm p=current.subterm p at atSame
  rw [LTerm.subterm_relabel,localAt,Option.map_some,globalAt] at atSame
  have eq:=congrArg LTerm.label (Option.some.inj atSame)
  cases localNode <;> exact eq

private theorem cut_bad
    (cut : ActualUnsafeMarkerCut F ps source current degree start edges) :
    ¬degreeReadSafe degree (current.labelAt cut.edge) := by
  intro safe
  apply cut.marked
  apply safe cut.node.label
  simp only [LTerm.labelAt,cut.lookup,Option.map_some]

private theorem given_cut_alignment
    (initial : INIT original) (prefixHistory : History prior original source)
    (closed : Closed source.erase)
    (old : Marked.RelativeOldHistory F ps (Marked.mark F source.erase) marked)
    (labels : History ps source current)
    (selected : ∀name∈F,source.degreeAt name=some degree)
    (sourceSafe : source.OuterBarsSafe (fun x=>x≠degree))
    (left : ActualUnsafeMarkerCut F ps source current degree ls les)
    (right : ActualUnsafeMarkerCut F ps source current degree rs res)
    (leftMore : left.after≠[]) (rightMore : right.after≠[])
    (wholeIso : ChainIncidenceIso
      (chainSyntaxIncidence current (labels.closed closed) les)
      (chainSyntaxIncidence current (labels.closed closed) res)) :
    left.node.label=right.node.label ∧left.forward=right.forward := by
  have lc : PrerequisiteChain current ls les := by
    rw [left.split];exact left.segment.close left.remaining
  have rc : PrerequisiteChain current rs res := by
    rw [right.split];exact right.segment.close right.remaining
  rcases actual_first_unsafe_current_after initial prefixHistory old labels selected sourceSafe
      (labels.closed closed) lc rc wholeIso with safe | cuts
  · apply False.elim
    apply cut_bad left
    apply safe.1 left.edge
    exact Eq.mpr (congrArg (fun xs : List Path=>left.edge∈xs) left.split)
      (List.mem_append_right _ List.mem_cons_self)
  · obtain ⟨l,r,_len,_front,head,_back,_ll,_rl,result⟩:=cuts
    have le:=left.nonterminal_unique l leftMore
    have re:=right.nonterminal_unique r rightMore
    cases le
    cases re
    have same : left.node.label=right.node.label := by
      simpa only [LTerm.labelAt,left.lookup,right.lookup,Option.map_some,Option.some.injEq] using head
    refine ⟨same,?_⟩
    rcases result with empty | more
    · exact False.elim (leftMore empty.1)
    · exact more.2.2.1

private theorem actual_local_not_singleton
    (labels : History ps source current)
    (localHistory : History ps (initLabels source.erase) localTarget)
    (sourceSafe : source.OuterBarsSafe (fun x=>x≠degree))
    (cut : ActualUnsafeMarkerCut F ps source current degree start edges)
    (lookup : localTarget.subterm cut.edge=some localNode) (n : Nat) :
    localNode.label.readLetters cut.forward≠[.atom n] := by
  intro singleton
  have atomic : localNode.label=Label.atom n := by
    apply Label.letters_injective
    cases direction : cut.forward with
    | true => simpa only [direction,Label.readLetters,if_true,Label.letters] using singleton
    | false =>
      have rev:=congrArg List.reverse singleton
      simpa only [direction,Label.readLetters,Bool.false_eq_true,if_false,List.reverse_reverse,
        List.reverse_cons,List.reverse_nil,List.nil_append,Label.letters] using rev
  have support:=(LTerm.supported_iff _ _).mp
    (localHistory.supported (init_is_INIT _).supported) _ (LTerm.label_mem_of_subterm lookup)
  rw [atomic] at support
  have inside : Label.atom n∈(initLabels source.erase).labels := support
  have imageMember:=initialRelabelling_mem source 0 n (Nat.zero_le _)
    (by simpa only [Nat.zero_add] using LTerm.basis_atom_bound source inside)
  have safe:=(LTerm.outerBarsSafe_iff _ _).mp sourceSafe _ imageMember
  have image:=actual_local_image labels localHistory cut.lookup lookup
  rw [atomic,Label.relabel_atom] at image
  exact cut.marked (image ▸ safe)

private theorem same_ordinal_atom
    {left right : List Letter} {lp rp lt rt : List Letter} {n m : Nat}
    (ls : left=lp++(.atom n::lt)) (rs : right=rp++(.atom m::rt))
    (same : left=right) (length : lp.length=rp.length) : n=m := by
  have equal : lp++(.atom n::lt)=rp++(.atom m::rt) := ls.symm.trans (same.trans rs)
  clear ls rs same
  induction lp generalizing rp with
  | nil =>
    have empty : rp=[]:=List.length_eq_zero_iff.mp length.symm
    subst rp
    exact Letter.atom.inj (List.cons.inj equal).1
  | cons a lp ih =>
    cases rp with
    | nil => simp at length
    | cons b rp =>
      exact ih (by simpa using length) (List.cons.inj equal).2

private theorem false_of_not_true (value : Bool) (ne : value≠true) : value=false := by
  cases value with
  | false => rfl
  | true => exact False.elim (ne rfl)

section Orientation
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable {g : Net signature N B W}
private theorem orient_cancel (forward : Bool) {left right : List (Endpoint g)}
    (same : orientPhysical forward left=orientPhysical forward right) : left=right := by
  cases forward with
  | true => exact same
  | false =>
    have back:=congrArg reverseEdges same
    simpa only [orientPhysical,Bool.false_eq_true,if_false,reverseEdges_involutive] using back
end Orientation

private theorem keyed_fold_equal {X : Type} (s : Nat→Lambda.Labelled.Label)
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

section NearDirections
variable {leftTarget rightTarget leftLocalTarget rightLocalTarget leftCurrent rightCurrent : LTerm}
variable {leftPs rightPs : List Path} {leftForward rightForward : Bool}
variable {leftBefore rightBefore : List (Option Lambda.Labelled.Label)} {lp rp : Path}
variable {leftSpine : DirectedMarkerSpine F source degree leftForward leftPs leftTarget leftBefore lp}
variable {rightSpine : DirectedMarkerSpine F source degree rightForward rightPs rightTarget rightBefore rp}
variable {leftLookup : leftTarget.subterm lp=some leftCurrent}
variable {rightLookup : rightTarget.subterm rp=some rightCurrent}
variable {leftLeaf : DirectedMarkerLeafOutput F source degree leftForward leftPs
  (leftCurrent.label.readLetters leftForward)}
variable {rightLeaf : DirectedMarkerLeafOutput F source degree rightForward rightPs
  (rightCurrent.label.readLetters rightForward)}
variable {leftSnapshot : IncomingIncidenceSnapshot leftTarget lp}
variable {rightSnapshot : IncomingIncidenceSnapshot rightTarget rp}
variable {leftGeometry : SpineIncidenceProvenance F source degree leftForward
  leftSpine leftLookup leftLeaf leftSnapshot}
variable {rightGeometry : SpineIncidenceProvenance F source degree rightForward
  rightSpine rightLookup rightLeaf rightSnapshot}
variable {leftHistory : History leftPs (initLabels source.erase) leftLocalTarget}
variable {rightHistory : History rightPs (initLabels source.erase) rightLocalTarget}
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable {g : Net signature N B W} {root : B}

private theorem near_atom_words_of_directions
    (leftPair : PairedSpineReannotation leftGeometry leftHistory (erase_initLabels source.erase).symm)
    (rightPair : PairedSpineReannotation rightGeometry rightHistory (erase_initLabels source.erase).symm)
    (leftNear : SpineNearFirstAtom leftPair) (rightNear : SpineNearFirstAtom rightPair)
    {leftMarked rightMarked : Marked}
    (leftOld : Marked.RelativeOldHistory F leftPs (Marked.mark F source.erase) leftMarked)
    (rightOld : Marked.RelativeOldHistory F rightPs (Marked.mark F source.erase) rightMarked)
    (leftLabels : History leftPs source leftTarget) (rightLabels : History rightPs source rightTarget)
    (selected : ∀name∈F,source.degreeAt name=some degree)
    (sourceSafe : source.OuterBarsSafe (fun x=>x≠degree))
    (sameCurrent : leftCurrent.label=rightCurrent.label) (direction : leftForward=rightForward)
    (prefixHistory : History prior original source) (initial : INIT original)
    (closed : Closed source.erase) (matching : Matches g root source.erase)
    (sourceSelection : OccurrenceFragmentSelection source g root)
    (representation : ChainRepresentationInvariant closed sourceSelection)
    (selection : SourceEdgeSelection (initLabels source.erase) g root) (physical : BetaEdge g) :
    selection.atomWord leftNear.atom=selection.atomWord rightNear.atom := by
  cases direction
  exact (paired_spine_near_evaluations leftPair rightPair leftNear rightNear leftOld rightOld
    leftLabels rightLabels selected sourceSafe sameCurrent prefixHistory initial closed matching
    sourceSelection representation selection physical).1
end NearDirections

section FarDirections
variable {labels : History ps source current}
variable {leftCut : ActualUnsafeMarkerCut F ps source current degree ls les}
variable {rightCut : ActualUnsafeMarkerCut F ps source current degree rs res}
variable {leftSnapshot : IncomingIncidenceSnapshot current leftCut.edge}
variable {rightSnapshot : IncomingIncidenceSnapshot current rightCut.edge}
variable {leftCanonical : CanonicalAfterFarOutput labels leftCut leftSnapshot}
variable {rightCanonical : CanonicalAfterFarOutput labels rightCut rightSnapshot}
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable {g : Net signature N B W} {root : B}

private theorem far_atom_words_of_directions
    {leftForward rightForward kind : Bool} {n m : Nat}
    (closed : Closed source.erase) (selected : ∀name∈F,source.degreeAt name=some degree)
    (good : CanonicalFarFullComparison closed leftCanonical rightCanonical)
    (left : NonterminalFarBoundary.OriginalFarAtom source F n kind leftForward leftCanonical.sourceProper)
    (right : NonterminalFarBoundary.OriginalFarAtom source F m kind rightForward rightCanonical.sourceProper)
    (direction : leftForward=rightForward)
    (image : initialRelabelling source 0 n=initialRelabelling source 0 m)
    (matching : Matches g root source.erase)
    (sourceSelection : OccurrenceFragmentSelection source g root)
    (selection : SourceEdgeSelection (initLabels source.erase) g root)
    (auxiliary : AuxiliarySeparation closed sourceSelection) :
    selection.atomWord n=selection.atomWord m := by
  cases direction
  exact (NonterminalFarBoundary.compare_original_atoms closed selected leftCanonical rightCanonical
    good left right image).atom_words_equal matching sourceSelection selection auxiliary
end FarDirections

section CompleteHead
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable {g : Net signature N B W} {root : B}
variable {labels : History ps source current}
variable {leftCut : ActualUnsafeMarkerCut F ps source current degree ls les}
variable {rightCut : ActualUnsafeMarkerCut F ps source current degree rs res}
variable {leftSnapshot : IncomingIncidenceSnapshot current leftCut.edge}
variable {rightSnapshot : IncomingIncidenceSnapshot current rightCut.edge}
variable {leftLeaf : DirectedMarkerLeafOutput F source degree leftCut.forward ps
  (leftCut.node.label.readLetters leftCut.forward)}
variable {rightLeaf : DirectedMarkerLeafOutput F source degree rightCut.forward ps
  (rightCut.node.label.readLetters rightCut.forward)}
variable {leftGeometry : SpineIncidenceProvenance F source degree leftCut.forward
  leftCut.spine leftCut.lookup leftLeaf leftSnapshot}
variable {rightGeometry : SpineIncidenceProvenance F source degree rightCut.forward
  rightCut.spine rightCut.lookup rightLeaf rightSnapshot}
variable {localHistory : History ps (initLabels source.erase) localTarget}

/-- Compare the complete local evaluations of these GIVEN nonterminal heads.
All SOURCE endpoint comparisons come from the natural parent iso and SOURCE IH. -/
theorem paired_nonterminal_spine_head_evaluations
    (initial : INIT original) (prefixHistory : History prior original source)
    (closed : Closed source.erase)
    (old : Marked.RelativeOldHistory F ps (Marked.mark F source.erase) marked)
    (selected : ∀name∈F,source.degreeAt name=some degree)
    (sourceSafe : source.OuterBarsSafe (fun x=>x≠degree))
    (leftMore : leftCut.after≠[]) (rightMore : rightCut.after≠[])
    (wholeIso : ChainIncidenceIso
      (chainSyntaxIncidence current (labels.closed closed) les)
      (chainSyntaxIncidence current (labels.closed closed) res))
    (leftCanonical : CanonicalAfterFarOutput labels leftCut leftSnapshot)
    (rightCanonical : CanonicalAfterFarOutput labels rightCut rightSnapshot)
    (leftPair : PairedSpineReannotation leftGeometry localHistory (erase_initLabels source.erase).symm)
    (rightPair : PairedSpineReannotation rightGeometry localHistory (erase_initLabels source.erase).symm)
    (leftNear : SpineNearFirstAtom leftPair) (rightNear : SpineNearFirstAtom rightPair)
    (matching : Matches g root source.erase)
    (sourceSelection : OccurrenceFragmentSelection source g root)
    (sourceJoint : JointRepresentation closed sourceSelection)
    (selection : SourceEdgeSelection (initLabels source.erase) g root)
    (physical : BetaEdge g) :
    selection.evalLabel physical leftPair.current.label=
      selection.evalLabel physical rightPair.current.label := by
  have alignment:=given_cut_alignment initial prefixHistory closed old labels selected sourceSafe
    leftCut rightCut leftMore rightMore wholeIso
  have direction:=alignment.2
  have nearEq:=near_atom_words_of_directions leftPair rightPair leftNear rightNear old old labels labels
    selected sourceSafe alignment.1 direction prefixHistory initial closed matching sourceSelection
    sourceJoint.1 selection physical
  have good:=actual_given_parent_canonical_far_comparison initial prefixHistory closed old labels
    selected sourceSafe leftCut rightCut leftMore rightMore leftSnapshot rightSnapshot
    leftCanonical rightCanonical wholeIso
  obtain ⟨cells⟩:=old.directed_outer_atom_cells old labels labels localHistory localHistory
    selected sourceSafe leftCut.lookup rightCut.lookup leftPair.currentLookup rightPair.currentLookup
    alignment.1 leftCut.forward
  have rightNearWord :=
    (congrArg (fun d=>rightPair.current.label.readLetters d) direction).trans rightNear.word
  have words :
      interpretReadLetters selection.atomWord physical.principal physical.reverseRoute leftCut.forward
        (leftPair.current.label.readLetters leftCut.forward)=
      interpretReadLetters selection.atomWord physical.principal physical.reverseRoute leftCut.forward
        (rightPair.current.label.readLetters leftCut.forward) := by
    apply keyed_fold_equal (initialRelabelling source 0)
      (fun letter=>orientPhysical leftCut.forward
        (letter.sourceWord selection.atomWord physical.principal physical.reverseRoute))
      (by intro kind a b;cases kind <;> rfl) cells.keyEq
    intro lp rp n m lt rt lsplit rsplit lengths _image
    obtain ⟨cell⟩:=cells.leftCells lp n lt lsplit
    have sameAtom:=same_ordinal_atom cell.rightSplit rsplit rfl
      (cell.beforeLength.symm.trans lengths)
    have atomEq : selection.atomWord n=selection.atomWord cell.rightAtom := by
      have windows:=cell.writing_windows
      rcases cell with ⟨other,rb,ra,lsp,rsp,_bl,_al,_rbc,_rac,image,_bk,_ak,shape⟩
      cases shape with
      | singleton =>
        exact False.elim (actual_local_not_singleton labels localHistory sourceSafe leftCut
          leftPair.currentLookup n lsp)
      | first kind ld rd lr rr =>
        have leftFirst : n=leftNear.atom := Letter.atom.inj (List.cons.inj (lsp.symm.trans leftNear.word)).1
        have rightFirst : other=rightNear.atom := Letter.atom.inj (List.cons.inj (rsp.symm.trans rightNearWord)).1
        exact (congrArg selection.atomWord leftFirst).trans
          (nearEq.trans (congrArg selection.atomWord rightFirst).symm)
      | last kind ld rd lb rb =>
        have leftBoundary : leftPair.current.label.readLetters leftCut.forward=
            lb++[InteriorSourceBlock.bar kind ld,.atom n] := by
          simpa only [List.append_assoc,List.singleton_append,readingBar,InteriorSourceBlock.bar] using lsp
        have rightCommon : rightPair.current.label.readLetters leftCut.forward=
            rb++[InteriorSourceBlock.bar kind rd,.atom other] := by
          simpa only [List.append_assoc,List.singleton_append,readingBar,InteriorSourceBlock.bar] using rsp
        have rightBoundary :=
          (congrArg (fun d=>rightPair.current.label.readLetters d) direction.symm).trans rightCommon
        obtain ⟨leftOrigin⟩:=NonterminalFarBoundary.actual_old_far_atom labels old localHistory
          leftCut leftMore leftSnapshot leftCanonical leftPair.currentLookup leftBoundary
        obtain ⟨rightOrigin⟩:=NonterminalFarBoundary.actual_old_far_atom labels old localHistory
          rightCut rightMore rightSnapshot rightCanonical rightPair.currentLookup rightBoundary
        exact far_atom_words_of_directions closed selected good leftOrigin rightOrigin direction image
          matching sourceSelection selection sourceJoint.2
      | interior nk fk lnd rnd lfd rfd lb rb la ra =>
        by_cases d : leftCut.forward=true
        ·
          have lw : leftPair.current.label.letters=
              lb++[InteriorSourceBlock.bar nk lnd,.atom n,InteriorSourceBlock.bar fk lfd]++la := by
            simpa [d,List.append_assoc,readingBar,InteriorSourceBlock.bar] using windows.1
          have rw : rightPair.current.label.letters=
              rb++[InteriorSourceBlock.bar nk rnd,.atom other,InteriorSourceBlock.bar fk rfd]++ra := by
            simpa [d,List.append_assoc,readingBar,InteriorSourceBlock.bar] using windows.2
          obtain ⟨comparison⟩:=InteriorSourceBlock.actual_old_interior_atom_comparison closed selected
            old localHistory leftPair.currentLookup lw old localHistory rightPair.currentLookup rw image
          exact comparison.atom_words_equal matching sourceSelection selection sourceJoint.2
        · have dFalse:=false_of_not_true leftCut.forward d
          have lw : leftPair.current.label.letters=
              la.reverse++[InteriorSourceBlock.bar fk lfd,.atom n,InteriorSourceBlock.bar nk lnd]++lb.reverse := by
            simpa [dFalse,List.append_assoc,List.reverse_append,List.reverse_cons,readingBar,InteriorSourceBlock.bar] using windows.1
          have rw : rightPair.current.label.letters=
              ra.reverse++[InteriorSourceBlock.bar fk rfd,.atom other,InteriorSourceBlock.bar nk rnd]++rb.reverse := by
            simpa [dFalse,List.append_assoc,List.reverse_append,List.reverse_cons,readingBar,InteriorSourceBlock.bar] using windows.2
          obtain ⟨comparison⟩:=InteriorSourceBlock.actual_old_interior_atom_comparison closed selected
            old localHistory leftPair.currentLookup lw old localHistory rightPair.currentLookup rw image
          exact comparison.atom_words_equal matching sourceSelection selection sourceJoint.2
    have same : selection.atomWord n=selection.atomWord m := by simpa only [sameAtom] using atomEq
    exact congrArg (orientPhysical leftCut.forward) same
  rw [SourceEdgeSelection.interpret_read_label,SourceEdgeSelection.interpret_read_label] at words
  exact orient_cancel leftCut.forward words
end CompleteHead

private theorem map_cancel {A C : Type} {f : A→C} (inj : Function.Injective f)
    {xs ys : List A} (same : xs.map f=ys.map f) : xs=ys := by
  induction xs generalizing ys with
  | nil => cases ys <;> simp_all
  | cons a xs ih =>
    cases ys with
    | nil => cases same
    | cons b ys =>
      have pair:=List.cons.inj same
      rw [inj pair.1,ih pair.2]

section BetaProducer
variable {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K→Graph.Label signature} {i : Nat}
variable (site : PathSite (.beta i) kept (B:=B) (W:=W) (V:=V))
variable {root : B}

/-- Elementary transport for the exact SAME GIVEN producer and physical edge. -/
theorem EvaluatedChainResiduals.given_member_pieces_of_evaluations
    {edge : BetaEdge site.net}
    {selection : SourceEdgeSelection (initLabels source.erase) site.net root}
    {targetSelection : OccurrenceFragmentSelection current site.reduce root}
    {leftChain : PrerequisiteChain current ls les} {rightChain : PrerequisiteChain current rs res}
    (geometry : SiteBetaGeometry site edge)
    (left : EvaluatedChainResiduals site (localTarget:=localTarget) edge selection targetSelection leftChain)
    (right : EvaluatedChainResiduals site (localTarget:=localTarget) edge selection targetSelection rightChain)
    (lm : {p : Path // p∈les}) (rm : {p : Path // p∈res})
    (same : selection.evalLabel edge (left.node lm).label=selection.evalLabel edge (right.node rm).label) :
    (targetSelection (actualChainPosition leftChain lm)).fragment.segments=
      (targetSelection (actualChainPosition rightChain rm)).fragment.segments := by
  have raw:=(left.residual lm).target_unique site geometry (right.residual rm) same
  exact map_cancel (plugEnd _ _).symm.injective raw

variable {labels : History ps source current}
variable {leftCut : ActualUnsafeMarkerCut F ps source current degree ls les}
variable {rightCut : ActualUnsafeMarkerCut F ps source current degree rs res}
variable {leftSnapshot : IncomingIncidenceSnapshot current leftCut.edge}
variable {rightSnapshot : IncomingIncidenceSnapshot current rightCut.edge}
variable {leftLeaf : DirectedMarkerLeafOutput F source degree leftCut.forward ps
  (leftCut.node.label.readLetters leftCut.forward)}
variable {rightLeaf : DirectedMarkerLeafOutput F source degree rightCut.forward ps
  (rightCut.node.label.readLetters rightCut.forward)}
variable {leftGeometry : SpineIncidenceProvenance F source degree leftCut.forward
  leftCut.spine leftCut.lookup leftLeaf leftSnapshot}
variable {rightGeometry : SpineIncidenceProvenance F source degree rightCut.forward
  rightCut.spine rightCut.lookup rightLeaf rightSnapshot}
variable {localHistory : History ps (initLabels source.erase) localTarget}

/-- Natural complete-head comparison feeds the SAME already supplied
whole-chain residuals; neither producer nor assignment is selected again. -/
theorem EvaluatedChainResiduals.given_nonterminal_spine_head_pieces
    (initial : INIT original) (prefixHistory : History prior original source)
    (closed : Closed source.erase)
    (old : Marked.RelativeOldHistory F ps (Marked.mark F source.erase) marked)
    (selected : ∀name∈F,source.degreeAt name=some degree)
    (sourceSafe : source.OuterBarsSafe (fun x=>x≠degree))
    (leftMore : leftCut.after≠[]) (rightMore : rightCut.after≠[])
    (wholeIso : ChainIncidenceIso
      (chainSyntaxIncidence current (labels.closed closed) les)
      (chainSyntaxIncidence current (labels.closed closed) res))
    (leftCanonical : CanonicalAfterFarOutput labels leftCut leftSnapshot)
    (rightCanonical : CanonicalAfterFarOutput labels rightCut rightSnapshot)
    (leftPair : PairedSpineReannotation leftGeometry localHistory (erase_initLabels source.erase).symm)
    (rightPair : PairedSpineReannotation rightGeometry localHistory (erase_initLabels source.erase).symm)
    (leftNear : SpineNearFirstAtom leftPair) (rightNear : SpineNearFirstAtom rightPair)
    (matching : Matches site.net root source.erase)
    (sourceSelection : OccurrenceFragmentSelection source site.net root)
    (sourceJoint : JointRepresentation closed sourceSelection)
    {selection : SourceEdgeSelection (initLabels source.erase) site.net root}
    {edge : BetaEdge site.net} (geometry : SiteBetaGeometry site edge)
    {targetSelection : OccurrenceFragmentSelection current site.reduce root}
    {leftChain : PrerequisiteChain current ls les} {rightChain : PrerequisiteChain current rs res}
    (left : EvaluatedChainResiduals site (localTarget:=localTarget) edge selection targetSelection leftChain)
    (right : EvaluatedChainResiduals site (localTarget:=localTarget) edge selection targetSelection rightChain)
    (lm : {p : Path // p∈les}) (rm : {p : Path // p∈res})
    (leftAt : lm.val=leftCut.edge) (rightAt : rm.val=rightCut.edge) :
    (targetSelection (actualChainPosition leftChain lm)).fragment.segments=
      (targetSelection (actualChainPosition rightChain rm)).fragment.segments := by
  have heads:=paired_nonterminal_spine_head_evaluations initial prefixHistory closed old selected
    sourceSafe leftMore rightMore wholeIso leftCanonical rightCanonical leftPair rightPair
    leftNear rightNear matching sourceSelection sourceJoint selection edge
  have ll : localTarget.subterm lm.val=some leftPair.current := by
    rw [leftAt];exact leftPair.currentLookup
  have rl : localTarget.subterm rm.val=some rightPair.current := by
    rw [rightAt];exact rightPair.currentLookup
  have ln : left.node lm=leftPair.current:=Option.some.inj ((left.lookup lm).symm.trans ll)
  have rn : right.node rm=rightPair.current:=Option.some.inj ((right.lookup rm).symm.trans rl)
  apply EvaluatedChainResiduals.given_member_pieces_of_evaluations site geometry left right lm rm
  rw [ln,rn]
  exact heads
end BetaProducer

#print axioms paired_nonterminal_spine_head_evaluations
#print axioms EvaluatedChainResiduals.given_member_pieces_of_evaluations
#print axioms EvaluatedChainResiduals.given_nonterminal_spine_head_pieces

end Lamping.AG
