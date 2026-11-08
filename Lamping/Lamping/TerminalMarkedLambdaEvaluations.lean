import Lamping.Lamping.TerminalLambdaLastAtom
import Lamping.Lamping.PairedSpineNearComparison
import Lamping.Lambda.DirectedOuterAtomCells

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

private theorem tail_spec_nonempty
    {middle last : LTerm} {site : Path} {alpha : Label} {d : Bool}
    {marker : Letter} {tail : List Letter}
    (spec : SpineReannotation.TailSpecification middle site alpha d last marker tail) : tail≠[] := by
  rcases spec with rfl | ⟨_d,_m,arg,_lookup,rfl⟩ | ⟨_d,_m,app,_lookup,rfl⟩ <;> simp

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

section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable {g : Net signature N B W} {root : B}

/-- Compare the COMPLETE local marked redex-lambda labels. TRUE companions
are new native witnesses; only SAME-coordinate lookup uniqueness identifies
their local nodes with the given ones. No original geometry is identified. -/
theorem terminal_marked_lambda_evaluations
    {original source current localTarget : LTerm}
    {prior ps F : List Path} {degree : Label} {marked : Marked}
    {lp rp : Path} {la ll ra rl llocal rlocal : Label}
    {lb larg rb rarg llbody rlbody : LTerm}
    (initial : INIT original) (prefixHistory : History prior original source)
    (closed : Closed source.erase)
    (old : Marked.RelativeOldHistory F ps (Marked.mark F source.erase) marked)
    (labels : History ps source current)
    (selected : ∀name∈F,source.degreeAt name=some degree)
    (sourceSafe : source.OuterBarsSafe (fun x=>x≠degree))
    (localHistory : History ps (initLabels source.erase) localTarget)
    (leftRedex : current.subterm lp=some (.app la (.lam ll lb) larg))
    (rightRedex : current.subterm rp=some (.app ra (.lam rl rb) rarg))
    (sameCurrent : ll=rl)
    (leftMarked : ¬ll.OuterBarsSafe (fun x=>x≠degree))
    (leftLocal : localTarget.subterm (lp++[.fn])=some (.lam llocal llbody))
    (rightLocal : localTarget.subterm (rp++[.fn])=some (.lam rlocal rlbody))
    (matching : Matches g root source.erase)
    (sourceSelection : OccurrenceFragmentSelection source g root)
    (sourceJoint : JointRepresentation closed sourceSelection)
    (selection : SourceEdgeSelection (initLabels source.erase) g root)
    (physical : BetaEdge g) :
    selection.evalLabel physical llocal=selection.evalLabel physical rlocal := by
  have leftLookup : current.subterm (lp++[.fn])=some (.lam ll lb) := by
    rw [LTerm.subterm_append,leftRedex];rfl
  have rightLookup : current.subterm (rp++[.fn])=some (.lam rl rb) := by
    rw [LTerm.subterm_append,rightRedex];rfl
  have leftRead : PrerequisiteReadsDirected current lp (lp++[.fn]) true :=
    ⟨Or.inl ⟨la,.lam ll lb,larg,leftRedex,rfl⟩,rfl⟩
  have rightRead : PrerequisiteReadsDirected current rp (rp++[.fn]) true :=
    ⟨Or.inl ⟨ra,.lam rl rb,rarg,rightRedex,rfl⟩,rfl⟩
  have rightMarked : ¬rl.OuterBarsSafe (fun x=>x≠degree) := by rw [←sameCurrent];exact leftMarked
  let leftSpine := old.directed_marker_spine labels selected sourceSafe
    (start:=lp) (before:=[]) .refl leftRead leftLookup leftMarked (by intro e inside;cases inside)
  let rightSpine := old.directed_marker_spine labels selected sourceSafe
    (start:=rp) (before:=[]) .refl rightRead rightLookup rightMarked (by intro e inside;cases inside)
  obtain ⟨leftLeaf,leftSnapshot,⟨leftGeometry⟩⟩ := leftSpine.incidence_leaf_output closed leftLookup
  obtain ⟨rightLeaf,rightSnapshot,⟨rightGeometry⟩⟩ := rightSpine.incidence_leaf_output closed rightLookup
  obtain ⟨leftPair⟩ := leftGeometry.paired_reannotation localHistory (erase_initLabels source.erase).symm
  obtain ⟨rightPair⟩ := rightGeometry.paired_reannotation localHistory (erase_initLabels source.erase).symm
  have leftNode : leftPair.current=.lam llocal llbody :=
    Option.some.inj (leftPair.currentLookup.symm.trans leftLocal)
  have rightNode : rightPair.current=.lam rlocal rlbody :=
    Option.some.inj (rightPair.currentLookup.symm.trans rightLocal)
  obtain ⟨leftNear⟩ := Lamping.AG.PairedSpineReannotation.near_first_atom leftPair selected
  obtain ⟨rightNear⟩ := Lamping.AG.PairedSpineReannotation.near_first_atom rightPair selected
  have nearEq := (paired_spine_near_evaluations leftPair rightPair leftNear rightNear old old labels labels
    selected sourceSafe sameCurrent prefixHistory initial closed matching sourceSelection sourceJoint.1 selection physical).1
  obtain ⟨cells⟩ := old.directed_outer_atom_cells old labels labels localHistory localHistory
    selected sourceSafe leftLookup rightLookup leftPair.currentLookup rightPair.currentLookup sameCurrent true
  have words : interpretReadLetters selection.atomWord physical.principal physical.reverseRoute true
      (leftPair.current.label.readLetters true)=
    interpretReadLetters selection.atomWord physical.principal physical.reverseRoute true
      (rightPair.current.label.readLetters true) := by
    apply ordered_key_fold (initialRelabelling source 0)
      (fun letter=>orientPhysical true (letter.sourceWord selection.atomWord physical.principal physical.reverseRoute))
      (by intro kind a b;cases kind <;> rfl) cells.keyEq
    intro before rightBefore n m after rightAfter leftSplit rightSplit lengths _image
    obtain ⟨cell⟩ := cells.leftCells before n after leftSplit
    have atomSame := same_ordinal_atom cell.rightSplit rightSplit (cell.beforeLength.symm.trans lengths)
    have atomEq : selection.atomWord n=selection.atomWord cell.rightAtom := by
      have windows := cell.writing_windows
      rcases cell with ⟨other,rb,ra,lsp,rsp,_bl,_al,_rbc,_rac,image,_bk,_ak,shape⟩
      cases shape with
      | singleton =>
        have positive : 0<leftNear.baseTail.length := List.length_pos_iff.mpr (tail_spec_nonempty leftNear.tailSpec)
        have length := congrArg List.length (lsp.symm.trans leftNear.word)
        simp only [List.length_append,List.length_singleton,List.length_nil] at length
        omega
      | first kind ld rd lr rr =>
        have lfirst : n=leftNear.atom := Letter.atom.inj (List.cons.inj (lsp.symm.trans leftNear.word)).1
        have rfirst : other=rightNear.atom := Letter.atom.inj (List.cons.inj (rsp.symm.trans rightNear.word)).1
        exact (congrArg selection.atomWord lfirst).trans
          (nearEq.trans (congrArg selection.atomWord rfirst).symm)
      | last kind ld rd lb rb =>
        have lastLeft : llocal.lastAtom=some n := by
          apply word_last_atom (pre:=lb++[readingBar kind ld])
          simpa only [Label.readLetters,if_true,leftNode,LTerm.label] using lsp
        have lastRight : rlocal.lastAtom=some other := by
          apply word_last_atom (pre:=rb++[readingBar kind rd])
          simpa only [Label.readLetters,if_true,rightNode,LTerm.label] using rsp
        exact terminal_lambda_writing_last_atom_evaluations initial prefixHistory closed old labels
          selected sourceSafe localHistory leftRedex rightRedex sameCurrent leftLocal rightLocal lastLeft lastRight
          matching sourceSelection sourceJoint.1 selection
      | interior nk fk lnd rnd lfd rfd lb rb la ra =>
        have lw : leftPair.current.label.letters=
            lb++[InteriorSourceBlock.bar nk lnd,.atom n,InteriorSourceBlock.bar fk lfd]++la := by
          simpa [List.append_assoc,readingBar,InteriorSourceBlock.bar] using windows.1
        have rw : rightPair.current.label.letters=
            rb++[InteriorSourceBlock.bar nk rnd,.atom other,InteriorSourceBlock.bar fk rfd]++ra := by
          simpa [List.append_assoc,readingBar,InteriorSourceBlock.bar] using windows.2
        obtain ⟨comparison⟩ := InteriorSourceBlock.actual_old_interior_atom_comparison closed selected
          old localHistory leftPair.currentLookup lw old localHistory rightPair.currentLookup rw image
        exact comparison.atom_words_equal matching sourceSelection selection sourceJoint.2
    exact congrArg (orientPhysical true) (by simpa only [atomSame] using atomEq)
  rw [SourceEdgeSelection.interpret_read_label,SourceEdgeSelection.interpret_read_label] at words
  simpa only [orientPhysical,if_true,leftNode,rightNode,LTerm.label] using words
end
end Lamping.AG
