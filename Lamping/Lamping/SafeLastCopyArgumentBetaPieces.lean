import Lamping.Lamping.NormalCopyArgumentLocalEvaluation
import Lamping.Lamping.SafeLastCopyArgumentAuxInputs
import Lamping.Lamping.FirstCopyArgumentEvaluation
import Lamping.Lamping.FamilyRepresentation
import Lamping.Lamping.BetaEvaluatedChildResiduals

namespace Lamping.AG
open Graph Lambda Lambda.Labelled

private def reindexOccurrence
    {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
    {current : LTerm} {g : Net signature N B W} {root : B} {p q : Path}
    (child : OccurrenceFragment current g root p) (same : p=q) :
    OccurrenceFragment current g root q := same ▸ child

private theorem reindexOccurrence_segments
    {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
    {current : LTerm} {g : Net signature N B W} {root : B} {p q : Path}
    (child : OccurrenceFragment current g root p) (same : p=q) :
    (reindexOccurrence child same).fragment.segments=child.fragment.segments := by
  cases same
  rfl

private theorem mapped_lists_injective {A C : Type} {f : A→C}
    (injective : Function.Injective f) {xs ys : List A}
    (same : xs.map f=ys.map f) : xs=ys := by
  induction xs generalizing ys with
  | nil => cases ys <;> simp_all
  | cons x xs ih =>
    cases ys with
    | nil => cases same
    | cons y ys =>
      obtain ⟨head,tail⟩ := List.cons.inj same
      rw [injective head,ih tail]

section
variable {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K→Graph.Label signature} {i : Nat}

/-- Normal COPYlambda APPARG after an arbitrary actual OLD prefix, with
safe LAST and safe AFTER. SOURCE Aux and source coordinate alignment are
internal; ONE physical producer supplies both full CURRENT fragments. -/
theorem PathSite.beta_safe_last_copy_argument_pieces
    (site : PathSite (.beta i) kept (B:=B) (W:=W) (V:=V))
    {root : B} {source middle target original : LTerm} {F prior pre : List Path}
    {degree leftStamp rightStamp : Lambda.Labelled.Label}
    {leftBody rightBody : LTerm} {chosen leftParent rightParent : Path}
    {es fs : List Path} {marked : Marked}
    (closed : Closed source.erase) (initial : INIT original)
    (prefixHistory : History prior original source)
    (event : SelectedOldTurn F source degree pre middle target chosen)
    (selected : ∀name∈F,source.degreeAt name=some degree)
    (leftOccurs : ArgumentOccurrence event.body.erase (leftParent++[.arg]))
    (rightOccurs : ArgumentOccurrence event.body.erase (rightParent++[.arg]))
    (leftLookup : target.subterm (chosen++(leftParent++[.arg]))=some (.lam leftStamp leftBody))
    (rightLookup : target.subterm (chosen++(rightParent++[.arg]))=some (.lam rightStamp rightBody))
    (leftChain : PrerequisiteChain target (chosen++(leftParent++[.arg])) es)
    (rightChain : PrerequisiteChain target (chosen++(rightParent++[.arg])) fs)
    (iso : ChainIncidenceIso
      (chainSyntaxIncidence target (event.final_history.closed closed) es)
      (chainSyntaxIncidence target (event.final_history.closed closed) fs))
    (leftSafe : ∀e∈es.tail,∀n,target.subterm e=some n →n.label.OuterBarsSafe (fun x=>x≠degree))
    (rightSafe : ∀e∈fs.tail,∀n,target.subterm e=some n →n.label.OuterBarsSafe (fun x=>x≠degree))
    (leftLastSafe : ∀node,
      middle.subterm ((chosen++[.fn,.body])++(leftParent++[.arg]))=some node →
        node.label.OuterBarsSafe (fun x=>x≠degree))
    (rightLastSafe : ∀node,
      middle.subterm ((chosen++[.fn,.body])++(rightParent++[.arg]))=some node →
        node.label.OuterBarsSafe (fun x=>x≠degree))
    (matching : Matches site.net root source.erase) (inputs : RootInputs site.net root)
    {boundary : B→Bool} (flow : FlowBalance site.net boundary) (positive : boundary root=true)
    {heights : B→Int} (balance : IndexedLevelBalance site.net heights) (rootDepth : heights root=0)
    (transparency : Transparency site.net root)
    (relative : Marked.RelativeHistory (pre++[chosen])
      (Marked.mark (site.betaSyntaxFiber root source.erase) source.erase) marked)
    (normal : Marked.Normal marked)
    (sourceSelection : OccurrenceFragmentSelection source site.net root)
    (representation : JointRepresentation closed sourceSelection)
    (leftChild : OccurrenceFragment target site.reduce root (chosen++(leftParent++[.arg])))
    (rightChild : OccurrenceFragment target site.reduce root (chosen++(rightParent++[.arg]))) :
    ∃localTarget,History (pre++[chosen]) (initLabels source.erase) localTarget ∧
      ∃edge : BetaEdge site.net,∃selection : SourceEdgeSelection (initLabels source.erase) site.net root,
        SiteBetaGeometry site edge ∧∃ln rn,
          localTarget.subterm (chosen++(leftParent++[.arg]))=some ln ∧
          localTarget.subterm (chosen++(rightParent++[.arg]))=some rn ∧
          selection.evalLabel edge ln.label=selection.evalLabel edge rn.label ∧
          selection.evalLabel edge ln.label≠[] ∧selection.evalLabel edge rn.label≠[] ∧
          BetaPathResidual site edge (leftChild.fragment.segments.map (plugEnd _ _).invFun)
            (selection.evalLabel edge ln.label) ∧
          BetaPathResidual site edge (rightChild.fragment.segments.map (plugEnd _ _).invFun)
            (selection.evalLabel edge rn.label) ∧
          leftChild.fragment.segments=rightChild.fragment.segments := by
  obtain ⟨out⟩ := safe_last_copy_argument_aux_inputs initial prefixHistory closed event selected
    leftOccurs rightOccurs leftLookup rightLookup leftChain rightChain iso leftSafe rightSafe
    leftLastSafe rightLastSafe
  have oldPieces : (sourceSelection out.leftLast).fragment.segments=
      (sourceSelection out.rightLast).fragment.segments := by
    classical
    exact Classical.byContradiction (fun unequal=>
      representation.2 out.leftLast out.rightLast out.leftAux out.rightAux out.sameLabel unequal
        ⟨out.sourceIso,out.targetIso⟩)
  obtain ⟨localTarget,localHistory,_erase,_matching,edge,selection,geometry,allChildren⟩ :=
    site.beta_evaluated_child_residuals closed matching inputs flow positive balance rootDepth transparency
      relative normal event.final_history
  obtain ⟨localMiddle,localPrefix,localLast⟩ := History.split (ps:=pre) (qs:=[chosen]) localHistory
  have localStep : StepAt chosen localMiddle localTarget := by
    cases localLast with
    | cons first rest => cases rest;exact first
  have sameMiddle : middle.erase=localMiddle.erase := by
    obtain ⟨candidate,lifted,erased⟩ := lift_history event.labels.betaHistory
      (initLabels source.erase) (erase_initLabels source.erase)
    rw [lifted.deterministic localPrefix] at erased
    exact erased.symm
  let leftAt := reindexOccurrence leftChild (List.append_assoc chosen leftParent [Step.arg]).symm
  let rightAt := reindexOccurrence rightChild (List.append_assoc chosen rightParent [Step.arg]).symm
  obtain ⟨la,lf,larg,leftParentLookup,leftRole⟩ := leftAt.argument_parent_departure
  obtain ⟨ra,rf,rarg,rightParentLookup,rightRole⟩ := rightAt.argument_parent_departure
  obtain ⟨ln,leftLocal,_leftErase,leftNonempty,leftResidual⟩ :=
    allChildren (chosen++leftParent) .arg (.app la lf larg) leftParentLookup leftAt leftRole
  obtain ⟨rn,rightLocal,_rightErase,rightNonempty,rightResidual⟩ :=
    allChildren (chosen++rightParent) .arg (.app ra rf rarg) rightParentLookup rightAt rightRole
  have leftLocalLookup : localTarget.subterm (chosen++(leftParent++[.arg]))=some ln := by
    simpa only [List.append_assoc] using leftLocal
  have rightLocalLookup : localTarget.subterm (chosen++(rightParent++[.arg]))=some rn := by
    simpa only [List.append_assoc] using rightLocal
  obtain ⟨lb,la,lbody,larg,lvar,lredex,leval⟩ :=
    selection.copy_argument_local_formula sameMiddle event.redex localStep leftOccurs leftLocalLookup edge
  obtain ⟨rb,ra,rbody,rarg,rvar,rredex,reval⟩ :=
    selection.copy_argument_local_formula sameMiddle event.redex localStep rightOccurs rightLocalLookup edge
  have leftLocalLast : localMiddle.subterm out.left.current.last.val=
      some (.var lvar (binderDepth (leftParent++[.arg]))) := by
    rw [out.left.current.lastPath]
    exact leval.1
  have rightLocalLast : localMiddle.subterm out.right.current.last.val=
      some (.var rvar (binderDepth (rightParent++[.arg]))) := by
    rw [out.right.current.lastPath]
    exact reval.1
  have leftIncomingSafe : out.left.current.variableLabel.OuterBarsSafe (fun x=>x≠degree) := by
    apply leftLastSafe (.var out.left.current.variableLabel (binderDepth (leftParent++[.arg])))
    rw [←out.left.current.lastPath]
    exact out.left.current.lastLookup
  have rightIncomingSafe : out.right.current.variableLabel.OuterBarsSafe (fun x=>x≠degree) := by
    apply rightLastSafe (.var out.right.current.variableLabel (binderDepth (rightParent++[.arg])))
    rw [←out.right.current.lastPath]
    exact out.right.current.lastLookup
  have leftEvaluation : selection.evalLabel edge lvar=(sourceSelection out.leftLast).fragment.segments := by
    obtain ⟨oldPosition,oldNode,_lookup,trace,evaluate⟩ :=
      selection.marker_free_local_evaluation matching event.beforeOld (DegreeAligned.initial source F)
        event.labels localPrefix selected out.left.current.lastLookup leftLocalLast leftIncomingSafe edge
    have same : oldPosition=out.leftLast.val := trace.unique out.left.trace
    subst oldPosition
    exact evaluate (sourceSelection out.leftLast)
  have rightEvaluation : selection.evalLabel edge rvar=(sourceSelection out.rightLast).fragment.segments := by
    obtain ⟨oldPosition,oldNode,_lookup,trace,evaluate⟩ :=
      selection.marker_free_local_evaluation matching event.beforeOld (DegreeAligned.initial source F)
        event.labels localPrefix selected out.right.current.lastLookup rightLocalLast rightIncomingSafe edge
    have same : oldPosition=out.rightLast.val := trace.unique out.right.trace
    subst oldPosition
    exact evaluate (sourceSelection out.rightLast)
  have arguments := LTerm.app.inj (Option.some.inj (lredex.symm.trans rredex))
  have heads : selection.evalLabel edge ln.label=selection.evalLabel edge rn.label := by
    rw [leval.2,reval.2,leftEvaluation,rightEvaluation,oldPieces,arguments.2.2]
  simp only [leftAt,reindexOccurrence_segments] at leftResidual
  simp only [rightAt,reindexOccurrence_segments] at rightResidual
  have raw := leftResidual.target_unique site geometry rightResidual heads
  have pieces := mapped_lists_injective (plugEnd _ _).symm.injective raw
  exact ⟨localTarget,localHistory,edge,selection,geometry,ln,rn,leftLocalLookup,rightLocalLookup,
    heads,leftNonempty,rightNonempty,leftResidual,rightResidual,pieces⟩
end

#print axioms PathSite.beta_safe_last_copy_argument_pieces
end Lamping.AG
