import Lamping.Lamping.FirstCopyArgumentEvaluation
import Lamping.Lamping.FirstCopyArgumentAuxInputs
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
variable (site : PathSite (.beta i) kept (B:=B) (W:=W) (V:=V))

/-- Actual SOURCE Aux is applied internally to the two genuine old variable
edges and four successful chains. ONE local producer then gives complete
CURRENT ARG fragment equality. This is only the first relative-event,
normal COPYlambda APPARG, all-safe-AFTER branch. -/
theorem PathSite.beta_first_copy_argument_pieces
    {root : B} {source target original : LTerm} {F prior : List Path}
    {degree argStamp leftStamp rightStamp : Lambda.Labelled.Label}
    {argBody leftBody rightBody : LTerm} {chosen leftParent rightParent : Path}
    {es fs : List Path} {marked : Marked}
    (closed : Closed source.erase) (initial : INIT original)
    (prefixHistory : History prior original source)
    (event : SelectedOldTurn F source degree [] source target chosen)
    (selected : ∀name∈F,source.degreeAt name=some degree)
    (_argumentShape : event.argument=.lam argStamp argBody)
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
    (matching : Matches site.net root source.erase) (inputs : RootInputs site.net root)
    {boundary : B→Bool} (flow : FlowBalance site.net boundary) (positive : boundary root=true)
    {heights : B→Int} (balance : IndexedLevelBalance site.net heights) (rootDepth : heights root=0)
    (transparency : Transparency site.net root)
    (relative : Marked.RelativeHistory [chosen]
      (Marked.mark (site.betaSyntaxFiber root source.erase) source.erase) marked)
    (normal : Marked.Normal marked)
    (sourceSelection : OccurrenceFragmentSelection source site.net root)
    (representation : JointRepresentation closed sourceSelection)
    (leftChild : OccurrenceFragment target site.reduce root (chosen++(leftParent++[.arg])))
    (rightChild : OccurrenceFragment target site.reduce root (chosen++(rightParent++[.arg]))) :
    ∃localTarget,History [chosen] (initLabels source.erase) localTarget ∧
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
  -- The natural copied-argument shape is retained in this public signature;
  -- the actual copied lambda lookups already suffice for its pure supplier.
  obtain ⟨out⟩ := first_copy_argument_aux_inputs initial prefixHistory closed event selected
    leftOccurs rightOccurs leftLookup rightLookup leftChain rightChain iso leftSafe rightSafe
  have oldPieces : (sourceSelection out.leftLast).fragment.segments=
      (sourceSelection out.rightLast).fragment.segments := by
    classical
    exact Classical.byContradiction (fun unequal=>
      representation.2 out.leftLast out.rightLast out.leftAux out.rightAux out.sameLabel unequal
        ⟨out.sourceIso,out.targetIso⟩)
  obtain ⟨localTarget,localHistory,_erase,_matching,edge,selection,geometry,allChildren⟩ :=
    site.beta_evaluated_child_residuals closed matching inputs flow positive balance rootDepth transparency
      relative normal event.final_history
  have localStep : StepAt chosen (initLabels source.erase) localTarget := by
    cases localHistory with
    | cons first rest => cases rest;exact first
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
  have heads := selection.first_copy_argument_evaluations_eq matching event.redex localStep
    leftOccurs rightOccurs out.left.lastPath out.right.lastPath
    (sourceSelection out.leftLast) (sourceSelection out.rightLast)
    leftLocalLookup rightLocalLookup edge oldPieces
  simp only [leftAt,reindexOccurrence_segments] at leftResidual
  simp only [rightAt,reindexOccurrence_segments] at rightResidual
  have raw := leftResidual.target_unique site geometry rightResidual heads
  have pieces := mapped_lists_injective (plugEnd _ _).symm.injective raw
  exact ⟨localTarget,localHistory,edge,selection,geometry,ln,rn,leftLocalLookup,rightLocalLookup,
    heads,leftNonempty,rightNonempty,leftResidual,rightResidual,pieces⟩
end

#print axioms PathSite.beta_first_copy_argument_pieces
end Lamping.AG
