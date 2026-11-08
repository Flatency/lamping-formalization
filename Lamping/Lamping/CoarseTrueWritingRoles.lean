import Lamping.Lamping.WritingLetterBlocks
import Lamping.Lamping.CompletedLocalAtomRoles

namespace Lamping.AG
open Graph Lambda Lambda.Labelled

def coarseLetterTag : Letter → Nat
  | .atom _ => 0
  | .over _ => 1
  | .under _ => 2

private theorem principal_ne_reverse {N B W : Type}
    [FiniteNames N] [FiniteNames B] [FiniteNames W]
    {g : Net signature N B W} (edge : BetaEdge g) : edge.principal≠edge.reverseRoute := by
  intro same
  have starts := Option.some.inj (edge.principalStart.symm.trans (same ▸ edge.reverse_start))
  have nodes : edge.app=edge.lam := congrArg Sigma.fst (Sum.inl.inj starts)
  have impossible := edge.appLabel.symm.trans ((congrArg g.label nodes).trans edge.lamLabel)
  cases impossible

private theorem letter_tag_of_word {N B W : Type}
    [FiniteNames N] [FiniteNames B] [FiniteNames W]
    {g : Net signature N B W} {original : LTerm} {root : B}
    (selection : SourceEdgeSelection original g root) (edge : BetaEdge g)
    (x y : Letter)
    (leftAtoms : ∀n,x=Letter.atom n →selection.atomWord n≠edge.principal ∧selection.atomWord n≠edge.reverseRoute)
    (rightAtoms : ∀n,y=Letter.atom n →selection.atomWord n≠edge.principal ∧selection.atomWord n≠edge.reverseRoute)
    (same : x.sourceWord selection.atomWord edge.principal edge.reverseRoute=
      y.sourceWord selection.atomWord edge.principal edge.reverseRoute) :
    coarseLetterTag x=coarseLetterTag y := by
  cases x with
  | atom n =>
    cases y with
    | atom m => rfl
    | over d => exact False.elim ((leftAtoms n rfl).1 same)
    | under d => exact False.elim ((leftAtoms n rfl).2 same)
  | over d =>
    cases y with
    | atom m => exact False.elim ((rightAtoms m rfl).1 same.symm)
    | over e => rfl
    | under e => exact False.elim (principal_ne_reverse edge same)
  | under d =>
    cases y with
    | atom m => exact False.elim ((rightAtoms m rfl).2 same.symm)
    | over e => exact False.elim (principal_ne_reverse edge same.symm)
    | under e => rfl

private theorem tags_of_blocks {N B W : Type}
    [FiniteNames N] [FiniteNames B] [FiniteNames W]
    {g : Net signature N B W} {original : LTerm} {root : B}
    (selection : SourceEdgeSelection original g root) (edge : BetaEdge g)
    (xs ys : List Letter)
    (leftAtoms : ∀n,Letter.atom n∈xs →selection.atomWord n≠edge.principal ∧selection.atomWord n≠edge.reverseRoute)
    (rightAtoms : ∀n,Letter.atom n∈ys →selection.atomWord n≠edge.principal ∧selection.atomWord n≠edge.reverseRoute)
    (same : xs.map (fun x=>x.sourceWord selection.atomWord edge.principal edge.reverseRoute)=
      ys.map (fun x=>x.sourceWord selection.atomWord edge.principal edge.reverseRoute)) :
    xs.map coarseLetterTag=ys.map coarseLetterTag := by
  induction xs generalizing ys with
  | nil =>
    cases ys with
    | nil => rfl
    | cons y ys => cases same
  | cons x xs ih =>
    cases ys with
    | nil => cases same
    | cons y ys =>
      have pair := List.cons.inj same
      have tags := letter_tag_of_word selection edge x y
        (by intro n eq;exact leftAtoms n (by rw [eq];exact List.mem_cons_self))
        (by intro n eq;exact rightAtoms n (by rw [eq];exact List.mem_cons_self)) pair.1
      have tail := ih ys
        (by intro n inside;exact leftAtoms n (List.mem_cons_of_mem _ inside))
        (by intro n inside;exact rightAtoms n (List.mem_cons_of_mem _ inside)) pair.2
      simp only [List.map_cons,tags,tail]

theorem EvaluatedChainResiduals.coarse_true_role_profiles
    {K B W V : Type}
    [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
    {kept : K → Graph.Label signature} {i : Nat}
    (site : PathSite (.beta i) kept (B:=B) (W:=W) (V:=V))
    {root : B} {source target localTarget : LTerm}
    {ps : List Path} {marked : Marked}
    {edge : BetaEdge site.net}
    {selection : SourceEdgeSelection (initLabels source.erase) site.net root}
    {targetSelection : OccurrenceFragmentSelection target site.reduce root}
    {ls rs : Path} {les res : List Path}
    {leftChain : PrerequisiteChain target ls les}
    {rightChain : PrerequisiteChain target rs res}
    (matching : Matches site.net root source.erase)
    {boundary : B → Bool} (flow : FlowBalance site.net boundary)
    (positive : boundary root=true)
    (relative : Marked.RelativeHistory ps
      (Marked.mark (site.betaSyntaxFiber root source.erase) source.erase) marked)
    (normal : Marked.Normal marked)
    (localHistory : History ps (initLabels source.erase) localTarget)
    (geometry : SiteBetaGeometry site edge)
    (left : EvaluatedChainResiduals site (localTarget:=localTarget)
      edge selection targetSelection leftChain)
    (right : EvaluatedChainResiduals site (localTarget:=localTarget)
      edge selection targetSelection rightChain)
    (same : SameChainRepresentation targetSelection leftChain rightChain) :
    les.attach.map (fun member =>
      (left.node member).label.letters.map coarseLetterTag) =
    res.attach.map (fun member =>
      (right.node member).label.letters.map coarseLetterTag) := by
  have blocks := left.blocks_eq_of_target_images site geometry right same
  have length : les.length=res.length := by
    have lengths := congrArg List.length blocks
    simpa only [EvaluatedChainResiduals.blocks,List.length_map,List.length_attach] using lengths
  apply List.ext_getElem (by simpa only [List.length_map,List.length_attach] using length)
  intro k leftBound rightBound
  have lb : k<les.length := by simpa only [List.length_map,List.length_attach] using leftBound
  have rb : k<res.length := by simpa only [List.length_map,List.length_attach] using rightBound
  have lab : k<les.attach.length := by simpa only [List.length_attach] using lb
  have rab : k<res.attach.length := by simpa only [List.length_attach] using rb
  let lm : {p : Path //p∈les} := les.attach[k]'(by simpa using lb)
  let rm : {p : Path //p∈res} := res.attach[k]'(by simpa using rb)
  have slot : selection.evalLabel edge (left.node lm).label=
      selection.evalLabel edge (right.node rm).label := by
    have atSlot := congrArg (fun xs : List (List (Endpoint site.net))=>xs[k]?) blocks
    simpa only [EvaluatedChainResiduals.blocks,List.getElem?_map,List.getElem?_eq_getElem lab,
      List.getElem?_eq_getElem rab,Option.map_some,Option.some.injEq,List.getElem_attach,lm,rm] using atSlot
  have lr := left.writing_letter_blocks_regular site (init_is_INIT source.erase) localHistory lm
  have rr := right.writing_letter_blocks_regular site (init_is_INIT source.erase) localHistory rm
  have perLetter := proper_ended_control_blocks_unique lr.2.2 rr.2.2
    (lr.2.1.trans (slot.trans rr.2.1.symm))
  have la := site.complete_local_outer_atoms_not_beta_routes geometry selection matching flow positive
    relative normal localHistory (left.lookup lm)
  have ra := site.complete_local_outer_atoms_not_beta_routes geometry selection matching flow positive
    relative normal localHistory (right.lookup rm)
  have tags := tags_of_blocks selection edge _ _ la ra perLetter
  simpa only [List.getElem_map,lm,rm] using tags


end Lamping.AG
