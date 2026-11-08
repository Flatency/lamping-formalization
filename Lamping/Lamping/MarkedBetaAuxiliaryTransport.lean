import Lamping.Lamping.MarkedAuxiliaryEvaluations
import Lamping.Lamping.SafeBetaAuxiliaryTransport
import Lamping.Lamping.BetaEvaluatedChildResiduals

namespace Lamping.AG
open Graph Lambda Lambda.Labelled

private theorem list_map_cancel {A C : Type} {f : A→C}
    (injective : Function.Injective f) {xs ys : List A} (same : xs.map f=ys.map f) : xs=ys := by
  induction xs generalizing ys with
  | nil => cases ys <;> simp_all
  | cons x xs ih =>
    cases ys with
    | nil => cases same
    | cons y ys =>
      obtain ⟨head,tail⟩:=List.cons.inj same
      rw [injective head,ih tail]

theorem PathSite.beta_marked_auxiliary_pair
    {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
    {kept : K → Graph.Label signature} {i : Nat}
    (site : PathSite (.beta i) kept (B:=B) (W:=W) (V:=V))
    {root : B} {original source target : LTerm} {ps : List Path} {marked : Marked}
    {degree : Lambda.Labelled.Label}
    (initial : INIT original)
    (prior : ParallelHistory original.erase source.erase)
    (completePrior : CompleteDerivation prior)
    (prefixHistory : History prior.derivation.paths original source)
    (closed : Closed source.erase)
    (matching : Matches site.net root source.erase)
    (inputs : RootInputs site.net root)
    {boundary : B → Bool} (flow : FlowBalance site.net boundary)
    (positive : boundary root=true)
    {heights : B → Int} (balance : IndexedLevelBalance site.net heights)
    (rootDepth : heights root=0)
    (oldT : Transparency site.net root)
    (relative : Marked.RelativeHistory ps
      (Marked.mark (site.betaSyntaxFiber root source.erase) source.erase) marked)
    (normal : Marked.Normal marked)
    (labels : History ps source target)
    (sourceSelection : OccurrenceFragmentSelection source site.net root)
    (targetSelection : OccurrenceFragmentSelection target site.reduce root)
    (sourceJoint : JointRepresentation closed sourceSelection)
    (representative : RedexOcc source.erase)
    (member : representative.val ∈ site.betaSyntaxFiber root source.erase)
    (atDegree : source.degreeAt representative.val=some degree)
    (left right : SyntaxIncidence.Edge target)
    (leftAux : AuxiliaryAt target left.val)
    (rightAux : AuxiliaryAt target right.val)
    (sameLabel : SyntaxIncidence.label target left=SyntaxIncidence.label target right)
    (leftMarked : ¬(SyntaxIncidence.label target left).OuterBarsSafe (fun x=>x≠degree))
    (sourceIso : SuccessfulEndpointIso target (labels.closed closed)
      (SyntaxIncidence.source target left) (SyntaxIncidence.source target right))
    (targetIso : SuccessfulEndpointIso target (labels.closed closed)
      (SyntaxIncidence.target target (labels.closed closed) left)
      (SyntaxIncidence.target target (labels.closed closed) right)) :
    (targetSelection left).fragment.segments=(targetSelection right).fragment.segments := by
  have sourceSafe:=complete_prefix_outer_bars_fresh initial prior completePrior prefixHistory representative atDegree
  have selected (path : Path) (inside : path∈site.betaSyntaxFiber root source.erase) :
      source.degreeAt path=some degree := by
    obtain ⟨candidate,_access,same,_app,_lam⟩:=
      (mem_physicalBetaFiberPaths site.net root source.erase (.inr (.inl ())) (.inr (.inr ())) path).mp inside
    have chosen : candidate.val∈site.betaSyntaxFiber root source.erase:=same.symm ▸ inside
    have equal:=(site.beta_fiber_iff_degree closed matching sourceSelection sourceJoint.1
      representative member candidate).mp chosen
    rw [same] at equal
    exact equal.trans atDegree
  have old:=(Marked.relativeOld_iff_relative
    (Marked.selected_mark (site.betaSyntaxFiber root source.erase) source.erase)).mpr relative
  obtain ⟨localTarget,localHistory,_erase,_targetMatching,physical,selection,geometry,all⟩:=
    site.beta_evaluated_child_residuals closed matching inputs flow positive balance rootDepth oldT
      relative normal labels
  have evaluated (edge : SyntaxIncidence.Edge target)
      (fragment : OccurrenceFragment target site.reduce root edge.val)
      (available : ∃es,EndpointChain target (SyntaxIncidence.source target edge) es) :
      ∃localNode,localTarget.subterm edge.val=some localNode ∧
        BetaPathResidual site physical (fragment.fragment.segments.map (plugEnd _ _).invFun)
          (selection.evalLabel physical localNode.label) := by
    rcases edge with ⟨path,valid⟩
    rcases fragment.occurrence.last_departure with ⟨rootAt,_context⟩ |⟨parent,step,parentTerm,split,atParent,role⟩
    · have sourceNone : SyntaxIncidence.source target ⟨path,valid⟩=none :=
        SyntaxIncidence.source_eq_of_spec target ⟨path,valid⟩ rootAt
      obtain ⟨es,chain⟩:=available
      rw [sourceNone] at chain
      exact False.elim chain
    · change path=parent++[step] at split
      subst path
      obtain ⟨localNode,atLocal,_sameErase,_nonempty,residual⟩:=
        all parent step parentTerm atParent fragment
          (by simpa only [InteriorSourceBlock.source_edge_departure] using role)
      exact ⟨localNode,atLocal,residual⟩
  obtain ⟨localLeft,leftLocal,leftResidual⟩:=evaluated left (targetSelection left) sourceIso.left_available
  obtain ⟨localRight,rightLocal,rightResidual⟩:=evaluated right (targetSelection right) sourceIso.right_available
  have whole:=marked_auxiliary_whole_evaluations initial prefixHistory old labels selected sourceSafe closed
    matching sourceSelection sourceJoint localHistory left right
    (targetSelection left).occurrence.lookup (targetSelection right).occurrence.lookup
    leftLocal rightLocal leftAux rightAux sameLabel leftMarked sourceIso targetIso selection physical
  have raw:=leftResidual.target_unique site geometry rightResidual whole
  exact list_map_cancel (plugEnd _ _).symm.injective raw

end Lamping.AG
#print axioms Lamping.AG.PathSite.beta_marked_auxiliary_pair
