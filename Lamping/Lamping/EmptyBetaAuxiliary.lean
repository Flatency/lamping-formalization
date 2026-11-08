import Lamping.Lamping.InteriorSourceBlockEndpoints
import Lamping.Lamping.FamilyRepresentation
import Lamping.Lamping.BetaEvaluatedChildResiduals
import Lamping.Lamping.LocalSourceFragmentEvaluation

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

theorem PathSite.beta_empty_auxiliary_preserve
    {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
    {kept : K → Graph.Label signature} {i : Nat}
    (site : PathSite (.beta i) kept (B:=B) (W:=W) (V:=V))
    {root : B} {source target : LTerm} {ps : List Path} {marked : Marked}
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
    (empty : site.betaSyntaxFiber root source.erase=[]) :
    AuxiliarySeparation (labels.closed closed) targetSelection := by
  have complete := (Marked.completeOld_iff
    (site.betaSyntaxFiber root source.erase) source.erase).mpr ⟨relative,normal⟩
  have noSteps := (physicalBetaFiber_complete_empty complete empty).1
  subst ps
  cases labels
  obtain ⟨localTarget,localHistory,_erase,_targetMatching,physical,selection,geometry,all⟩:=
    site.beta_evaluated_child_residuals closed matching inputs flow positive balance rootDepth oldT
      relative normal (.nil source)
  cases localHistory
  have evaluated (edge : SyntaxIncidence.Edge source)
      (fragment : OccurrenceFragment source site.reduce root edge.val)
      (available : ∃es,EndpointChain source (SyntaxIncidence.source source edge) es) :
      BetaPathResidual site physical (fragment.fragment.segments.map (plugEnd _ _).invFun)
        (sourceSelection edge).fragment.segments := by
    rcases edge with ⟨path,valid⟩
    rcases fragment.occurrence.last_departure with ⟨rootAt,_context⟩ |⟨parent,step,parentTerm,split,atParent,role⟩
    · have sourceNone : SyntaxIncidence.source source ⟨path,valid⟩=none :=
        SyntaxIncidence.source_eq_of_spec source ⟨path,valid⟩ rootAt
      obtain ⟨es,chain⟩:=available
      rw [sourceNone] at chain
      exact False.elim chain
    · change path=parent++[step] at split
      subst path
      obtain ⟨localNode,atLocal,_sameErase,_nonempty,residual⟩:=
        all parent step parentTerm atParent fragment
          (by simpa only [InteriorSourceBlock.source_edge_departure] using role)
      obtain ⟨env,ctx,occurrence⟩:=
        SourceSubterm.of_lookup (initLabels source.erase) atLocal [] .external
      have localMatching : Matches site.net root (initLabels source.erase).erase := by
        simpa only [erase_initLabels] using matching
      have evaluation := selection.evalLabel_occurrence_segments (init_is_INIT source.erase)
        localMatching matching occurrence (sourceSelection ⟨parent++[step],valid⟩) physical
      rw [evaluation] at residual
      exact residual
  intro left right leftAux rightAux sameLabel different isos
  rcases isos with ⟨sourceIso,targetIso⟩
  have oldEq : (sourceSelection left).fragment.segments=(sourceSelection right).fragment.segments := by
    apply Classical.byContradiction
    intro ne
    exact sourceJoint.2 left right leftAux rightAux sameLabel ne ⟨sourceIso,targetIso⟩
  have leftResidual := evaluated left (targetSelection left) sourceIso.left_available
  have rightResidual := evaluated right (targetSelection right) sourceIso.right_available
  have raw := leftResidual.target_unique site geometry rightResidual oldEq
  exact different (list_map_cancel (plugEnd _ _).symm.injective raw)

end Lamping.AG
#print axioms Lamping.AG.PathSite.beta_empty_auxiliary_preserve
