import Lamping.Lamping.LocalBetaSelectorResidual
import Lamping.Lamping.BetaCanonicalComparison

namespace Lamping.AG
open Graph Lambda Lambda.Labelled

private theorem list_map_injective {A C : Type} {f : A → C}
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
variable {kept : K → Graph.Label signature} {i : Nat}
variable (site : PathSite (.beta i) kept (B:=B) (W:=W) (V:=V))

/-- The evaluator block at an actual child cannot disappear: otherwise the
same-edge residual uniqueness identifies the parent and child root accesses,
whose actual syntax words differ by one final token. No safe-label premise. -/
theorem BetaPathResidual.child_evaluator_nonempty
    {root : B} {edge : BetaEdge site.net} (geometry : SiteBetaGeometry site edge)
    (parent child : RootAccess site.reduce root) {p : Path} {step : Step}
    (parentWord : accessWord site.reduce parent.val=p)
    (childWord : accessWord site.reduce child.val=p++[step])
    {parentOld oldPiece : List (Endpoint site.net)}
    (parentResidual : BetaPathResidual site edge (parent.val.map (plugEnd _ _).invFun) parentOld)
    (childResidual : BetaPathResidual site edge (child.val.map (plugEnd _ _).invFun) (parentOld++oldPiece)) :
    oldPiece≠[] := by
  intro empty
  have sameOld : parentOld++oldPiece=parentOld := by rw [empty,List.append_nil]
  have rawSame := childResidual.target_unique site geometry parentResidual sameOld
  have accessSame : child.val=parent.val :=
    list_map_injective (plugEnd _ _).symm.injective rawSame
  have words : p++[step]=p := childWord.symm.trans ((congrArg (accessWord site.reduce) accessSame).trans parentWord)
  have lengths := congrArg List.length words
  simp only [List.length_append,List.length_cons,List.length_nil] at lengths
  omega

/-- ONE actual development producer supplies literal evaluator residuals for
every specified syntax child, including marked incoming edges. The local
annotation records geometry only; no global family history is reinitialized.
The old block is an evaluator value, not an asserted global old occurrence. -/
theorem PathSite.beta_evaluated_child_residuals
    {root : B} {source target : LTerm} {ps : List Path} {marked : Marked}
    (closed : Closed source.erase) (matching : Matches site.net root source.erase)
    (inputs : RootInputs site.net root)
    {boundary : B → Bool} (flow : FlowBalance site.net boundary) (positive : boundary root=true)
    {heights : B → Int} (balance : IndexedLevelBalance site.net heights) (rootDepth : heights root=0)
    (transparency : Transparency site.net root)
    (relative : Marked.RelativeHistory ps (Marked.mark (site.betaSyntaxFiber root source.erase) source.erase) marked)
    (normal : Marked.Normal marked) (history : History ps source target) :
    ∃ localTarget,History ps (initLabels source.erase) localTarget ∧
      localTarget.erase=target.erase ∧Matches site.reduce root target.erase ∧
      ∃ edge : BetaEdge site.net,∃ selection : SourceEdgeSelection (initLabels source.erase) site.net root,
        SiteBetaGeometry site edge ∧
        ∀ (p : Path) (step : Step) (parentTerm : LTerm),target.subterm p=some parentTerm →
          ∀ child : OccurrenceFragment target site.reduce root (p++[step]),
            SourceDeparture parentTerm step (sourceEdge child.environment child.context child.term).fromPort →
            ∃ localChild,localTarget.subterm (p++[step])=some localChild ∧
              localChild.erase=child.term.erase ∧selection.evalLabel edge localChild.label≠[] ∧
              BetaPathResidual site edge (child.fragment.segments.map (plugEnd _ _).invFun)
                (selection.evalLabel edge localChild.label) := by
  obtain ⟨localTarget,localLabels,sameErase,targetMatching,edge,selection,geometry,all⟩ :=
    site.beta_local_selector_residuals closed matching inputs flow positive balance rootDepth transparency
      relative normal history
  refine ⟨localTarget,localLabels,sameErase,targetMatching,edge,selection,geometry,?_⟩
  intro p step parentTerm atParent child role
  let parentPosition : Position target.erase := ⟨p,by rw [←LTerm.erase_subterm,atParent];rfl⟩
  obtain ⟨parent,parentWord,_shape⟩ := Matches.observation _ targetMatching parentPosition
  obtain ⟨localParent,localParentLookup,_parentErase,parentFinish,parentTrail,parentOutput,parentNode,parentPort,
    parentEvaluation,parentResidual,_parentLabels,parentEnd,_parentKind⟩ :=
    all atParent parent parentWord Context.empty
  obtain ⟨localChild,localChildLookup,childErase,childFinish,childTrail,childOutput,_childNode,_childPort,
    childEvaluation,childResidual,_childLabels,_childEnd,_childKind⟩ :=
    all child.occurrence.lookup child.fragment.access child.fragment.word Context.empty
  have atChild : localParent.subterm [step]=some localChild := by
    have lookup := localChildLookup
    rw [LTerm.subterm_append,localParentLookup] at lookup
    exact lookup
  have oldSplit : childTrail.edges=parentTrail.edges++selection.evalLabel edge localChild.label := by
    have evaluation := LTerm.sourceTrail_single_child_evaluation selection.atomWord edge.principal edge.reverseRoute
      localParentLookup atChild
    rw [childEvaluation,parentEvaluation,Option.map_some] at evaluation
    exact Option.some.inj evaluation
  have childWord : (p++[step])=accessWord site.reduce parent.val++[step] := by rw [parentWord]
  have newSplit := (child.fragment.child_prefix targetMatching role parent childWord).2
  have rawSplit := congrArg (fun xs : List (Endpoint site.reduce)=>xs.map (plugEnd _ _).invFun) newSplit
  simp only [List.map_append] at rawSplit
  have parentLast : parentTrail.edges.getLast?=some (site.net.wire (.inl ⟨.inl parentNode,parentPort⟩)) := by
    rw [←parentEnd]
    exact parentTrail.last
  have nonempty : selection.evalLabel edge localChild.label≠[] := by
    rw [oldSplit] at childResidual
    exact BetaPathResidual.child_evaluator_nonempty site geometry parent child.fragment.access
      parentWord child.fragment.word parentResidual childResidual
  refine ⟨localChild,localChildLookup,childErase,nonempty,?_⟩
  exact childResidual.cut_at_kept_prefix site geometry parentResidual oldSplit rawSplit
    parentNode parentPort parentLast nonempty
end

#print axioms BetaPathResidual.child_evaluator_nonempty
#print axioms PathSite.beta_evaluated_child_residuals
end Lamping.AG
