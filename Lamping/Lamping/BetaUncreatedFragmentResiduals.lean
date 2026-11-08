import Lamping.Lamping.LocalBetaSelectorResidual
import Lamping.Lamping.BetaCanonicalComparison
import Lamping.Lamping.BetaAtomicComparison

namespace Lamping.AG
open Graph Lambda Lambda.Labelled
section
variable {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K → Graph.Label signature} {i : Nat}
variable (site : PathSite (.beta i) kept (B:=B) (W:=W) (V:=V))
variable {root : B} {source target : LTerm} {ps F : List Path} {marked m n : Marked}
variable {d : Path →Option Labelled.Label} {degree : Labelled.Label}

/-- ONE actual complete physical development supplies every nonroot old
fragment's specified target residual. The parent and whole paths, their
literal cuts and retained seam are constructed internally. The global OLD
history alone supplies the original coordinate; local INIT is geometry. -/
theorem PathSite.beta_uncreated_child_residuals
    (closed : Closed source.erase) (matching : Matches site.net root source.erase)
    (inputs : RootInputs site.net root)
    {boundary : B → Bool} (flow : FlowBalance site.net boundary) (positive : boundary root=true)
    {heights : B → Int} (balance : IndexedLevelBalance site.net heights) (rootDepth : heights root=0)
    (transparency : Transparency site.net root)
    (relative : Marked.RelativeHistory ps (Marked.mark (site.betaSyntaxFiber root source.erase) source.erase) marked)
    (normal : Marked.Normal marked) (history : History ps source target)
    (old : Marked.RelativeOldHistory F ps m n) (aligned : DegreeAligned d m source)
    (selected : ∀ path∈F,d path=some degree) :
    ∃ edge : BetaEdge site.net,SiteBetaGeometry site edge ∧
      ∀ (p : Path) (step : Step) (parentTerm : LTerm),target.subterm p=some parentTerm →
        ∀ child : OccurrenceFragment target site.reduce root (p++[step]),
          SourceDeparture parentTerm step (sourceEdge child.environment child.context child.term).fromPort →
          child.term.label.OuterBarsSafe (fun payload=>payload≠degree) →
          ∃ oldPosition oldNode,source.subterm oldPosition=some oldNode ∧
            BetaNodeHistoryPreimage history (p++[step]) oldPosition ∧
            ∀ oldFragment : OccurrenceFragment source site.net root oldPosition,
              BetaPathResidual site edge (child.fragment.segments.map (plugEnd _ _).invFun)
                oldFragment.fragment.segments := by
  obtain ⟨localTarget,localLabels,_sameErase,targetMatching,edge,selection,geometry,all⟩ :=
    site.beta_local_selector_residuals closed matching inputs flow positive balance rootDepth transparency
      relative normal history
  refine ⟨edge,geometry,?_⟩
  intro p step parentTerm atParent child role safe
  let parentPosition : Position target.erase := ⟨p,by rw [←LTerm.erase_subterm,atParent];rfl⟩
  obtain ⟨parent,parentWord,_shape⟩ := Matches.observation _ targetMatching parentPosition
  obtain ⟨localParent,localParentLookup,_parentErase,parentFinish,parentTrail,parentOutput,parentNode,parentPort,
    parentEvaluation,parentResidual,_parentLabels,parentEnd,_parentKind⟩ :=
    all atParent parent parentWord Context.empty
  obtain ⟨localChild,localChildLookup,_childErase,childFinish,childTrail,childOutput,_childNode,_childPort,
    childEvaluation,childResidual,_childLabels,_childEnd,_childKind⟩ :=
    all child.occurrence.lookup child.fragment.access child.fragment.word Context.empty
  obtain ⟨oldPosition,oldNode,oldLookup,trace,block⟩ :=
    selection.marker_free_local_evaluation matching old aligned history localLabels selected
      child.occurrence.lookup localChildLookup safe edge
  refine ⟨oldPosition,oldNode,oldLookup,trace,?_⟩
  intro oldFragment
  have atChild : localParent.subterm [step]=some localChild := by
    have lookup := localChildLookup
    rw [LTerm.subterm_append,localParentLookup] at lookup
    exact lookup
  have oldSplit : childTrail.edges=parentTrail.edges++oldFragment.fragment.segments := by
    have evaluation := LTerm.sourceTrail_single_child_evaluation selection.atomWord edge.principal edge.reverseRoute
      localParentLookup atChild
    rw [childEvaluation,parentEvaluation,Option.map_some] at evaluation
    change some childTrail.edges=some (parentTrail.edges++selection.evalLabel edge localChild.label) at evaluation
    rw [block oldFragment] at evaluation
    exact Option.some.inj evaluation
  have childWord : (p++[step])=accessWord site.reduce parent.val++[step] := by rw [parentWord]
  have newSplit := (child.fragment.child_prefix targetMatching role parent childWord).2
  have rawSplit := congrArg (fun xs : List (Endpoint site.reduce)=>xs.map (plugEnd _ _).invFun) newSplit
  simp only [List.map_append] at rawSplit
  have parentLast : parentTrail.edges.getLast?=some (site.net.wire (.inl ⟨.inl parentNode,parentPort⟩)) := by
    rw [←parentEnd]
    exact parentTrail.last
  have nonempty : oldFragment.fragment.segments≠[] := by
    intro empty
    have first := oldFragment.fragment.start
    rw [empty] at first
    cases first
  exact childResidual.cut_at_kept_prefix site geometry parentResidual oldSplit rawSplit
    parentNode parentPort parentLast nonempty
end
end Lamping.AG
