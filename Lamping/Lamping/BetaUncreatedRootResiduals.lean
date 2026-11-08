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

/-- The root edge is a whole actual access. Its old fragment is aligned by
the SAME operational history and local evaluator, without a nonroot cut. -/
theorem PathSite.beta_uncreated_root_residuals
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
      ∀ child : OccurrenceFragment target site.reduce root [],
        child.term.label.OuterBarsSafe (fun payload=>payload≠degree) →
        ∃ oldPosition oldNode,source.subterm oldPosition=some oldNode ∧
          BetaNodeHistoryPreimage history [] oldPosition ∧
          ∀ oldFragment : OccurrenceFragment source site.net root oldPosition,
            BetaPathResidual site edge (child.fragment.segments.map (plugEnd _ _).invFun)
              oldFragment.fragment.segments := by
  obtain ⟨localTarget,localLabels,_sameErase,targetMatching,edge,selection,geometry,all⟩ :=
    site.beta_local_selector_residuals closed matching inputs flow positive balance rootDepth transparency
      relative normal history
  refine ⟨edge,geometry,?_⟩
  intro child safe
  obtain ⟨localChild,localLookup,_childErase,finish,trail,output,node,port,
    evaluation,residual,_labels,_ending,_kind⟩ :=
    all child.occurrence.lookup child.fragment.access child.fragment.word Context.empty
  obtain ⟨oldPosition,oldNode,oldLookup,trace,block⟩ :=
    selection.marker_free_local_evaluation matching old aligned history localLabels selected
      child.occurrence.lookup localLookup safe edge
  refine ⟨oldPosition,oldNode,oldLookup,trace,?_⟩
  intro oldFragment
  have rootOccurrence := child.occurrence.same_occurrence
    (SourceSubterm.nil (t:=target) (env:=[]) (ctx:=.external))
  obtain ⟨_environment,context,_term⟩ := rootOccurrence
  have external : (sourceEdge child.environment child.context child.term).fromPort=.external := by
    rw [context]
    cases child.term <;> rfl
  have whole := child.fragment.external_segments external
  have atRoot : localChild=localTarget := by
    exact Option.some.inj (by simpa only [LTerm.subterm] using localLookup.symm)
  have evaluated : selection.evalLabel edge localChild.label=trail.edges := by
    subst localChild
    exact Option.some.inj (by simpa only [LTerm.sourceTrail,SourceEdgeSelection.evalLabel] using evaluation)
  rw [←whole,←evaluated,block oldFragment] at residual
  exact residual
end
end Lamping.AG

