import Lamping.Lamping.HistoryGeneratedCopyStep
import Lamping.Lamping.StepPositionEvaluationOrigins
namespace Lamping.AG
open Graph Lambda Lambda.Labelled
section
variable {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K → Graph.Label signature} {i : Nat}

/-- The ENTIRE generated-path component advances through an actual event.
The P/L arguments refer only to its previous state. The new generated path
is constructed at every real target position by retained/outside origins or
the actual copy step. The target binder invariant and labels are separate. -/
theorem PathSite.relative_generated_paths_step
    (site : PathSite (.beta i) kept (B:=B) (W:=W) (V:=V))
    {root : B} {original : LTerm} (initial : INIT original) (matching : Matches site.net root original.erase)
    (selection : SourceEdgeSelection original site.net root) (beta : BetaEdge site.net)
    (app : beta.app=.inr (.inl ())) (lam : beta.lam=.inr (.inr ()))
    (allPorts : ∀ {degree appId lamId},SelectedDegree original (site.betaSyntaxFiber root original.erase) degree →
      SourceRoute (sourceEdges [] .external original) (.appFn appId) degree (.lamContext lamId) →
      degree=lamId ∧BetaSourcePorts original root beta appId lamId)
    (allWalks : ∀ {start stamp finish},SelectedSourceRoute (sourceEdges [] .external original)
      (SelectedDegree original (site.betaSyntaxFiber root original.erase)) start stamp finish →
      ∃ walk : PhysicalSourceWalk original root beta start stamp finish,walk.edges=selection.evalLabel beta stamp)
    {ps : List Path} {p : Path} {current target : LTerm} {markedBefore markedAfter : Marked}
    (relativeBefore : Marked.RelativeHistory ps (Marked.mark (site.betaSyntaxFiber root original.erase) original.erase) markedBefore)
    (relativeAfter : Marked.RelativeHistory (ps++[p]) (Marked.mark (site.betaSyntaxFiber root original.erase) original.erase) markedAfter)
    (prior : History ps original current) (step : StepAt p current target)
    {stamp degree : Labelled.Label} {body argument : LTerm}
    (lookup : current.subterm p=some (.app stamp (.lam degree body) argument))
    (paths : GeneratedSyntaxPaths selection beta current)
    (binders : SupportedSyntaxBinders selection beta current) :
    GeneratedSyntaxPaths selection beta target := by
  have degreeAt : current.degreeAt p=some degree := by
    simp only [LTerm.degreeAt,lookup,Option.bind_some,LTerm.degree]
  have selected := relative_last_selected_degree initial relativeAfter prior step degreeAt
  have active := site.selected_principal_word_at initial matching selection beta app lam selected
  intro position sub atTarget
  rcases step.sourceTrail_position_origins selection.atomWord beta.principal beta.reverseRoute
      lookup active atTarget with ⟨oldPosition,oldSub,oldLookup,sameWord⟩ | ⟨q,r,argSub,split,occurs,atArgument⟩
  · obtain ⟨word,eval,generated⟩ := paths oldLookup
    exact ⟨word,sameWord.trans eval,generated⟩
  · rw [split]
    exact site.relative_generated_copy_step initial matching selection beta app lam allPorts allWalks
      relativeBefore relativeAfter prior step lookup occurs atArgument paths binders
end
end Lamping.AG
