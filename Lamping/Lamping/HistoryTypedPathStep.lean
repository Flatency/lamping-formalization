import Lamping.Lamping.HistoryTypedCopyStep
import Lamping.Lamping.StepPositionEvaluationOrigins
namespace Lamping.AG
open Graph Lambda Lambda.Labelled
section
variable {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K → Graph.Label signature} {i : Nat}

/-- Every actual target lookup preserves typed path totality from OLD typed
paths and OLD specified-binder shells. Actual origin classification handles
retained/outside words; the copied case constructs the inserted assignment.
No target typed-path or target binder property is supplied by the caller. -/
theorem PathSite.relative_typed_paths_step
    (site : PathSite (.beta i) kept (B:=B) (W:=W) (V:=V))
    {root : B} {original : LTerm} (initial : INIT original) (matching : Matches site.net root original.erase)
    (selection : SourceEdgeSelection original site.net root) (beta : BetaEdge site.net)
    (app : beta.app=.inr (.inl ())) (lam : beta.lam=.inr (.inr ()))
    (inputs : RootInputs site.net root) {boundary : B → Bool} (flow : FlowBalance site.net boundary)
    (positive : boundary root=true) {heights : B → Int} (balance : IndexedLevelBalance site.net heights)
    (rootDepth : heights root=0) (transparency : Transparency site.net root)
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
    (paths : TypedSyntaxPaths selection beta current)
    (binders : SupportedSyntaxBinders selection beta current)
    (typedBinders : TypedSyntaxBinders selection beta current) :
    TypedSyntaxPaths selection beta target := by
  have degreeAt : current.degreeAt p=some degree := by
    simp only [LTerm.degreeAt,lookup,Option.bind_some,LTerm.degree]
  have selected := relative_last_selected_degree initial relativeAfter prior step degreeAt
  have active := site.selected_principal_word_at initial matching selection beta app lam selected
  intro position sub atTarget
  rcases step.sourceTrail_position_origins selection.atomWord beta.principal beta.reverseRoute
      lookup active atTarget with ⟨oldPosition,oldSub,oldLookup,sameWord⟩ | ⟨q,r,argSub,split,occurs,atArgument⟩
  · obtain ⟨word,eval,assigned⟩ := paths oldLookup
    exact ⟨word,sameWord.trans eval,assigned⟩
  · rw [split]
    exact site.relative_typed_copy_step initial matching selection beta app lam inputs flow positive balance rootDepth transparency allPorts allWalks
      relativeBefore relativeAfter prior step lookup occurs atArgument paths binders typedBinders
end
end Lamping.AG
