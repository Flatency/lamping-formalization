import Lamping.Lamping.HistorySupportedStep
import Lamping.Lamping.HistoryTypedPathStep
import Lamping.Lamping.HistoryTypedBinderStep
import Lamping.Lamping.MatchingSpecifiedBindingShell
namespace Lamping.AG
open Graph Lambda Lambda.Labelled

private theorem relative_split {ps qs : List Path} {source target : Marked}
    (history : Marked.RelativeHistory (ps++qs) source target) :
    ∃ middle,Marked.RelativeHistory ps source middle ∧Marked.RelativeHistory qs middle target := by
  induction ps generalizing source with
  | nil => exact ⟨source,.nil _,history⟩
  | cons p ps ih =>
    cases history with
    | cons step tail =>
      obtain ⟨middle,before,after⟩ := ih tail
      exact ⟨middle,.cons step before,after⟩

section
variable {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K → Graph.Label signature} {i : Nat}

/-- Prove the generated/support and typed path/binder assertions JOINTLY
along the actual finite marked development and its label history. ONE
source selector and ONE physical beta are fixed before induction; no
intermediate correctness assertion is supplied by the caller. Root input
totality is a real source premise and is not general proper-source I.
This theorem does not assert target Matches or SND. -/theorem PathSite.relative_history_typed_with_walks
    (site : PathSite (.beta i) kept (B:=B) (W:=W) (V:=V))
    {root : B} {original : LTerm} (initial : INIT original) (closed : Closed original.erase)
    (matching : Matches site.net root original.erase)
    (inputs : RootInputs site.net root) {boundary : B → Bool} (flow : FlowBalance site.net boundary)
    (positive : boundary root=true) {heights : B → Int} (balance : IndexedLevelBalance site.net heights)
    (rootDepth : heights root=0) (transparency : Transparency site.net root) :
    ∃ beta : BetaEdge site.net,beta.app=.inr (.inl ()) ∧beta.lam=.inr (.inr ()) ∧
      ∃ selection : SourceEdgeSelection original site.net root,
      (∀ {degree appId lamId},SelectedDegree original (site.betaSyntaxFiber root original.erase) degree →
        SourceRoute (sourceEdges [] .external original) (.appFn appId) degree (.lamContext lamId) →
        degree=lamId ∧BetaSourcePorts original root beta appId lamId) ∧
      (∀ {start stamp finish},SelectedSourceRoute (sourceEdges [] .external original)
        (SelectedDegree original (site.betaSyntaxFiber root original.erase)) start stamp finish →
        ∃ walk : PhysicalSourceWalk original root beta start stamp finish,walk.edges=selection.evalLabel beta stamp) ∧
      ∀ {ps marked current},
      Marked.RelativeHistory ps (Marked.mark (site.betaSyntaxFiber root original.erase) original.erase) marked →
      History ps original current →
      GeneratedSyntaxPaths selection beta current ∧SupportedSyntaxBinders selection beta current ∧
      TypedSyntaxPaths selection beta current ∧TypedSyntaxBinders selection beta current := by
  obtain ⟨beta,app,lam,allPorts⟩ := site.selected_beta_source_ports initial matching
  let selection := matching.source_edge_selection closed
  have allWalks : ∀ {start stamp finish},SelectedSourceRoute (sourceEdges [] .external original)
      (SelectedDegree original (site.betaSyntaxFiber root original.erase)) start stamp finish →
      ∃ walk : PhysicalSourceWalk original root beta start stamp finish,walk.edges=selection.evalLabel beta stamp := by
    intro start stamp finish route
    exact selection.selected_route_walk initial matching allPorts route
  have reversed : ∀ reversedPaths : List Path,∀ {marked current},
      Marked.RelativeHistory reversedPaths.reverse (Marked.mark (site.betaSyntaxFiber root original.erase) original.erase) marked →
      History reversedPaths.reverse original current →
      GeneratedSyntaxPaths selection beta current ∧SupportedSyntaxBinders selection beta current ∧
      TypedSyntaxPaths selection beta current ∧TypedSyntaxBinders selection beta current := by
    intro reversedPaths
    induction reversedPaths with
    | nil =>
      intro marked current relative labels
      cases labels
      exact ⟨matching.generated_syntax_paths initial selection beta,
        matching.supported_syntax_binders initial selection beta,
        matching.typed_syntax_paths initial inputs selection beta,
        matching.typed_syntax_binders initial transparency selection beta⟩
    | cons p previous ih =>
      intro marked current relative labels
      have relative' : Marked.RelativeHistory (previous.reverse++[p])
          (Marked.mark (site.betaSyntaxFiber root original.erase) original.erase) marked := by
        simpa only [List.reverse_cons] using relative
      have labels' : History (previous.reverse++[p]) original current := by
        simpa only [List.reverse_cons] using labels
      obtain ⟨markedMiddle,relativeBefore,_relativeLast⟩ := relative_split relative'
      obtain ⟨middle,prior,last⟩ := labels'.split
      have previousInvariants := ih relativeBefore prior
      cases last with
      | cons next tail =>
        cases tail
        obtain ⟨stamp,degree,body,argument,lookup,_contractum⟩ := next.head_lookups
        exact ⟨site.relative_generated_paths_step initial matching selection beta app lam allPorts allWalks
          relativeBefore relative' prior next lookup previousInvariants.1 previousInvariants.2.1,
          site.relative_supported_binders_step initial matching selection beta app lam allPorts allWalks
            relativeBefore relative' prior next lookup previousInvariants.1 previousInvariants.2.1,
          site.relative_typed_paths_step initial matching selection beta app lam inputs flow positive balance rootDepth transparency allPorts allWalks
            relativeBefore relative' prior next lookup previousInvariants.2.2.1 previousInvariants.2.1 previousInvariants.2.2.2,
          site.relative_typed_binders_step initial matching selection beta app lam allPorts allWalks
            relativeBefore relative' prior next lookup previousInvariants.1 previousInvariants.2.1 previousInvariants.2.2.2
            flow positive balance rootDepth⟩
  refine ⟨beta,app,lam,selection,allPorts,allWalks,?_⟩
  intro ps marked current relative labels
  exact reversed ps.reverse (by simpa only [List.reverse_reverse] using relative)
    (by simpa only [List.reverse_reverse] using labels)
/-- Forget the extra source-route witnesses, preserving the original API. -/
theorem PathSite.relative_history_typed
    (site : PathSite (.beta i) kept (B:=B) (W:=W) (V:=V))
    {root : B} {original : LTerm} (initial : INIT original) (closed : Closed original.erase)
    (matching : Matches site.net root original.erase)
    (inputs : RootInputs site.net root) {boundary : B → Bool} (flow : FlowBalance site.net boundary)
    (positive : boundary root=true) {heights : B → Int} (balance : IndexedLevelBalance site.net heights)
    (rootDepth : heights root=0) (transparency : Transparency site.net root) :
    ∃ beta : BetaEdge site.net,beta.app=.inr (.inl ()) ∧beta.lam=.inr (.inr ()) ∧
      ∃ selection : SourceEdgeSelection original site.net root,
      ∀ {ps marked current},
      Marked.RelativeHistory ps (Marked.mark (site.betaSyntaxFiber root original.erase) original.erase) marked →
      History ps original current →
      GeneratedSyntaxPaths selection beta current ∧SupportedSyntaxBinders selection beta current ∧
      TypedSyntaxPaths selection beta current ∧TypedSyntaxBinders selection beta current := by
  obtain ⟨beta,app,lam,selection,_ports,_walks,histories⟩ := site.relative_history_typed_with_walks
    initial closed matching inputs flow positive balance rootDepth transparency
  exact ⟨beta,app,lam,selection,histories⟩
end
end Lamping.AG
