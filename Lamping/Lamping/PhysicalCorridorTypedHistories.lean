import Lamping.Lamping.NetIsoBetaFiberTransport
import Lamping.Lamping.RelativeHistoryTyped
import Lamping.Lamping.GraphFlowPreservation
import Lamping.Lamping.GraphIndexedBalance
namespace Lamping.AG
open Graph Lambda Lambda.Labelled
section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable {g : Net signature N B W} {app lam : N} {i : Nat}
variable {p : Port (g.label app).sort} {q : Port (g.label lam).sort}

/-- Canonical-site history assertions for the ORIGINAL selected pair's
ordered fiber. One actual presentation, beta and selector are fixed before
quantifying over all schedules. All semantic premises concern the original
graph and are transported by its boundary-fixing source isomorphism.
No intermediate invariant or target matching premise is supplied. -/
theorem PhysicalCorridorPresentation.relative_history_typed
    (presentation : PhysicalCorridorPresentation g (.beta i) app lam p q)
    {root : B} {original : LTerm} (initial : INIT original) (closed : Closed original.erase)
    (matching : Matches g root original.erase) (inputs : RootInputs g root)
    {boundary : B → Bool} (flow : FlowBalance g boundary) (positive : boundary root=true)
    {heights : B → Int} (balance : IndexedLevelBalance g heights) (rootDepth : heights root=0)
    (transparency : Transparency g root) :
    ∃ beta : BetaEdge presentation.site.net,
      beta.app=.inr (.inl ()) ∧beta.lam=.inr (.inr ()) ∧
      ∃ selection : SourceEdgeSelection original presentation.site.net root,
      ∀ {ps marked current},
      Marked.RelativeHistory ps (Marked.mark (physicalBetaFiberPaths g root original.erase app lam) original.erase) marked →
      History ps original current →
      GeneratedSyntaxPaths selection beta current ∧SupportedSyntaxBinders selection beta current ∧
      TypedSyntaxPaths selection beta current ∧TypedSyntaxBinders selection beta current := by
  have siteMatching := presentation.sourceIso.matches matching
  have siteInputs := presentation.sourceIso.rootInputs inputs
  let siteFlow := presentation.sourceIso.flowBalance flow
  let siteBalance := presentation.sourceIso.indexed_balance balance
  have siteTransparency := presentation.sourceIso.transparency transparency
  obtain ⟨beta,atApp,atLam,selection,joint⟩ := presentation.site.relative_history_typed
    initial closed siteMatching siteInputs siteFlow positive siteBalance rootDepth siteTransparency
  refine ⟨beta,atApp,atLam,selection,?_⟩
  intro ps marked current relative labels
  have sameSchedule : Marked.RelativeHistory ps
      (Marked.mark (presentation.site.betaSyntaxFiber root original.erase) original.erase) marked := by
    rw [presentation.betaSyntaxFiber_eq]
    exact relative
  exact joint sameSchedule labels
end
end Lamping.AG
