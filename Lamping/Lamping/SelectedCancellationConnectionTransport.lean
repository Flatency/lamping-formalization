import Lamping.Lamping.CancellationFragmentTransport
import Lamping.Lamping.CancellationCanonicalComparison
import Lamping.Lamping.RootCancellationMatching
import Lamping.Lamping.RedexOccurrenceFragments

namespace Lamping.AG
open Graph Lambda Lambda.Labelled
section
variable {s : Schema} {K B W V : Type} [FiniteNames K] [FiniteNames B]
variable [FiniteNames W] [FiniteNames V] {kept : K → Graph.Label signature}
variable (site : PathSite s kept (B:=B) (W:=W) (V:=V))

/-- One actual cancellation transports the WHOLE connection of each specified
redex. Target Matches is derived, and every actual target witness has the same
literal connection; mere existence of an unrelated target access is not used
as a progress certificate. -/
theorem PathSite.cancellation_selected_connection
    (cancel : IsCancellation s) {directions : B → Bool}
    (flow : FlowBalance site.net directions) (root : B) (positive : directions root = true)
    (inputs : RootInputs site.net root) {depths : B → Int}
    (balance : IndexedLevelBalance site.net depths) (rootDepth : depths root = 0)
    (oldT : Transparency site.net root) {current : LTerm}
    (closed : Closed current.erase) (matching : Matches site.net root current.erase) :
    ∃ principal : SiteActionPrincipal site,
      Matches site.reduce root current.erase ∧
      ∀ (redex : RedexOcc current.erase)
        (appStamp lamStamp : Lambda.Labelled.Label) (body arg : LTerm)
        (_lookup : current.subterm redex.val = some (.app appStamp (.lam lamStamp body) arg))
        (source : ActualRedexAccess site.net root redex),
        ∃ target : ActualRedexAccess site.reduce root redex,
          CanonicalCancellationResidual site (site.cancellation_canonical_fronts principal.edges)
            target.connection.edges source.connection.edges ∧
          ∀ other : ActualRedexAccess site.reduce root redex,
            other.connection.edges = target.connection.edges := by
  have targetMatches := site.cancellation_matches_rootInputs cancel flow root positive inputs
    balance rootDepth oldT matching
  obtain ⟨principal,transport⟩ := site.cancellation_occurrence_fragments cancel flow root positive
    matching targetMatches
  refine ⟨principal,targetMatches,?_⟩
  intro redex appStamp lamStamp body arg lookup source
  have childLookup : current.subterm (redex.val++[.fn]) = some (.lam lamStamp body) := by
    rw [LTerm.subterm_append,lookup]
    rfl
  obtain ⟨oldFragment⟩ := matching.occurrence_fragment_at closed childLookup
  obtain ⟨newFragment⟩ := targetMatches.occurrence_fragment_at closed childLookup
  obtain ⟨target⟩ := targetMatches.actual_redex_access redex
  have oldEq := source.occurrence_fragment_segments matching lookup oldFragment
  have newEq := target.occurrence_fragment_segments targetMatches lookup newFragment
  have residual := transport oldFragment newFragment
  rw [oldEq,newEq] at residual
  refine ⟨target,residual,?_⟩
  intro other
  have otherEq := other.occurrence_fragment_segments targetMatches lookup newFragment
  exact otherEq.symm.trans newEq

/-- Literal sharing of two represented redex connections is preserved AND
reflected by the same actual cancellation and the same principal producer. -/
theorem PathSite.cancellation_selected_connections_eq_iff
    (cancel : IsCancellation s) {directions : B → Bool}
    (flow : FlowBalance site.net directions) (root : B) (positive : directions root = true)
    (inputs : RootInputs site.net root) {depths : B → Int}
    (balance : IndexedLevelBalance site.net depths) (rootDepth : depths root = 0)
    (oldT : Transparency site.net root) {current : LTerm}
    (closed : Closed current.erase) (matching : Matches site.net root current.erase)
    (first second : RedexOcc current.erase)
    (firstApp firstLam secondApp secondLam : Lambda.Labelled.Label)
    (firstBody firstArg secondBody secondArg : LTerm)
    (firstLookup : current.subterm first.val = some (.app firstApp (.lam firstLam firstBody) firstArg))
    (secondLookup : current.subterm second.val = some (.app secondApp (.lam secondLam secondBody) secondArg))
    (firstSource : ActualRedexAccess site.net root first)
    (secondSource : ActualRedexAccess site.net root second) :
    ∃ (firstTarget : ActualRedexAccess site.reduce root first)
      (secondTarget : ActualRedexAccess site.reduce root second),
      firstTarget.connection.edges = secondTarget.connection.edges ↔
        firstSource.connection.edges = secondSource.connection.edges := by
  obtain ⟨principal,_targetMatches,transport⟩ := site.cancellation_selected_connection cancel flow root
    positive inputs balance rootDepth oldT closed matching
  obtain ⟨firstTarget,firstResidual,_firstUnique⟩ :=
    transport first firstApp firstLam firstBody firstArg firstLookup firstSource
  obtain ⟨secondTarget,secondResidual,_secondUnique⟩ :=
    transport second secondApp secondLam secondBody secondArg secondLookup secondSource
  exact ⟨firstTarget,secondTarget,
    CanonicalCancellationResidual.equality_iff site cancel principal firstResidual secondResidual⟩
end
end Lamping.AG
