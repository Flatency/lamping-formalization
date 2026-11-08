import Lamping.Lamping.MatchingSelectedPrincipalWord
namespace Lamping.Lambda.Labelled
private theorem last_degree_guard
    (prior : History ps original current)
    (guarded : GuardedDegreeHistory allowed (ps++[p]) original target) :
    ∀ degree,current.degreeAt p=some degree → allowed degree := by
  induction prior generalizing target with
  | nil => cases guarded with | cons step guard tail => exact guard
  | cons step history ih =>
    cases guarded with
    | cons first guard tail =>
      have same := step.deterministic first
      cases same
      exact ih tail

/-- The selected original degree of the NEXT actual relative-development
step is derived from its real marked and labelled schedules. The intermediate
term is never reinitialized and no guarded-history certificate is input. -/
theorem relative_last_selected_degree (initial : INIT original)
    (relative : Marked.RelativeHistory (ps++[p]) (Marked.mark old original.erase) marked)
    (prior : History ps original current) (next : StepAt p current target)
    (degreeAt : current.degreeAt p=some degree) : SelectedDegree original old degree := by
  have labels := prior.append (.cons next (.nil _))
  have guarded := (relative_development_origin_guards initial relative labels).1
  exact last_degree_guard prior guarded degree degreeAt
end Lamping.Lambda.Labelled
namespace Lamping.AG
open Graph Lambda Lambda.Labelled
section
variable {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K → Graph.Label signature} {i : Nat}

/-- One original INIT and actual source Matches fix one principal word for
EVERY future actual relative-development event, for any shared atom selector.
This is the literal active-degree invariant, not history generatedness. -/
theorem PathSite.relative_active_principal_word
    (site : PathSite (.beta i) kept (B:=B) (W:=W) (V:=V))
    {root : B} {original : LTerm} (initial : INIT original)
    (matching : Matches site.net root original.erase) :
    ∃ beta : BetaEdge site.net,beta.app=.inr (.inl ()) ∧ beta.lam=.inr (.inr ()) ∧
      ∀ selection : SourceEdgeSelection original site.net root,
      ∀ {ps p marked current target degree},
      Marked.RelativeHistory (ps++[p])
        (Marked.mark (site.betaSyntaxFiber root original.erase) original.erase) marked →
      History ps original current → StepAt p current target → current.degreeAt p=some degree →
      selection.evalLabel beta degree=beta.principal := by
  obtain ⟨beta,app,lam,allDegrees⟩ := site.selected_principal_word initial matching
  refine ⟨beta,app,lam,?_⟩
  intro selection ps p marked current target degree relative prior next degreeAt
  exact allDegrees selection degree (relative_last_selected_degree initial relative prior next degreeAt)
end
end Lamping.AG

