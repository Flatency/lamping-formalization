import Lamping.Lamping.AdministrativeOriginalWordAccess
import Lamping.Checks.FunctionWrappedReachable

namespace Lamping.Checks.AdministrativeOriginalWordAccess
open AG Graph Lambda Lambda.Labelled FunctionWrappedReachable

/-- Actual original closed encoding, beta then administrative lambda action,
with genuine non-root accesses selected by independent source/target Matches.
Every wire assignment satisfying reversal is consumed; none is set to zero. -/
theorem actual_closed_admin_original_word_access :
    INIT original ∧Closed original.erase ∧
    GraphTrace (ActualNet.initial term) (ActualNet.ofNet croLambda.site.reduce)
      [.beta 0,.croAction .lam 0 1 (by decide)] ∧
    ∃ (principal : SiteActionPrincipal croLambda.site)
      (source : RootAccess croLambda.site.net (.inl ()))
      (target : RootAccess croLambda.site.reduce (.inl ())),
      accessWord croLambda.site.net source.val=[.fn] ∧
      accessWord croLambda.site.reduce target.val=[.fn] ∧
      ∀ weights : Endpoint croLambda.site.net → EdgeWord,
        OriginalWordReversal weights →
        physicalOriginalWord
          (croLambda.site.actionOriginalWordWeights (.cro .lam 0 1 (by decide)) principal weights) target.val =
          physicalOriginalWord weights source.val := by
  obtain ⟨flow,_balance,_inputs,_transparency,matching⟩ := beta_certified
  have sourceMatches := croLambda.sourceIso.matches matching
  obtain ⟨_newFlow,_newBalance,_newInputs,_newT,targetMatches⟩ := lambda_certified
  let position : Position current.erase := ⟨[.fn],by decide⟩
  obtain ⟨source,sourceWord,_sourceShape⟩ := Matches.observation _ sourceMatches position
  obtain ⟨target,targetWord,_targetShape⟩ := Matches.observation _ targetMatches position
  obtain ⟨principal⟩ := croLambda.site.actionPrincipal_exists
  refine ⟨WrappedSuccessfulChains.initial,WrappedSuccessfulChains.sourceClosed,
    actual_two_step_trace,principal,source,target,sourceWord,targetWord,?_⟩
  intro weights reverseLaw
  obtain ⟨a,b,whole⟩ := target.property.1.1
  exact croLambda.site.action_original_word_root_access (.cro .lam 0 1 (by decide))
    (croLambda.sourceIso.flowBalance flow) (.inl ()) rfl sourceMatches principal source target
    (sourceWord.trans targetWord.symm) whole weights reverseLaw

#print axioms actual_closed_admin_original_word_access
end Lamping.Checks.AdministrativeOriginalWordAccess
