import Lamping.Lamping.ActionSyntaxObservationKinds
import Lamping.Checks.UnaryBindingConsumer
set_option maxHeartbeats 4000000

namespace Lamping.Checks.ActionSyntaxObservationKindsChecks.Cro
open AG Graph Lambda Lambda.Labelled FunctionWrappedReachable UnaryBindingReachable.Cro

theorem actual_app_after_lambda :
    ∃ (path : RootAccess croLambda.site.reduce (.inl ()))
      (port : NodePort signature croLambda.Kept croLambda.kept),
      accessWord croLambda.site.reduce path.val=[.fn,.body] ∧
      accessKind croLambda.site.reduce path.val=some .app ∧
      path.val.getLast?=some (croLambda.site.reduce.wire (.inl ⟨.inl port.1,port.2⟩)) := by
  let position : Position current.erase := ⟨[.fn,.body],rfl⟩
  obtain ⟨path,word,u,lookup,observes⟩ := Matches.observation croLambda.site.reduce target_matches position
  have actual : u=.app (.var 0) (.lam (.var 0)) := Option.some.inj (lookup.symm.trans rfl)
  subst u
  obtain ⟨port,finish⟩ := croLambda.site.action_access_kept_of_kind_excluded
    (.cro .lam 0 1 (by decide)) path observes.1 (by
      intro port
      cases port with
      | inl u => cases u;intro impossible;cases impossible
      | inr bit => cases bit <;> intro impossible <;> cases impossible)
  exact ⟨path,port,word,observes.1,finish⟩

theorem actual_lambda_after_app :
    ∃ (path : RootAccess croApp.site.reduce (.inl ()))
      (port : NodePort signature croApp.Kept croApp.kept),
      accessWord croApp.site.reduce path.val=[.arg] ∧
      accessKind croApp.site.reduce path.val=some .lam ∧
      path.val.getLast?=some (croApp.site.reduce.wire (.inl ⟨.inl port.1,port.2⟩)) := by
  let position : Position current.erase := ⟨[.arg],rfl⟩
  obtain ⟨path,word,u,lookup,observes⟩ := Matches.observation croApp.site.reduce actual_final_matches position
  have actual : u=.lam (.var 0) := Option.some.inj (lookup.symm.trans rfl)
  subst u
  obtain ⟨port,finish⟩ := croApp.site.action_access_kept_of_kind_excluded
    (.cro .app 0 1 (by decide)) path observes.1 (by
      intro port
      cases port with
      | inl u => cases u;intro impossible;cases impossible
      | inr bit => cases bit <;> intro impossible <;> cases impossible)
  exact ⟨path,port,word,observes.1,finish⟩

theorem actual_two_and_four_step_traces :
    GraphTrace (ActualNet.initial term) (ActualNet.ofNet croLambda.site.reduce)
      [.beta 0,.croAction .lam 0 1 (by decide)] ∧
    GraphTrace (ActualNet.initial term) (ActualNet.ofNet croApp.site.reduce)
      [.beta 0,.croAction .lam 0 1 (by decide),.croAction .cro 0 1 (by decide),
        .croAction .app 0 1 (by decide)] :=
  ⟨UnaryBindingConsumer.Cro.actual_two_rule_trace,actual_four_step_trace⟩
#print axioms actual_app_after_lambda
#print axioms actual_lambda_after_app
#print axioms actual_two_and_four_step_traces
end Lamping.Checks.ActionSyntaxObservationKindsChecks.Cro

namespace Lamping.Checks.ActionSyntaxObservationKindsChecks.Bra
open AG Graph Lambda Lambda.Labelled BraFunctionReachable UnaryBindingReachable.Bra

theorem actual_app_after_lambda :
    ∃ (path : RootAccess braLambda.site.reduce (.inl ()))
      (port : NodePort signature braLambda.Kept braLambda.kept),
      accessWord braLambda.site.reduce path.val=[.arg,.body] ∧
      accessKind braLambda.site.reduce path.val=some .app ∧
      path.val.getLast?=some (braLambda.site.reduce.wire (.inl ⟨.inl port.1,port.2⟩)) := by
  let position : Position current.erase := ⟨[.arg,.body],rfl⟩
  obtain ⟨path,word,u,lookup,observes⟩ := Matches.observation braLambda.site.reduce target_matches position
  have actual : u=.app (.var 0) (.lam (.var 0)) := Option.some.inj (lookup.symm.trans rfl)
  subst u
  obtain ⟨port,finish⟩ := braLambda.site.action_access_kept_of_kind_excluded
    (.bra .lam 0 1 (by decide)) path observes.1 (by
      intro port
      cases port with
      | inl u => cases u;intro impossible;cases impossible
      | inr bit => cases bit <;> intro impossible <;> cases impossible)
  exact ⟨path,port,word,observes.1,finish⟩

theorem actual_lambda_after_app :
    ∃ (path : RootAccess braApp.site.reduce (.inl ()))
      (port : NodePort signature braApp.Kept braApp.kept),
      accessWord braApp.site.reduce path.val=[.arg] ∧
      accessKind braApp.site.reduce path.val=some .lam ∧
      path.val.getLast?=some (braApp.site.reduce.wire (.inl ⟨.inl port.1,port.2⟩)) := by
  let position : Position current.erase := ⟨[.arg],rfl⟩
  obtain ⟨path,word,u,lookup,observes⟩ := Matches.observation braApp.site.reduce actual_final_matches position
  have actual : u=.lam (.app (.var 0) identity) := Option.some.inj (lookup.symm.trans rfl)
  subst u
  obtain ⟨port,finish⟩ := braApp.site.action_access_kept_of_kind_excluded
    (.bra .app 0 1 (by decide)) path observes.1 (by
      intro port
      cases port with
      | inl u => cases u;intro impossible;cases impossible
      | inr bit => cases bit <;> intro impossible <;> cases impossible)
  exact ⟨path,port,word,observes.1,finish⟩

theorem actual_two_and_four_step_traces :
    GraphTrace (ActualNet.initial term) (ActualNet.ofNet braLambda.site.reduce)
      [.beta 0,.braAction .lam 0 1 (by decide)] ∧
    GraphTrace (ActualNet.initial term) (ActualNet.ofNet braApp.site.reduce)
      [.beta 0,.braAction .lam 0 1 (by decide),.braAction .cro 0 1 (by decide),
        .braAction .app 0 1 (by decide)] :=
  ⟨UnaryBindingConsumer.Bra.actual_two_rule_trace,actual_four_step_trace⟩
#print axioms actual_app_after_lambda
#print axioms actual_lambda_after_app
#print axioms actual_two_and_four_step_traces
end Lamping.Checks.ActionSyntaxObservationKindsChecks.Bra

#print axioms Lamping.AG.accessKind_at_actual_finish
#print axioms Lamping.AG.PathSite.action_access_kept_of_kind_excluded
