import Lamping.Lamping.ActionSyntaxEndpointCases
import Lamping.Checks.UnaryBindingConsumer

namespace Lamping.Checks.ActionSyntaxEndpointCasesChecks.Cro
open AG Graph Lambda Lambda.Labelled FunctionWrappedReachable UnaryBindingReachable.Cro

theorem actual_copied_endpoint :
    ∃ (node : (Schema.croAction .lam 0 1 (by decide)).right.N)
      (port : Port ((Schema.croAction .lam 0 1 (by decide)).right.net.label node).sort),
      ActionPassiveNode (.croAction .lam 0 1 (by decide)) node ∧
      lambdaParent.val.getLast?=some (croLambda.site.reduce.wire (.inl ⟨.inr node,port⟩)) := by
  rcases croLambda.site.action_access_node_cases (.cro .lam 0 1 (by decide)) lambdaParent with
    ⟨port,finish⟩ | copied
  · have actual := lambdaFinish
    change lambdaEdges.getLast?=_ at finish
    have same := Option.some.inj (actual.symm.trans finish)
    have endpoints := congrArg croLambda.site.reduce.wire same
    simp only [Pairing.involutive] at endpoints
    have nodeEq := congrArg Sigma.fst (Sum.inl.inj endpoints)
    cases nodeEq
  · exact copied

theorem actual_two_step_context :
    GraphTrace (ActualNet.initial term) (ActualNet.ofNet croLambda.site.reduce)
      [.beta 0,.croAction .lam 0 1 (by decide)] ∧
    Nonempty (RootAccess croLambda.site.reduce (.inl ())) :=
  ⟨UnaryBindingConsumer.Cro.actual_two_rule_trace,⟨lambdaParent⟩⟩
#print axioms actual_copied_endpoint
#print axioms actual_two_step_context
end Lamping.Checks.ActionSyntaxEndpointCasesChecks.Cro

namespace Lamping.Checks.ActionSyntaxEndpointCasesChecks.Bra
open AG Graph Lambda Lambda.Labelled BraFunctionReachable UnaryBindingReachable.Bra

theorem actual_copied_endpoint :
    ∃ (node : (Schema.braAction .lam 0 1 (by decide)).right.N)
      (port : Port ((Schema.braAction .lam 0 1 (by decide)).right.net.label node).sort),
      ActionPassiveNode (.braAction .lam 0 1 (by decide)) node ∧
      lambdaParent.val.getLast?=some (braLambda.site.reduce.wire (.inl ⟨.inr node,port⟩)) := by
  rcases braLambda.site.action_access_node_cases (.bra .lam 0 1 (by decide)) lambdaParent with
    ⟨port,finish⟩ | copied
  · have actual := lambdaFinish
    change lambdaEdges.getLast?=_ at finish
    have same := Option.some.inj (actual.symm.trans finish)
    have endpoints := congrArg braLambda.site.reduce.wire same
    simp only [Pairing.involutive] at endpoints
    have nodeEq := congrArg Sigma.fst (Sum.inl.inj endpoints)
    cases nodeEq
  · exact copied

theorem actual_two_step_context :
    GraphTrace (ActualNet.initial term) (ActualNet.ofNet braLambda.site.reduce)
      [.beta 0,.braAction .lam 0 1 (by decide)] ∧
    Nonempty (RootAccess braLambda.site.reduce (.inl ())) :=
  ⟨UnaryBindingConsumer.Bra.actual_two_rule_trace,⟨lambdaParent⟩⟩
#print axioms actual_copied_endpoint
#print axioms actual_two_step_context
end Lamping.Checks.ActionSyntaxEndpointCasesChecks.Bra

#print axioms Lamping.AG.ActionPassiveNode.sort
#print axioms Lamping.AG.PathSite.action_access_node_cases
