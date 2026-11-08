import Lamping.Lamping.UnaryOccurrenceCases
import Lamping.Lamping.UnaryDoubleCopiedAppComparison
import Lamping.Lamping.UnaryDoubleCopiedLambdaContext
import Lamping.Lamping.UnaryMixedAppParentSeparation
import Lamping.Lamping.UnaryMixedLambdaParentSeparation
import Lamping.Lamping.UnaryMixedAppTerminalSeparation
import Lamping.Lamping.UnaryMixedLambdaTerminalSeparation
import Lamping.Lamping.ActionCopiedFunctionComparison
import Lamping.Lamping.ActionBraCopiedFunctionComparison
import Lamping.Lamping.ActionCopiedArgumentComparison
import Lamping.Lamping.ActionCopiedAppContextComparison
import Lamping.Lamping.KeptParentCopiedLambdaComparison
import Lamping.Lamping.KeptParentCopiedBindingComparison
import Lamping.Lamping.CopiedLambdaBodyKeptComparison
import Lamping.Lamping.ActionCopiedBindingComparison
import Lamping.Lamping.ControlActionJointRepresentation
namespace Lamping.AG
open Graph Lambda Lambda.Labelled
set_option maxHeartbeats 4000000


section
variable {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K → Label signature} {i j : Nat} {lt : i<j}
variable (site : PathSite (Schema.croAction Op.app i j lt) kept (B:=B) (W:=W) (V:=V))
private theorem SourceEdgeFragment.cro_app_same_step_equality
    {directions : B → Bool} (flow : FlowBalance site.net directions)
    (root : B) (positive : directions root=true) {current : LTerm}
    (sourceMatches : Matches site.net root current.erase) (targetMatches : Matches site.reduce root current.erase)
    (principal : SiteActionPrincipal site)
    (sourceLeft : SourceEdgeFragment current site.net root leftEdge p)
    (targetLeft : SourceEdgeFragment current site.reduce root leftEdge p)
    (sourceRight : SourceEdgeFragment current site.net root rightEdge q)
    (targetRight : SourceEdgeFragment current site.reduce root rightEdge q)
    (leftRole : SourceDeparture leftTerm step leftEdge.fromPort)
    (rightRole : SourceDeparture rightTerm step rightEdge.fromPort)
    (oldParentLeft oldParentRight : RootAccess site.net root)
    (newParentLeft newParentRight : RootAccess site.reduce root)
    (oldWordLeft : p=accessWord site.net oldParentLeft.val++[step])
    (oldWordRight : q=accessWord site.net oldParentRight.val++[step])
    (newWordLeft : p=accessWord site.reduce newParentLeft.val++[step])
    (newWordRight : q=accessWord site.reduce newParentRight.val++[step]) :
    targetLeft.segments=targetRight.segments ↔sourceLeft.segments=sourceRight.segments := by
  rcases site.cro_app_access_cases newParentLeft with ⟨leftParent,leftParentAt⟩ | leftParentAt
  ·
    rcases site.cro_app_access_cases newParentRight with ⟨rightParent,rightParentAt⟩ | rightParentAt
    ·
      rcases site.cro_app_access_cases targetLeft.access with ⟨leftEnd,leftEndAt⟩ | leftEndAt
      ·
        rcases site.cro_app_access_cases targetRight.access with ⟨rightEnd,rightEndAt⟩ | rightEndAt
        ·
          exact sourceLeft.unary_kept_piece_equality site (IsAction.cro .app i j lt) (by intro wrong;cases wrong)
            flow root positive sourceMatches targetMatches principal targetLeft sourceRight targetRight leftRole rightRole
            oldParentLeft oldParentRight newParentLeft newParentRight oldWordLeft oldWordRight newWordLeft newWordRight
            leftParent rightParent leftEnd rightEnd leftParentAt rightParentAt leftEndAt rightEndAt
        ·
          have separated := sourceRight.cro_copied_app_terminal_vs_kept_terminal site flow root positive sourceMatches principal
            targetRight sourceLeft targetLeft rightEndAt leftEnd.1 leftEnd.2 leftEndAt
          exact ⟨fun same=>(separated.2.1 same.symm).elim,fun same=>(separated.1 same.symm).elim⟩
      ·
        rcases site.cro_app_access_cases targetRight.access with ⟨rightEnd,rightEndAt⟩ | rightEndAt
        ·
          have separated := sourceLeft.cro_copied_app_terminal_vs_kept_terminal site flow root positive sourceMatches principal
            targetLeft sourceRight targetRight leftEndAt rightEnd.1 rightEnd.2 rightEndAt
          exact separated.2.2
        ·
          exact sourceLeft.cro_kept_parent_copied_app_context_equality site flow root positive sourceMatches targetMatches principal
            targetLeft sourceRight targetRight leftRole rightRole oldParentLeft oldParentRight newParentLeft newParentRight
            oldWordLeft oldWordRight newWordLeft newWordRight
            leftParent rightParent leftParentAt rightParentAt leftEndAt rightEndAt
    ·
      have separated := sourceRight.cro_copied_app_parent_vs_kept_parent site flow root positive sourceMatches targetMatches principal
        targetRight sourceLeft targetLeft rightRole leftRole oldParentRight newParentRight oldParentLeft newParentLeft
        oldWordRight newWordRight oldWordLeft newWordLeft rightParentAt leftParent.1 leftParent.2 leftParentAt
      exact ⟨fun same=>(separated.2.1 same.symm).elim,fun same=>(separated.1 same.symm).elim⟩
  ·
    rcases site.cro_app_access_cases newParentRight with ⟨rightParent,rightParentAt⟩ | rightParentAt
    ·
      have separated := sourceLeft.cro_copied_app_parent_vs_kept_parent site flow root positive sourceMatches targetMatches principal
        targetLeft sourceRight targetRight leftRole rightRole oldParentLeft newParentLeft oldParentRight newParentRight
        oldWordLeft newWordLeft oldWordRight newWordRight leftParentAt rightParent.1 rightParent.2 rightParentAt
      exact separated.2.2
    ·
      rcases targetLeft.step_of_app_parent targetMatches newParentLeft newWordLeft (.inr (.inl ())) appCtx rfl leftParentAt with rfl | rfl
      ·
        rcases site.cro_app_access_cases targetLeft.access with ⟨leftEnd,leftEndAt⟩ | leftEndAt
        ·
          rcases site.cro_app_access_cases targetRight.access with ⟨rightEnd,rightEndAt⟩ | rightEndAt
          ·
            exact sourceLeft.cro_copied_function_kept_equality site flow root positive sourceMatches targetMatches principal
              targetLeft sourceRight targetRight leftRole rightRole oldParentLeft oldParentRight newParentLeft newParentRight
              oldWordLeft oldWordRight newWordLeft newWordRight
              leftParentAt rightParentAt leftEnd.1 rightEnd.1 leftEnd.2 rightEnd.2 leftEndAt rightEndAt
          ·
            have separated := sourceRight.cro_copied_app_terminal_vs_kept_terminal site flow root positive sourceMatches principal
              targetRight sourceLeft targetLeft rightEndAt leftEnd.1 leftEnd.2 leftEndAt
            exact ⟨fun same=>(separated.2.1 same.symm).elim,fun same=>(separated.1 same.symm).elim⟩
        ·
          rcases site.cro_app_access_cases targetRight.access with ⟨rightEnd,rightEndAt⟩ | rightEndAt
          ·
            have separated := sourceLeft.cro_copied_app_terminal_vs_kept_terminal site flow root positive sourceMatches principal
              targetLeft sourceRight targetRight leftEndAt rightEnd.1 rightEnd.2 rightEndAt
            exact separated.2.2
          ·
            exact sourceLeft.cro_double_copied_app_function_equality site flow root positive sourceMatches targetMatches principal
              targetLeft sourceRight targetRight leftRole rightRole oldParentLeft oldParentRight newParentLeft newParentRight
              oldWordLeft oldWordRight newWordLeft newWordRight
              leftParentAt rightParentAt leftEndAt rightEndAt
      ·
        rcases site.cro_app_access_cases targetLeft.access with ⟨leftEnd,leftEndAt⟩ | leftEndAt
        ·
          rcases site.cro_app_access_cases targetRight.access with ⟨rightEnd,rightEndAt⟩ | rightEndAt
          ·
            exact sourceLeft.cro_copied_argument_kept_equality site flow root positive sourceMatches targetMatches principal
              targetLeft sourceRight targetRight leftRole rightRole oldParentLeft oldParentRight newParentLeft newParentRight
              oldWordLeft oldWordRight newWordLeft newWordRight
              leftParentAt rightParentAt leftEnd.1 rightEnd.1 leftEnd.2 rightEnd.2 leftEndAt rightEndAt
          ·
            have separated := sourceRight.cro_copied_app_terminal_vs_kept_terminal site flow root positive sourceMatches principal
              targetRight sourceLeft targetLeft rightEndAt leftEnd.1 leftEnd.2 leftEndAt
            exact ⟨fun same=>(separated.2.1 same.symm).elim,fun same=>(separated.1 same.symm).elim⟩
        ·
          rcases site.cro_app_access_cases targetRight.access with ⟨rightEnd,rightEndAt⟩ | rightEndAt
          ·
            have separated := sourceLeft.cro_copied_app_terminal_vs_kept_terminal site flow root positive sourceMatches principal
              targetLeft sourceRight targetRight leftEndAt rightEnd.1 rightEnd.2 rightEndAt
            exact separated.2.2
          ·
            exact sourceLeft.cro_double_copied_app_argument_equality site flow root positive sourceMatches targetMatches principal
              targetLeft sourceRight targetRight leftRole rightRole oldParentLeft oldParentRight newParentLeft newParentRight
              oldWordLeft oldWordRight newWordLeft newWordRight
              leftParentAt rightParentAt leftEndAt rightEndAt
end

section
variable {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K → Label signature} {i j : Nat} {lt : i<j}
variable (site : PathSite (Schema.croAction Op.lam i j lt) kept (B:=B) (W:=W) (V:=V))
private theorem SourceEdgeFragment.cro_lam_same_step_equality
    {directions : B → Bool} (flow : FlowBalance site.net directions)
    (root : B) (positive : directions root=true) {current : LTerm}
    (sourceMatches : Matches site.net root current.erase) (targetMatches : Matches site.reduce root current.erase)
    (principal : SiteActionPrincipal site)
    (sourceLeft : SourceEdgeFragment current site.net root leftEdge p)
    (targetLeft : SourceEdgeFragment current site.reduce root leftEdge p)
    (sourceRight : SourceEdgeFragment current site.net root rightEdge q)
    (targetRight : SourceEdgeFragment current site.reduce root rightEdge q)
    (leftRole : SourceDeparture leftTerm step leftEdge.fromPort)
    (rightRole : SourceDeparture rightTerm step rightEdge.fromPort)
    (oldParentLeft oldParentRight : RootAccess site.net root)
    (newParentLeft newParentRight : RootAccess site.reduce root)
    (oldWordLeft : p=accessWord site.net oldParentLeft.val++[step])
    (oldWordRight : q=accessWord site.net oldParentRight.val++[step])
    (newWordLeft : p=accessWord site.reduce newParentLeft.val++[step])
    (newWordRight : q=accessWord site.reduce newParentRight.val++[step]) :
    targetLeft.segments=targetRight.segments ↔sourceLeft.segments=sourceRight.segments := by
  rcases site.cro_lam_parent_cases targetMatches targetLeft newParentLeft newWordLeft with ⟨leftParent,leftParentAt⟩ | leftParentAt
  ·
    rcases site.cro_lam_parent_cases targetMatches targetRight newParentRight newWordRight with ⟨rightParent,rightParentAt⟩ | rightParentAt
    ·
      rcases site.cro_lam_access_cases targetLeft.access with ⟨leftEnd,leftEndAt⟩ | leftEndAt | leftEndAt
      ·
        rcases site.cro_lam_access_cases targetRight.access with ⟨rightEnd,rightEndAt⟩ | rightEndAt | rightEndAt
        ·
          exact sourceLeft.unary_kept_piece_equality site (IsAction.cro .lam i j lt) (by intro wrong;cases wrong)
            flow root positive sourceMatches targetMatches principal targetLeft sourceRight targetRight leftRole rightRole
            oldParentLeft oldParentRight newParentLeft newParentRight oldWordLeft oldWordRight newWordLeft newWordRight
            leftParent rightParent leftEnd rightEnd leftParentAt rightParentAt leftEndAt rightEndAt
        ·
          have separated := sourceRight.cro_copied_lambda_context_terminal_vs_kept_terminal site flow root positive sourceMatches principal
            targetRight sourceLeft targetLeft rightEndAt leftEnd.1 leftEnd.2 leftEndAt
          exact ⟨fun same=>(separated.2.1 same.symm).elim,fun same=>(separated.1 same.symm).elim⟩
        ·
          have separated := sourceRight.cro_copied_lambda_binding_terminal_vs_kept_terminal site flow root positive sourceMatches principal
            targetRight sourceLeft targetLeft rightEndAt leftEnd.1 leftEnd.2 leftEndAt
          exact ⟨fun same=>(separated.2.1 same.symm).elim,fun same=>(separated.1 same.symm).elim⟩
      ·
        rcases site.cro_lam_access_cases targetRight.access with ⟨rightEnd,rightEndAt⟩ | rightEndAt | rightEndAt
        ·
          have separated := sourceLeft.cro_copied_lambda_context_terminal_vs_kept_terminal site flow root positive sourceMatches principal
            targetLeft sourceRight targetRight leftEndAt rightEnd.1 rightEnd.2 rightEndAt
          exact separated.2.2
        ·
          exact sourceLeft.cro_kept_parent_copied_lambda_equality site flow root positive sourceMatches targetMatches principal
            targetLeft sourceRight targetRight leftRole rightRole oldParentLeft oldParentRight newParentLeft newParentRight
            oldWordLeft oldWordRight newWordLeft newWordRight
            leftParent rightParent leftParentAt rightParentAt leftEndAt rightEndAt
        ·
          have separated := sourceLeft.cro_copied_lambda_context_vs_binding site flow root positive sourceMatches principal
            targetLeft sourceRight targetRight leftEndAt rightEndAt
          exact separated.2.2
      ·
        rcases site.cro_lam_access_cases targetRight.access with ⟨rightEnd,rightEndAt⟩ | rightEndAt | rightEndAt
        ·
          have separated := sourceLeft.cro_copied_lambda_binding_terminal_vs_kept_terminal site flow root positive sourceMatches principal
            targetLeft sourceRight targetRight leftEndAt rightEnd.1 rightEnd.2 rightEndAt
          exact separated.2.2
        ·
          have separated := sourceRight.cro_copied_lambda_context_vs_binding site flow root positive sourceMatches principal
            targetRight sourceLeft targetLeft rightEndAt leftEndAt
          exact ⟨fun same=>(separated.2.1 same.symm).elim,fun same=>(separated.1 same.symm).elim⟩
        ·
          exact sourceLeft.cro_kept_parent_copied_binding_equality site flow root positive sourceMatches targetMatches principal
            targetLeft sourceRight targetRight leftRole rightRole oldParentLeft oldParentRight newParentLeft newParentRight
            oldWordLeft oldWordRight newWordLeft newWordRight
            leftParent rightParent leftParentAt rightParentAt leftEndAt rightEndAt
    ·
      have separated := sourceRight.cro_copied_lambda_parent_vs_kept_parent site flow root positive sourceMatches targetMatches principal
        targetRight sourceLeft targetLeft rightRole leftRole oldParentRight newParentRight oldParentLeft newParentLeft
        oldWordRight newWordRight oldWordLeft newWordLeft rightParentAt leftParent.1 leftParent.2 leftParentAt
      exact ⟨fun same=>(separated.2.1 same.symm).elim,fun same=>(separated.1 same.symm).elim⟩
  ·
    rcases site.cro_lam_parent_cases targetMatches targetRight newParentRight newWordRight with ⟨rightParent,rightParentAt⟩ | rightParentAt
    ·
      have separated := sourceLeft.cro_copied_lambda_parent_vs_kept_parent site flow root positive sourceMatches targetMatches principal
        targetLeft sourceRight targetRight leftRole rightRole oldParentLeft newParentLeft oldParentRight newParentRight
        oldWordLeft newWordLeft oldWordRight newWordRight leftParentAt rightParent.1 rightParent.2 rightParentAt
      exact separated.2.2
    ·
      have bodyStep := targetLeft.step_of_lambda_parent targetMatches newParentLeft newWordLeft (.inr (.inl ())) (.inl ()) rfl leftParentAt
      subst step
      rcases site.cro_lam_access_cases targetLeft.access with ⟨leftEnd,leftEndAt⟩ | leftEndAt | leftEndAt
      ·
        rcases site.cro_lam_access_cases targetRight.access with ⟨rightEnd,rightEndAt⟩ | rightEndAt | rightEndAt
        ·
          exact sourceLeft.cro_copied_lambda_body_kept_equality site flow root positive sourceMatches targetMatches principal
            targetLeft sourceRight targetRight leftRole rightRole oldParentLeft oldParentRight newParentLeft newParentRight
            oldWordLeft oldWordRight newWordLeft newWordRight
            leftParentAt rightParentAt leftEnd.1 rightEnd.1 leftEnd.2 rightEnd.2 leftEndAt rightEndAt
        ·
          have separated := sourceRight.cro_copied_lambda_context_terminal_vs_kept_terminal site flow root positive sourceMatches principal
            targetRight sourceLeft targetLeft rightEndAt leftEnd.1 leftEnd.2 leftEndAt
          exact ⟨fun same=>(separated.2.1 same.symm).elim,fun same=>(separated.1 same.symm).elim⟩
        ·
          have separated := sourceRight.cro_copied_lambda_binding_terminal_vs_kept_terminal site flow root positive sourceMatches principal
            targetRight sourceLeft targetLeft rightEndAt leftEnd.1 leftEnd.2 leftEndAt
          exact ⟨fun same=>(separated.2.1 same.symm).elim,fun same=>(separated.1 same.symm).elim⟩
      ·
        rcases site.cro_lam_access_cases targetRight.access with ⟨rightEnd,rightEndAt⟩ | rightEndAt | rightEndAt
        ·
          have separated := sourceLeft.cro_copied_lambda_context_terminal_vs_kept_terminal site flow root positive sourceMatches principal
            targetLeft sourceRight targetRight leftEndAt rightEnd.1 rightEnd.2 rightEndAt
          exact separated.2.2
        ·
          exact sourceLeft.cro_double_copied_lambda_context_equality site flow root positive sourceMatches targetMatches principal
            targetLeft sourceRight targetRight leftRole rightRole oldParentLeft oldParentRight newParentLeft newParentRight
            oldWordLeft oldWordRight newWordLeft newWordRight
            leftParentAt rightParentAt leftEndAt rightEndAt
        ·
          have separated := sourceLeft.cro_copied_lambda_context_vs_binding site flow root positive sourceMatches principal
            targetLeft sourceRight targetRight leftEndAt rightEndAt
          exact separated.2.2
      ·
        rcases site.cro_lam_access_cases targetRight.access with ⟨rightEnd,rightEndAt⟩ | rightEndAt | rightEndAt
        ·
          have separated := sourceLeft.cro_copied_lambda_binding_terminal_vs_kept_terminal site flow root positive sourceMatches principal
            targetLeft sourceRight targetRight leftEndAt rightEnd.1 rightEnd.2 rightEndAt
          exact separated.2.2
        ·
          have separated := sourceRight.cro_copied_lambda_context_vs_binding site flow root positive sourceMatches principal
            targetRight sourceLeft targetLeft rightEndAt leftEndAt
          exact ⟨fun same=>(separated.2.1 same.symm).elim,fun same=>(separated.1 same.symm).elim⟩
        ·
          exact sourceLeft.cro_copied_binding_piece_equality site flow root positive sourceMatches targetMatches principal
            targetLeft sourceRight targetRight leftRole rightRole oldParentLeft oldParentRight newParentLeft newParentRight
            oldWordLeft oldWordRight newWordLeft newWordRight
            leftParentAt rightParentAt leftEndAt rightEndAt
end

section
variable {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K → Label signature} {i j : Nat} {lt : i<j}
variable (site : PathSite (Schema.braAction Op.app i j lt) kept (B:=B) (W:=W) (V:=V))
private theorem SourceEdgeFragment.bra_app_same_step_equality
    {directions : B → Bool} (flow : FlowBalance site.net directions)
    (root : B) (positive : directions root=true) {current : LTerm}
    (sourceMatches : Matches site.net root current.erase) (targetMatches : Matches site.reduce root current.erase)
    (principal : SiteActionPrincipal site)
    (sourceLeft : SourceEdgeFragment current site.net root leftEdge p)
    (targetLeft : SourceEdgeFragment current site.reduce root leftEdge p)
    (sourceRight : SourceEdgeFragment current site.net root rightEdge q)
    (targetRight : SourceEdgeFragment current site.reduce root rightEdge q)
    (leftRole : SourceDeparture leftTerm step leftEdge.fromPort)
    (rightRole : SourceDeparture rightTerm step rightEdge.fromPort)
    (oldParentLeft oldParentRight : RootAccess site.net root)
    (newParentLeft newParentRight : RootAccess site.reduce root)
    (oldWordLeft : p=accessWord site.net oldParentLeft.val++[step])
    (oldWordRight : q=accessWord site.net oldParentRight.val++[step])
    (newWordLeft : p=accessWord site.reduce newParentLeft.val++[step])
    (newWordRight : q=accessWord site.reduce newParentRight.val++[step]) :
    targetLeft.segments=targetRight.segments ↔sourceLeft.segments=sourceRight.segments := by
  rcases site.bra_app_access_cases newParentLeft with ⟨leftParent,leftParentAt⟩ | leftParentAt
  ·
    rcases site.bra_app_access_cases newParentRight with ⟨rightParent,rightParentAt⟩ | rightParentAt
    ·
      rcases site.bra_app_access_cases targetLeft.access with ⟨leftEnd,leftEndAt⟩ | leftEndAt
      ·
        rcases site.bra_app_access_cases targetRight.access with ⟨rightEnd,rightEndAt⟩ | rightEndAt
        ·
          exact sourceLeft.unary_kept_piece_equality site (IsAction.bra .app i j lt) (by intro wrong;cases wrong)
            flow root positive sourceMatches targetMatches principal targetLeft sourceRight targetRight leftRole rightRole
            oldParentLeft oldParentRight newParentLeft newParentRight oldWordLeft oldWordRight newWordLeft newWordRight
            leftParent rightParent leftEnd rightEnd leftParentAt rightParentAt leftEndAt rightEndAt
        ·
          have separated := sourceRight.bra_copied_app_terminal_vs_kept_terminal site flow root positive sourceMatches principal
            targetRight sourceLeft targetLeft rightEndAt leftEnd.1 leftEnd.2 leftEndAt
          exact ⟨fun same=>(separated.2.1 same.symm).elim,fun same=>(separated.1 same.symm).elim⟩
      ·
        rcases site.bra_app_access_cases targetRight.access with ⟨rightEnd,rightEndAt⟩ | rightEndAt
        ·
          have separated := sourceLeft.bra_copied_app_terminal_vs_kept_terminal site flow root positive sourceMatches principal
            targetLeft sourceRight targetRight leftEndAt rightEnd.1 rightEnd.2 rightEndAt
          exact separated.2.2
        ·
          exact sourceLeft.bra_kept_parent_copied_app_context_equality site flow root positive sourceMatches targetMatches principal
            targetLeft sourceRight targetRight leftRole rightRole oldParentLeft oldParentRight newParentLeft newParentRight
            oldWordLeft oldWordRight newWordLeft newWordRight
            leftParent rightParent leftParentAt rightParentAt leftEndAt rightEndAt
    ·
      have separated := sourceRight.bra_copied_app_parent_vs_kept_parent site flow root positive sourceMatches targetMatches principal
        targetRight sourceLeft targetLeft rightRole leftRole oldParentRight newParentRight oldParentLeft newParentLeft
        oldWordRight newWordRight oldWordLeft newWordLeft rightParentAt leftParent.1 leftParent.2 leftParentAt
      exact ⟨fun same=>(separated.2.1 same.symm).elim,fun same=>(separated.1 same.symm).elim⟩
  ·
    rcases site.bra_app_access_cases newParentRight with ⟨rightParent,rightParentAt⟩ | rightParentAt
    ·
      have separated := sourceLeft.bra_copied_app_parent_vs_kept_parent site flow root positive sourceMatches targetMatches principal
        targetLeft sourceRight targetRight leftRole rightRole oldParentLeft newParentLeft oldParentRight newParentRight
        oldWordLeft newWordLeft oldWordRight newWordRight leftParentAt rightParent.1 rightParent.2 rightParentAt
      exact separated.2.2
    ·
      rcases targetLeft.step_of_app_parent targetMatches newParentLeft newWordLeft (.inr (.inl ())) appCtx rfl leftParentAt with rfl | rfl
      ·
        rcases site.bra_app_access_cases targetLeft.access with ⟨leftEnd,leftEndAt⟩ | leftEndAt
        ·
          rcases site.bra_app_access_cases targetRight.access with ⟨rightEnd,rightEndAt⟩ | rightEndAt
          ·
            exact sourceLeft.bra_copied_function_kept_equality site flow root positive sourceMatches targetMatches principal
              targetLeft sourceRight targetRight leftRole rightRole oldParentLeft oldParentRight newParentLeft newParentRight
              oldWordLeft oldWordRight newWordLeft newWordRight
              leftParentAt rightParentAt leftEnd.1 rightEnd.1 leftEnd.2 rightEnd.2 leftEndAt rightEndAt
          ·
            have separated := sourceRight.bra_copied_app_terminal_vs_kept_terminal site flow root positive sourceMatches principal
              targetRight sourceLeft targetLeft rightEndAt leftEnd.1 leftEnd.2 leftEndAt
            exact ⟨fun same=>(separated.2.1 same.symm).elim,fun same=>(separated.1 same.symm).elim⟩
        ·
          rcases site.bra_app_access_cases targetRight.access with ⟨rightEnd,rightEndAt⟩ | rightEndAt
          ·
            have separated := sourceLeft.bra_copied_app_terminal_vs_kept_terminal site flow root positive sourceMatches principal
              targetLeft sourceRight targetRight leftEndAt rightEnd.1 rightEnd.2 rightEndAt
            exact separated.2.2
          ·
            exact sourceLeft.bra_double_copied_app_function_equality site flow root positive sourceMatches targetMatches principal
              targetLeft sourceRight targetRight leftRole rightRole oldParentLeft oldParentRight newParentLeft newParentRight
              oldWordLeft oldWordRight newWordLeft newWordRight
              leftParentAt rightParentAt leftEndAt rightEndAt
      ·
        rcases site.bra_app_access_cases targetLeft.access with ⟨leftEnd,leftEndAt⟩ | leftEndAt
        ·
          rcases site.bra_app_access_cases targetRight.access with ⟨rightEnd,rightEndAt⟩ | rightEndAt
          ·
            exact sourceLeft.bra_copied_argument_kept_equality site flow root positive sourceMatches targetMatches principal
              targetLeft sourceRight targetRight leftRole rightRole oldParentLeft oldParentRight newParentLeft newParentRight
              oldWordLeft oldWordRight newWordLeft newWordRight
              leftParentAt rightParentAt leftEnd.1 rightEnd.1 leftEnd.2 rightEnd.2 leftEndAt rightEndAt
          ·
            have separated := sourceRight.bra_copied_app_terminal_vs_kept_terminal site flow root positive sourceMatches principal
              targetRight sourceLeft targetLeft rightEndAt leftEnd.1 leftEnd.2 leftEndAt
            exact ⟨fun same=>(separated.2.1 same.symm).elim,fun same=>(separated.1 same.symm).elim⟩
        ·
          rcases site.bra_app_access_cases targetRight.access with ⟨rightEnd,rightEndAt⟩ | rightEndAt
          ·
            have separated := sourceLeft.bra_copied_app_terminal_vs_kept_terminal site flow root positive sourceMatches principal
              targetLeft sourceRight targetRight leftEndAt rightEnd.1 rightEnd.2 rightEndAt
            exact separated.2.2
          ·
            exact sourceLeft.bra_double_copied_app_argument_equality site flow root positive sourceMatches targetMatches principal
              targetLeft sourceRight targetRight leftRole rightRole oldParentLeft oldParentRight newParentLeft newParentRight
              oldWordLeft oldWordRight newWordLeft newWordRight
              leftParentAt rightParentAt leftEndAt rightEndAt
end

section
variable {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K → Label signature} {i j : Nat} {lt : i<j}
variable (site : PathSite (Schema.braAction Op.lam i j lt) kept (B:=B) (W:=W) (V:=V))
private theorem SourceEdgeFragment.bra_lam_same_step_equality
    {directions : B → Bool} (flow : FlowBalance site.net directions)
    (root : B) (positive : directions root=true) {current : LTerm}
    (sourceMatches : Matches site.net root current.erase) (targetMatches : Matches site.reduce root current.erase)
    (principal : SiteActionPrincipal site)
    (sourceLeft : SourceEdgeFragment current site.net root leftEdge p)
    (targetLeft : SourceEdgeFragment current site.reduce root leftEdge p)
    (sourceRight : SourceEdgeFragment current site.net root rightEdge q)
    (targetRight : SourceEdgeFragment current site.reduce root rightEdge q)
    (leftRole : SourceDeparture leftTerm step leftEdge.fromPort)
    (rightRole : SourceDeparture rightTerm step rightEdge.fromPort)
    (oldParentLeft oldParentRight : RootAccess site.net root)
    (newParentLeft newParentRight : RootAccess site.reduce root)
    (oldWordLeft : p=accessWord site.net oldParentLeft.val++[step])
    (oldWordRight : q=accessWord site.net oldParentRight.val++[step])
    (newWordLeft : p=accessWord site.reduce newParentLeft.val++[step])
    (newWordRight : q=accessWord site.reduce newParentRight.val++[step]) :
    targetLeft.segments=targetRight.segments ↔sourceLeft.segments=sourceRight.segments := by
  rcases site.bra_lam_parent_cases targetMatches targetLeft newParentLeft newWordLeft with ⟨leftParent,leftParentAt⟩ | leftParentAt
  ·
    rcases site.bra_lam_parent_cases targetMatches targetRight newParentRight newWordRight with ⟨rightParent,rightParentAt⟩ | rightParentAt
    ·
      rcases site.bra_lam_access_cases targetLeft.access with ⟨leftEnd,leftEndAt⟩ | leftEndAt | leftEndAt
      ·
        rcases site.bra_lam_access_cases targetRight.access with ⟨rightEnd,rightEndAt⟩ | rightEndAt | rightEndAt
        ·
          exact sourceLeft.unary_kept_piece_equality site (IsAction.bra .lam i j lt) (by intro wrong;cases wrong)
            flow root positive sourceMatches targetMatches principal targetLeft sourceRight targetRight leftRole rightRole
            oldParentLeft oldParentRight newParentLeft newParentRight oldWordLeft oldWordRight newWordLeft newWordRight
            leftParent rightParent leftEnd rightEnd leftParentAt rightParentAt leftEndAt rightEndAt
        ·
          have separated := sourceRight.bra_copied_lambda_context_terminal_vs_kept_terminal site flow root positive sourceMatches principal
            targetRight sourceLeft targetLeft rightEndAt leftEnd.1 leftEnd.2 leftEndAt
          exact ⟨fun same=>(separated.2.1 same.symm).elim,fun same=>(separated.1 same.symm).elim⟩
        ·
          have separated := sourceRight.bra_copied_lambda_binding_terminal_vs_kept_terminal site flow root positive sourceMatches principal
            targetRight sourceLeft targetLeft rightEndAt leftEnd.1 leftEnd.2 leftEndAt
          exact ⟨fun same=>(separated.2.1 same.symm).elim,fun same=>(separated.1 same.symm).elim⟩
      ·
        rcases site.bra_lam_access_cases targetRight.access with ⟨rightEnd,rightEndAt⟩ | rightEndAt | rightEndAt
        ·
          have separated := sourceLeft.bra_copied_lambda_context_terminal_vs_kept_terminal site flow root positive sourceMatches principal
            targetLeft sourceRight targetRight leftEndAt rightEnd.1 rightEnd.2 rightEndAt
          exact separated.2.2
        ·
          exact sourceLeft.bra_kept_parent_copied_lambda_equality site flow root positive sourceMatches targetMatches principal
            targetLeft sourceRight targetRight leftRole rightRole oldParentLeft oldParentRight newParentLeft newParentRight
            oldWordLeft oldWordRight newWordLeft newWordRight
            leftParent rightParent leftParentAt rightParentAt leftEndAt rightEndAt
        ·
          have separated := sourceLeft.bra_copied_lambda_context_vs_binding site flow root positive sourceMatches principal
            targetLeft sourceRight targetRight leftEndAt rightEndAt
          exact separated.2.2
      ·
        rcases site.bra_lam_access_cases targetRight.access with ⟨rightEnd,rightEndAt⟩ | rightEndAt | rightEndAt
        ·
          have separated := sourceLeft.bra_copied_lambda_binding_terminal_vs_kept_terminal site flow root positive sourceMatches principal
            targetLeft sourceRight targetRight leftEndAt rightEnd.1 rightEnd.2 rightEndAt
          exact separated.2.2
        ·
          have separated := sourceRight.bra_copied_lambda_context_vs_binding site flow root positive sourceMatches principal
            targetRight sourceLeft targetLeft rightEndAt leftEndAt
          exact ⟨fun same=>(separated.2.1 same.symm).elim,fun same=>(separated.1 same.symm).elim⟩
        ·
          exact sourceLeft.bra_kept_parent_copied_binding_equality site flow root positive sourceMatches targetMatches principal
            targetLeft sourceRight targetRight leftRole rightRole oldParentLeft oldParentRight newParentLeft newParentRight
            oldWordLeft oldWordRight newWordLeft newWordRight
            leftParent rightParent leftParentAt rightParentAt leftEndAt rightEndAt
    ·
      have separated := sourceRight.bra_copied_lambda_parent_vs_kept_parent site flow root positive sourceMatches targetMatches principal
        targetRight sourceLeft targetLeft rightRole leftRole oldParentRight newParentRight oldParentLeft newParentLeft
        oldWordRight newWordRight oldWordLeft newWordLeft rightParentAt leftParent.1 leftParent.2 leftParentAt
      exact ⟨fun same=>(separated.2.1 same.symm).elim,fun same=>(separated.1 same.symm).elim⟩
  ·
    rcases site.bra_lam_parent_cases targetMatches targetRight newParentRight newWordRight with ⟨rightParent,rightParentAt⟩ | rightParentAt
    ·
      have separated := sourceLeft.bra_copied_lambda_parent_vs_kept_parent site flow root positive sourceMatches targetMatches principal
        targetLeft sourceRight targetRight leftRole rightRole oldParentLeft newParentLeft oldParentRight newParentRight
        oldWordLeft newWordLeft oldWordRight newWordRight leftParentAt rightParent.1 rightParent.2 rightParentAt
      exact separated.2.2
    ·
      have bodyStep := targetLeft.step_of_lambda_parent targetMatches newParentLeft newWordLeft (.inr (.inl ())) (.inl ()) rfl leftParentAt
      subst step
      rcases site.bra_lam_access_cases targetLeft.access with ⟨leftEnd,leftEndAt⟩ | leftEndAt | leftEndAt
      ·
        rcases site.bra_lam_access_cases targetRight.access with ⟨rightEnd,rightEndAt⟩ | rightEndAt | rightEndAt
        ·
          exact sourceLeft.bra_copied_lambda_body_kept_equality site flow root positive sourceMatches targetMatches principal
            targetLeft sourceRight targetRight leftRole rightRole oldParentLeft oldParentRight newParentLeft newParentRight
            oldWordLeft oldWordRight newWordLeft newWordRight
            leftParentAt rightParentAt leftEnd.1 rightEnd.1 leftEnd.2 rightEnd.2 leftEndAt rightEndAt
        ·
          have separated := sourceRight.bra_copied_lambda_context_terminal_vs_kept_terminal site flow root positive sourceMatches principal
            targetRight sourceLeft targetLeft rightEndAt leftEnd.1 leftEnd.2 leftEndAt
          exact ⟨fun same=>(separated.2.1 same.symm).elim,fun same=>(separated.1 same.symm).elim⟩
        ·
          have separated := sourceRight.bra_copied_lambda_binding_terminal_vs_kept_terminal site flow root positive sourceMatches principal
            targetRight sourceLeft targetLeft rightEndAt leftEnd.1 leftEnd.2 leftEndAt
          exact ⟨fun same=>(separated.2.1 same.symm).elim,fun same=>(separated.1 same.symm).elim⟩
      ·
        rcases site.bra_lam_access_cases targetRight.access with ⟨rightEnd,rightEndAt⟩ | rightEndAt | rightEndAt
        ·
          have separated := sourceLeft.bra_copied_lambda_context_terminal_vs_kept_terminal site flow root positive sourceMatches principal
            targetLeft sourceRight targetRight leftEndAt rightEnd.1 rightEnd.2 rightEndAt
          exact separated.2.2
        ·
          exact sourceLeft.bra_double_copied_lambda_context_equality site flow root positive sourceMatches targetMatches principal
            targetLeft sourceRight targetRight leftRole rightRole oldParentLeft oldParentRight newParentLeft newParentRight
            oldWordLeft oldWordRight newWordLeft newWordRight
            leftParentAt rightParentAt leftEndAt rightEndAt
        ·
          have separated := sourceLeft.bra_copied_lambda_context_vs_binding site flow root positive sourceMatches principal
            targetLeft sourceRight targetRight leftEndAt rightEndAt
          exact separated.2.2
      ·
        rcases site.bra_lam_access_cases targetRight.access with ⟨rightEnd,rightEndAt⟩ | rightEndAt | rightEndAt
        ·
          have separated := sourceLeft.bra_copied_lambda_binding_terminal_vs_kept_terminal site flow root positive sourceMatches principal
            targetLeft sourceRight targetRight leftEndAt rightEnd.1 rightEnd.2 rightEndAt
          exact separated.2.2
        ·
          have separated := sourceRight.bra_copied_lambda_context_vs_binding site flow root positive sourceMatches principal
            targetRight sourceLeft targetLeft rightEndAt leftEndAt
          exact ⟨fun same=>(separated.2.1 same.symm).elim,fun same=>(separated.1 same.symm).elim⟩
        ·
          exact sourceLeft.bra_copied_binding_piece_equality site flow root positive sourceMatches targetMatches principal
            targetLeft sourceRight targetRight leftRole rightRole oldParentLeft oldParentRight newParentLeft newParentRight
            oldWordLeft oldWordRight newWordLeft newWordRight
            leftParentAt rightParentAt leftEndAt rightEndAt
end
section
variable {s : Schema} {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K → Label signature}
/-- Actual nonroot occurrences determine all child roles, parents and finite
kept/copied cases internally; no caller classification is a premise. -/
theorem PathSite.unary_nonroot_occurrence_equality
    (site : PathSite s kept (B:=B) (W:=W) (V:=V))
    (action : IsAction s) (unary : s.active≠.fan)
    {directions : B → Bool} (flow : FlowBalance site.net directions)
    (root : B) (positive : directions root=true) {current : LTerm}
    (sourceMatches : Matches site.net root current.erase) (targetMatches : Matches site.reduce root current.erase)
    (principal : SiteActionPrincipal site) {p q : Path}
    (leftNonroot : p≠[]) (rightNonroot : q≠[])
    (sourceFirst : OccurrenceFragment current site.net root p)
    (targetFirst : OccurrenceFragment current site.reduce root p)
    (sourceSecond : OccurrenceFragment current site.net root q)
    (targetSecond : OccurrenceFragment current site.reduce root q) :
    targetFirst.fragment.segments=targetSecond.fragment.segments ↔
      sourceFirst.fragment.segments=sourceSecond.fragment.segments := by
  by_cases control : s.passive=.fan ∨s.passive=.cro ∨s.passive=.bra
  · exact site.control_action_nonroot_occurrence_equality action control flow root positive
      sourceMatches targetMatches principal leftNonroot rightNonroot sourceFirst targetFirst sourceSecond targetSecond
  rcases sourceFirst with ⟨leftSub,leftEnv,leftCtx,leftOccurrence,sourceFirst⟩
  rcases targetFirst with ⟨_otherSub,_otherEnv,_otherCtx,otherLeftOccurrence,targetFirst⟩
  obtain ⟨rfl,rfl,rfl⟩ := leftOccurrence.same_occurrence otherLeftOccurrence
  rcases sourceSecond with ⟨rightSub,rightEnv,rightCtx,rightOccurrence,sourceSecond⟩
  rcases targetSecond with ⟨_otherSub,_otherEnv,_otherCtx,otherRightOccurrence,targetSecond⟩
  obtain ⟨rfl,rfl,rfl⟩ := rightOccurrence.same_occurrence otherRightOccurrence
  rcases leftOccurrence.last_departure with ⟨empty,_⟩ |⟨leftParentPath,leftStep,leftTerm,leftSplit,leftLookup,leftRole⟩
  · exact (leftNonroot empty).elim
  rcases rightOccurrence.last_departure with ⟨empty,_⟩ |⟨rightParentPath,rightStep,rightTerm,rightSplit,rightLookup,rightRole⟩
  · exact (rightNonroot empty).elim
  let leftPosition : Position current.erase := ⟨leftParentPath,by rw [←LTerm.erase_subterm,leftLookup];rfl⟩
  let rightPosition : Position current.erase := ⟨rightParentPath,by rw [←LTerm.erase_subterm,rightLookup];rfl⟩
  obtain ⟨sourceLeft,sourceLeftWord,_⟩ := Matches.observation site.net sourceMatches leftPosition
  obtain ⟨targetLeft,targetLeftWord,_⟩ := Matches.observation site.reduce targetMatches leftPosition
  obtain ⟨sourceRight,sourceRightWord,_⟩ := Matches.observation site.net sourceMatches rightPosition
  obtain ⟨targetRight,targetRightWord,_⟩ := Matches.observation site.reduce targetMatches rightPosition
  have actualLeftRole : SourceDeparture leftTerm leftStep (sourceEdge leftEnv leftCtx leftSub).fromPort := by
    have sourceFrom : (sourceEdge leftEnv leftCtx leftSub).fromPort=leftCtx := by cases leftSub <;> rfl
    rw [sourceFrom];exact leftRole
  have actualRightRole : SourceDeparture rightTerm rightStep (sourceEdge rightEnv rightCtx rightSub).fromPort := by
    have sourceFrom : (sourceEdge rightEnv rightCtx rightSub).fromPort=rightCtx := by cases rightSub <;> rfl
    rw [sourceFrom];exact rightRole
  have oldWordLeft : p=accessWord site.net sourceLeft.val++[leftStep] := by rw [sourceLeftWord];exact leftSplit
  have oldWordRight : q=accessWord site.net sourceRight.val++[rightStep] := by rw [sourceRightWord];exact rightSplit
  have newWordLeft : p=accessWord site.reduce targetLeft.val++[leftStep] := by rw [targetLeftWord];exact leftSplit
  have newWordRight : q=accessWord site.reduce targetRight.val++[rightStep] := by rw [targetRightWord];exact rightSplit
  by_cases sameStep : leftStep=rightStep
  · subst rightStep
    cases action with
    | fan op i j lt => exact (unary rfl).elim
    | cro op i j lt =>
      cases op with
      | app =>
        exact sourceFirst.cro_app_same_step_equality site flow root positive sourceMatches targetMatches principal
          targetFirst sourceSecond targetSecond actualLeftRole actualRightRole sourceLeft sourceRight targetLeft targetRight
          oldWordLeft oldWordRight newWordLeft newWordRight
      | lam =>
        exact sourceFirst.cro_lam_same_step_equality site flow root positive sourceMatches targetMatches principal
          targetFirst sourceSecond targetSecond actualLeftRole actualRightRole sourceLeft sourceRight targetLeft targetRight
          oldWordLeft oldWordRight newWordLeft newWordRight
      | fan => exact (control (Or.inl rfl)).elim
      | cro => exact (control (Or.inr (Or.inl rfl))).elim
      | bra => exact (control (Or.inr (Or.inr rfl))).elim
    | bra op i j lt =>
      cases op with
      | app =>
        exact sourceFirst.bra_app_same_step_equality site flow root positive sourceMatches targetMatches principal
          targetFirst sourceSecond targetSecond actualLeftRole actualRightRole sourceLeft sourceRight targetLeft targetRight
          oldWordLeft oldWordRight newWordLeft newWordRight
      | lam =>
        exact sourceFirst.bra_lam_same_step_equality site flow root positive sourceMatches targetMatches principal
          targetFirst sourceSecond targetSecond actualLeftRole actualRightRole sourceLeft sourceRight targetLeft targetRight
          oldWordLeft oldWordRight newWordLeft newWordRight
      | fan => exact (control (Or.inl rfl)).elim
      | cro => exact (control (Or.inr (Or.inl rfl))).elim
      | bra => exact (control (Or.inr (Or.inr rfl))).elim
  · have oldDifferent := sourceFirst.ne_of_child_steps sourceMatches sourceSecond actualLeftRole actualRightRole
      sourceLeft sourceRight oldWordLeft oldWordRight sameStep
    have newDifferent := targetFirst.ne_of_child_steps targetMatches targetSecond actualLeftRole actualRightRole
      targetLeft targetRight newWordLeft newWordRight sameStep
    exact ⟨fun same=>(newDifferent same).elim,fun same=>(oldDifferent same).elim⟩

/-- The root boundary cases require only actual-position uniqueness/separation;
the complete unary proper-child classifier is internal to the nonroot branch. -/
theorem PathSite.unary_occurrence_equality
    (site : PathSite s kept (B:=B) (W:=W) (V:=V))
    (action : IsAction s) (unary : s.active≠.fan)
    {directions : B → Bool} (flow : FlowBalance site.net directions)
    (root : B) (positive : directions root=true) {current : LTerm}
    (sourceMatches : Matches site.net root current.erase) (targetMatches : Matches site.reduce root current.erase)
    (principal : SiteActionPrincipal site) {p q : Path}
    (sourceFirst : OccurrenceFragment current site.net root p)
    (targetFirst : OccurrenceFragment current site.reduce root p)
    (sourceSecond : OccurrenceFragment current site.net root q)
    (targetSecond : OccurrenceFragment current site.reduce root q) :
    targetFirst.fragment.segments=targetSecond.fragment.segments ↔
      sourceFirst.fragment.segments=sourceSecond.fragment.segments := by
  by_cases firstRoot : p=[]
  · subst p
    by_cases secondRoot : q=[]
    · subst q
      exact ⟨fun _=>sourceFirst.segments_unique sourceMatches sourceSecond,
        fun _=>targetFirst.segments_unique targetMatches targetSecond⟩
    · have oldDifferent := sourceFirst.ne_of_root_nonroot sourceSecond secondRoot
      have newDifferent := targetFirst.ne_of_root_nonroot targetSecond secondRoot
      exact ⟨fun same=>(newDifferent same).elim,fun same=>(oldDifferent same).elim⟩
  · by_cases secondRoot : q=[]
    · subst q
      have oldDifferent := sourceSecond.ne_of_root_nonroot sourceFirst firstRoot
      have newDifferent := targetSecond.ne_of_root_nonroot targetFirst firstRoot
      exact ⟨fun same=>(newDifferent same.symm).elim,fun same=>(oldDifferent same.symm).elim⟩
    · exact site.unary_nonroot_occurrence_equality action unary flow root positive sourceMatches targetMatches principal
        firstRoot secondRoot sourceFirst targetFirst sourceSecond targetSecond
end
#print axioms PathSite.unary_nonroot_occurrence_equality
#print axioms PathSite.unary_occurrence_equality
end Lamping.AG
