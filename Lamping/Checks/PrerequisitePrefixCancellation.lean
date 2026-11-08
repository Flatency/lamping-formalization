import Lamping.Lambda.PrerequisitePrefixCancellation
import Lamping.Checks.TerminalHeadSuppliers
import Lamping.Checks.FanSuccessfulChains

namespace Lamping.Checks.PrerequisitePrefixCancellationChecks
open Graph Lambda Lambda.Labelled AG

section Larger
open TerminalHeadSuppliersChecks.Larger
open NormalFalseCanonicalOriginalComparisonChecks.Terminal

/-- Actual closed INIT/root OLD, before1/after0 and distinct starts. Both
returned tails cancel the existing actual prefixes, including the binder jump. -/
theorem actual_larger_terminal_prefix_cancellation :
    INIT original ∧Closed original.erase ∧History [[]] original current ∧
    ([.arg] : Path)≠[.arg,.body] ∧leftCut.before.length=1 ∧rightCut.before.length=1 ∧
    leftCut.after=[] ∧rightCut.after=[] ∧
    PrerequisiteChain current [] [[.fn]] ∧PrerequisiteChain current [] [[.fn]] := by
  have leftTail : PrerequisiteChain current [] [[.fn]] :=
    leftPrefix.cancel_successful_chain (tail:=[[.fn]]) leftChain
  have rightTail : PrerequisiteChain current [] [[.fn]] :=
    rightPrefix.cancel_successful_chain (tail:=[[.fn]]) rightChain
  exact ⟨initial,sourceClosed,actualHistory,by decide,rfl,rfl,rfl,rfl,leftTail,rightTail⟩
end Larger

section ZeroJump
open FanSuccessfulChains

/-- Zero consumed edges do not remove the actual variable-to-binder jump.
The returned chain starts at THIS actual lambda, retaining all literal edges. -/
theorem actual_zero_edge_binder_cancellation :
    INIT original ∧History [[.fn]] original current ∧rightVar≠right ∧
    PrerequisitePrefix current rightVar [] right ∧
    PrerequisiteChain current right rightEdges := by
  have tail : PrerequisiteChain current right rightEdges :=
    right_variable_jump.cancel_successful_chain (tail:=rightEdges) right_variable_chain
  exact ⟨initial,actualHistory,by decide,right_variable_jump,tail⟩
end ZeroJump

#print axioms actual_larger_terminal_prefix_cancellation
#print axioms actual_zero_edge_binder_cancellation
end Lamping.Checks.PrerequisitePrefixCancellationChecks
