import Lamping.Lambda.NonterminalReadingDirections
import Lamping.Checks.FanSuccessfulChains
namespace Lamping.Checks.NonterminalReadingDirectionsChecks
open Lambda Lambda.Labelled

private theorem variable_not_redex (lookup : t.subterm edge=some (.var stamp index)) :
    ¬PrerequisiteRedexEdge t edge := by
  rintro ⟨parent,a,b,body,arg,split,atParent⟩
  have lambdaLookup : t.subterm edge=some (.lam b body) := by
    rw [split,LTerm.subterm_append,atParent];rfl
  cases Option.some.inj (lookup.symm.trans lambdaLookup)

namespace Copied
open FanSuccessfulChains

theorem actual_left_read : PrerequisiteReadsDirected current leftBody leftVar true :=
  ⟨Or.inl ⟨_,_,_,rfl,rfl⟩,rfl⟩
theorem actual_right_read : PrerequisiteReadsDirected current rightBody rightVar true :=
  ⟨Or.inl ⟨_,_,_,rfl,rfl⟩,rfl⟩
theorem left_nonterminal : ¬PrerequisiteRedexEdge current leftVar := variable_not_redex (stamp:=.atom 11) (index:=0) rfl
theorem right_nonterminal : ¬PrerequisiteRedexEdge current rightVar := variable_not_redex (stamp:=.atom 11) (index:=0) rfl

/-- Two different current copied positions have equal labels, so the actual
full-history theorem synchronizes their nonterminal reads. -/
theorem actual_distinct_copies_direction : true=true ∧leftVar≠rightVar := by
  refine ⟨?_,by decide⟩
  exact actualHistory.equal_label_nonredex_read_direction initial
    (edge:=leftVar) (otherEdge:=rightVar)
    (leftNode:=.var (.atom 11) 0) (rightNode:=.var (.atom 11) 0)
    rfl rfl rfl actual_left_read actual_right_read left_nonterminal right_nonterminal

theorem actual_backward_read : PrerequisiteReadsDirected current left left false :=
  ⟨Or.inr ⟨_,_,rfl,rfl⟩,rfl⟩
theorem backward_nonterminal : ¬PrerequisiteRedexEdge current left := by
  rintro ⟨parent,a,b,body,arg,split,_⟩
  have last : (some Step.arg : Option Step)=some .fn := by
    simpa [left] using congrArg List.getLast? split
  cases last

theorem actual_backward_criterion : false=true ↔left.getLast?=some .fn :=
  actual_backward_read.nonredex_forward_iff_function backward_nonterminal

theorem actual_successful_context : INIT original ∧History [[.fn]] original current ∧
    Closed current.erase ∧PrerequisiteChain current leftBody leftBodyEdges ∧
    PrerequisiteChain current rightBody rightBodyEdges ∧PrerequisiteChain current left leftEdges :=
  ⟨initial,actualHistory,targetClosed,left_body_chain,right_body_chain,left_lambda_chain⟩
end Copied

namespace Terminal
open WrappedSuccessfulChains
/-- Omitting the nonredex premise would fail on this actual reachable
singleton: its two endpoint readers traverse the same labelled edge oppositely. -/
theorem actual_terminal_opposite :
    PrerequisiteReadsDirected current [] [.fn] true ∧
    PrerequisiteReadsDirected current [.fn] [.fn] false ∧
    PrerequisiteRedexEdge current [.fn] ∧true≠false :=
  ⟨root_read,last_read,⟨[],_,_,_,_,rfl,rfl⟩,by decide⟩
theorem actual_nonempty_initial_history : INIT original ∧History [[.fn]] original current ∧Closed current.erase :=
  ⟨initial,actualHistory,targetClosed⟩
end Terminal

#print axioms Copied.actual_distinct_copies_direction
#print axioms Copied.actual_backward_criterion
#print axioms Copied.actual_successful_context
#print axioms Terminal.actual_terminal_opposite
#print axioms Terminal.actual_nonempty_initial_history
end Lamping.Checks.NonterminalReadingDirectionsChecks
