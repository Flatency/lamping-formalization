import Lamping.Lamping.ActualCurrentAfterChains
import Lamping.Checks.ActualUnsafeMarkerLeaves
import Lamping.Checks.ActualChainForwardOrder
namespace Lamping.Checks.ActualCurrentAfterChainsChecks
open Graph Lambda Lambda.Labelled AG
namespace Nonterminal
open ActualUnsafeMarkerLeavesChecks.Nonterminal

private theorem cut_shape (cut : ActualUnsafeMarkerCut F [[.arg]] source current (.atom 4) [.arg] edges) :
    cut.after=[[.fn]] := by
  have split:=cut.split
  have empty : cut.before=[] := by
    cases front : cut.before with
    | nil => rfl
    | cons head tail =>
      rw [front] at split
      have eq : head=[.arg] := (List.cons.inj split).1.symm
      have safe:=cut.safeBefore head (by rw [front];exact List.mem_cons_self)
      rw [eq] at safe
      exact False.elim (marked safe)
  rw [empty,List.nil_append] at split
  exact (List.cons.inj split).2.symm

theorem actual_degree4_after_iso :
    ∃leftNext rightNext,PrerequisiteChain current leftNext [[.fn]] ∧
      PrerequisiteChain current rightNext [[.fn]] ∧
      ChainIncidenceIsomorphic (chainSyntaxIncidence current closedCurrent [[.fn]])
        (chainSyntaxIncidence current closedCurrent [[.fn]]) ∧
      ([[Step.fn]] : List Path).length<edges.length := by
  rcases actual_first_unsafe_current_after initial (.nil source) old labels selected
      (initial.outerBarsSafe _) closedCurrent chain chain (ChainIncidenceIso.refl _) with all | cuts
  · exact False.elim (marked (all.1 [.arg] (by simp [edges])))
  · obtain ⟨left,right,len,front,head,back,ll,rl,cases⟩:=cuts
    have la:=cut_shape left
    have ra:=cut_shape right
    rcases cases with ⟨empty,_⟩ | ⟨nonempty,rightMore,signs,ln,rn,lg,rg,lc,rc,comparison⟩
    · rw [la] at empty;cases empty
    · rw [la] at lc ll
      rw [ra] at rc
      rw [la,ra] at comparison
      exact ⟨ln,rn,lc,rc,comparison,ll⟩
end Nonterminal
namespace Terminal
open DirectedReadingDecompositionChecks
abbrev closedTarget : Closed target.erase := history.closed closed
abbrev old := DirectedMarkerLeafWordsChecks.RootOverlap.old
abbrev selected := DirectedMarkerLeafWordsChecks.RootOverlap.selected

theorem actual_terminal_empty :
    ∃left : ActualUnsafeMarkerCut [[.fn]] [[.fn]] source target (.atom 2) [] [[.fn]],
    ∃right : ActualUnsafeMarkerCut [[.fn]] [[.fn]] source target (.atom 2) [.fn] [[.fn]],
      left.after=[] ∧right.after=[] ∧
      left.after.length<([[Step.fn]] : List Path).length ∧right.after.length<([[Step.fn]] : List Path).length := by
  have marked : ¬degreeReadSafe (.atom 2) (target.labelAt [.fn]) := by
    intro h;have bad:=h _ rfl
    change ((.atom 2 : Label)≠.atom 2) ∧_ at bad
    exact bad.1 rfl
  rcases actual_first_unsafe_current_after initial (.nil source) old history selected
      (initial.outerBarsSafe _) closedTarget successful_function successful_context (ChainIncidenceIso.refl _) with all | cuts
  · exact False.elim (marked (all.1 [.fn] (by simp)))
  · obtain ⟨left,right,len,front,head,back,ll,rl,cases⟩:=cuts
    have le : left.after=[] := List.length_eq_zero_iff.mp (by simp only [List.length_cons,List.length_nil] at ll;omega)
    have re : right.after=[] := List.length_eq_zero_iff.mp (by simp only [List.length_cons,List.length_nil] at rl;omega)
    exact ⟨left,right,le,re,ll,rl⟩

theorem actual_terminal_opposite_signs :
    ∃left : ActualUnsafeMarkerCut [[.fn]] [[.fn]] source target (.atom 2) [] [[.fn]],
    ∃right : ActualUnsafeMarkerCut [[.fn]] [[.fn]] source target (.atom 2) [.fn] [[.fn]],
      left.after=[] ∧right.after=[] ∧left.forward=true ∧right.forward=false := by
  obtain ⟨left,right,le,re,ls,rs,lf,rf⟩:=ActualUnsafeMarkerLeavesChecks.Terminal.actual_terminal_leaves
  exact ⟨left,right,le,re,ls,rs⟩
end Terminal
namespace ActualVariableJump
open ActualChainForwardOrderChecks.Distinct
/-- The FUNCTION read is followed by the actual bound-variable chain;
no zero-edge edge list is treated as a complete successful chain. -/
theorem actual_after_variable : ∃next,ActualAfterStart current leftStart [.fn,.fn,.body,.fn] next ∧
    PrerequisiteChain current next [[.fn,.fn]] :=
  leftChain.after_of_read (Or.inl ⟨_,_,_,rfl,rfl⟩) (by decide)
end ActualVariableJump
#print axioms PrerequisiteChain.after_of_read
#print axioms ActualUnsafeMarkerCut.after_length_lt
#print axioms ActualUnsafeMarkerCut.current_after_chain
#print axioms actual_cut_after_iso
#print axioms actual_first_unsafe_current_after
#print axioms Nonterminal.actual_degree4_after_iso
#print axioms Terminal.actual_terminal_empty
#print axioms Terminal.actual_terminal_opposite_signs
#print axioms ActualVariableJump.actual_after_variable
end Lamping.Checks.ActualCurrentAfterChainsChecks
