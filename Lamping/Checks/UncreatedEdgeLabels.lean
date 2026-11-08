import Lamping.Lambda.UncreatedEdgeLabels
namespace Lamping.Checks.UncreatedEdgeLabels
open Lamping.Lambda Lamping.Lambda.Labelled

private def duplicate : LTerm := .app (.atom 3) (.var (.atom 4) 0) (.var (.atom 5) 0)
private def argument : LTerm := .lam (.atom 7) (.app (.atom 8) (.var (.atom 9) 0) (.var (.atom 10) 0))
private def source : LTerm := .app (.atom 1) (.lam (.atom 2) duplicate) argument
private def target : LTerm := LTerm.contract (.atom 1) (.atom 2) duplicate argument

/-- Actual duplicated strict interiors share one genuine old argument edge. -/
theorem two_actual_copies :
    StepAt [] source target ∧
    target.labelAt [.fn,.body]=some (.atom 8) ∧
    target.labelAt [.arg,.body]=some (.atom 8) ∧
    ¬BetaCreatedIncoming duplicate [] [.fn,.body] ∧
    ¬BetaCreatedIncoming duplicate [] [.arg,.body] := by
  refine ⟨.root _ _ _ _,rfl,rfl,?_,?_⟩ <;>
    decide

theorem duplicate_old_label (side : Step) (which : side=.fn ∨side=.arg) :
    ∃ oldEdge old,source.subterm oldEdge=some old ∧
      old.label=(LTerm.app (.atom 8) (.var (.atom 9) 0) (.var (.atom 10) 0)).label := by
  rcases which with rfl | rfl
  · exact two_actual_copies.1.uncreated_label_origin rfl rfl two_actual_copies.2.2.2.1
  · exact two_actual_copies.1.uncreated_label_origin rfl rfl two_actual_copies.2.2.2.2

/-- The context root keeps its label while its actual child changes. -/
theorem changed_context_label :
    ∃ oldEdge old,(LTerm.lam (.atom 20) source).subterm oldEdge=some old ∧
      old.label=(LTerm.lam (.atom 20) target).label := by
  apply (StepAt.body two_actual_copies.1).uncreated_label_origin (body := duplicate) (argument := argument)
    (beta := .atom 1) (alpha := .atom 2) (edge := []) rfl rfl
  decide

/-- A retained variable under a lambda is not the substituted variable. -/
theorem retained_bound_variable :
    ∃ old,(LTerm.lam (.atom 3) (.app (.atom 4) (.var (.atom 5) 0) (.var (.atom 6) 1))).subterm
      [.body,.fn]=some old ∧old.label=(Label.atom 5) := by
  have lookup : (LTerm.contract (.atom 1) (.atom 2)
      (.lam (.atom 3) (.app (.atom 4) (.var (.atom 5) 0) (.var (.atom 6) 1))) argument).subterm
      [.body,.fn]=some (.var (.atom 5) 0) := rfl
  have origins := LTerm.contract_uncreated_label_origin lookup (by decide)
    (by simp [ArgumentOccurrence,LTerm.erase,subtermAt,binderDepth])
  rcases origins with retained | ⟨site,suffix,old,occurs,split,_,_,_⟩
  · exact retained
  · exact False.elim (retained_variable_not_argument_origin (by rfl) (by decide) occurs split)

/-- Fresh result labels are on actual created positions; the old-label
origin theorem cannot apply to the result itself. -/
theorem actual_result_created : BetaCreatedIncoming duplicate [] [] := by
  apply two_actual_copies.1.created_of_fresh_label rfl (current := target) rfl
  decide

end Lamping.Checks.UncreatedEdgeLabels
#print axioms Lamping.Lambda.Labelled.LTerm.contract_uncreated_label_origin
#print axioms Lamping.Lambda.Labelled.StepAt.uncreated_label_origin
#print axioms Lamping.Lambda.Labelled.StepAt.uncreated_label_mem
#print axioms Lamping.Lambda.Labelled.StepAt.created_of_fresh_label
#print axioms Lamping.Checks.UncreatedEdgeLabels.duplicate_old_label
#print axioms Lamping.Checks.UncreatedEdgeLabels.changed_context_label
