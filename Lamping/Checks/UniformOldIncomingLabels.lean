import Lamping.Lambda.UniformOldIncomingLabels
import Lamping.Checks.SafeIncomingHistory
namespace Lamping.Checks.UniformOldIncomingLabelsChecks
open Lambda Lambda.Labelled
open UniformOldCreatedIncomingLabelsChecks.Distinct

abbrev rightPosition : Path := right++[.body]
abbrev rightOldPosition : Path := oldRight++[.body]
abbrev leaf : LTerm := SafeIncomingHistoryChecks.leaf

def rightLeafTrace : BetaNodeHistoryPreimage labels rightPosition rightOldPosition := by
  apply BetaNodeHistoryPreimage.one (step:=firstStep) (by rfl)
    (BetaNodePreimage.context (by rintro ⟨rest,impossible⟩;cases impossible))
  exact BetaNodeHistoryPreimage.one (step:=secondStep)
    (show middle.subterm right=some (.app (.atom 6) (.lam (.atom 7) (.var (.atom 8) 0)) oldArgument) from rfl)
    (BetaNodePreimage.copied (q:=[]) (relative:=[.body]) (old:=leaf) (by rfl) (by rfl)) (.nil _ _)

theorem actual_safe_pair : ∃a b,
    source.subterm SafeIncomingHistoryChecks.oldPosition=some a ∧
    source.subterm rightOldPosition=some b ∧a.label=b.label :=
  old.equal_node_origin_labels (DegreeAligned.initial source F) labels selected
    SafeIncomingHistoryChecks.trace rightLeafTrace (current:=leaf) (otherCurrent:=leaf)
    rfl rfl source_safe rfl

theorem actual_marked_pair : ∃a b,
    source.subterm oldLeft=some a ∧source.subterm oldRight=some b ∧a.label=b.label :=
  old.equal_node_origin_labels (DegreeAligned.initial source F) labels selected
    leftTrace rightTrace (current:=leftNode) (otherCurrent:=leftNode)
    rfl rfl source_safe rfl

theorem actual_same_init_both_branches : INIT original ∧
    History [[],left,right] original target ∧
    leaf.label.OuterBarsSafe (fun x=>x≠Label.atom 7) ∧
    ¬leftNode.label.OuterBarsSafe (fun x=>x≠Label.atom 7) ∧
    ¬middle.OuterBarsSafe (fun x=>x≠Label.atom 7) :=
  ⟨initial,globalHistory.append labels,SafeIncomingHistoryChecks.incoming_safe,marked,unsafe_middle⟩

theorem safe_coordinates_distinct :
    SafeIncomingHistoryChecks.position≠rightPosition ∧
    SafeIncomingHistoryChecks.oldPosition≠rightOldPosition := by decide

theorem marked_coordinates_distinct : left≠right ∧oldLeft≠oldRight := by decide

#print axioms Marked.RelativeOldHistory.equal_node_origin_labels
#print axioms rightLeafTrace
#print axioms actual_safe_pair
#print axioms actual_marked_pair
#print axioms actual_same_init_both_branches
#print axioms safe_coordinates_distinct
#print axioms marked_coordinates_distinct
end Lamping.Checks.UniformOldIncomingLabelsChecks
