import Lamping.Lambda.SafeIncomingHistory
import Lamping.Checks.NodeIncomingFirstCreation
namespace Lamping.Checks.SafeIncomingHistoryChecks
open Lambda Lambda.Labelled
open UniformOldCreatedIncomingLabelsChecks.Distinct
abbrev position : Path := left++[.body]
abbrev oldPosition : Path := oldLeft++[.body]
abbrev leaf : LTerm := .var (.atom 10) 0

def trace : BetaNodeHistoryPreimage labels position oldPosition := by
  apply BetaNodeHistoryPreimage.one (step:=firstStep)
    (show source.subterm left=some (.app (.atom 6) (.lam (.atom 7) (.var (.atom 8) 0)) oldArgument) from rfl)
    (BetaNodePreimage.copied (q:=[]) (relative:=[.body]) (old:=leaf) (by rfl) (by rfl))
  exact BetaNodeHistoryPreimage.one (step:=secondStep) (by rfl)
    (BetaNodePreimage.context (by rintro ⟨rest,impossible⟩;cases impossible)) (.nil _ _)

theorem incoming_safe : leaf.label.OuterBarsSafe (fun x=>x≠Label.atom 7) := by trivial

theorem actual_uncreated : UncreatedNodeHistoryPreimage labels position oldPosition :=
  old.safe_incoming_uncreated (DegreeAligned.initial source F) selected trace
    (current:=leaf) rfl incoming_safe

def currentParent : SyntaxIncidence.ProperPosition target :=
  ⟨left,Or.inr ⟨leftNode.label,leaf,rfl⟩⟩
def originalParent : SyntaxIncidence.ProperPosition source :=
  ⟨oldLeft,Or.inr ⟨.atom 9,leaf,rfl⟩⟩

theorem currentSource : SyntaxIncidence.Source target position (some currentParent) :=
  ⟨.body,leftNode,.lamBody leftNode.label,rfl,rfl,.body⟩
theorem originalSource : SyntaxIncidence.Source source oldPosition (some originalParent) :=
  ⟨.body,oldArgument,.lamBody (.atom 9),rfl,rfl,.body⟩

/-- The safe BODY node has a real source ancestor at another coordinate,
while its current parent is marked and the intermediate whole is unsafe. -/
theorem actual_source_ancestry :
    ∃original,source.subterm oldPosition=some original ∧original.label=leaf.label ∧
      BetaVertexHistoryPreimage labels (some currentParent) (some originalParent) := by
  obtain ⟨original,vertex,lookup,same,endpoint,ancestry⟩ :=
    old.safe_incoming_source_history selected trace (current:=leaf) rfl incoming_safe currentSource
  have vertices:=SyntaxIncidence.Source.unique endpoint originalSource
  exact ⟨original,lookup,same,vertices ▸ ancestry⟩

theorem actual_same_initial_safe_incoming_marked_parent :
    INIT original ∧History [[],left,right] original target ∧
    leaf.label.OuterBarsSafe (fun x=>x≠Label.atom 7) ∧
    ¬leftNode.label.OuterBarsSafe (fun x=>x≠Label.atom 7) ∧
    ¬middle.OuterBarsSafe (fun x=>x≠Label.atom 7) ∧
    currentParent.val≠originalParent.val ∧
    UncreatedNodeHistoryPreimage labels position oldPosition ∧
    ∃original,source.subterm oldPosition=some original ∧original.label=leaf.label ∧
      BetaVertexHistoryPreimage labels (some currentParent) (some originalParent) := by
  exact ⟨initial,globalHistory.append labels,incoming_safe,marked,unsafe_middle,
    by decide,actual_uncreated,actual_source_ancestry⟩
#print axioms trace
#print axioms actual_uncreated
#print axioms actual_source_ancestry
#print axioms actual_same_initial_safe_incoming_marked_parent
end Lamping.Checks.SafeIncomingHistoryChecks
