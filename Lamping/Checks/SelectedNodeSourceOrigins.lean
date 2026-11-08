import Lamping.Lamping.SelectedNodeSourceOrigins
import Lamping.Checks.NodeIncomingFirstCreation
namespace Lamping.Checks.SelectedNodeSourceOriginsChecks
open Lambda Lambda.Labelled AG
namespace Copied
open UniformOldCreatedIncomingLabelsChecks.Distinct
open NodeIncomingFirstCreationChecks.Distinct

theorem original_history : History [[],left,right] original target := globalHistory.append labels

-- Nonempty-prefix actual event, with a globally unsafe intermediate term.
-- SAME original source coordinate oldRight forces the selected APP at right;
-- it cannot be the other selected APP with the same internal labels.
theorem actual_selected_app : ∃node,
    source.subterm oldRight=some node ∧
    SyntaxIncidence.Source source oldRight (some sourceParent) ∧
    EndpointChain source (some sourceParent) [right++[.fn]] := by
  obtain ⟨name,chosen,beta,body,argument,redex,node,vertex,lookup,endpoint,position,chain⟩ :=
    marked_node_source_selected old selected rightTrace (current:=leftNode) rfl source_safe marked
  have vertexEq:=SyntaxIncidence.Source.unique endpoint oldSource
  have posEq : vertex.val=right := congrArg Subtype.val (Option.some.inj vertexEq)
  rcases position with app |lam
  · have nameEq:=app.symm.trans posEq
    rw [nameEq] at chain
    exact ⟨node,lookup,vertexEq ▸ endpoint,vertexEq ▸ chain⟩
  · have impossible:=congrArg List.getLast? (posEq.symm.trans lam)
    simp [right] at impossible

theorem wrong_selected_position : left≠right := by decide
#print axioms initial
#print axioms original_history
#print axioms actual_selected_app
#print axioms wrong_selected_position
#print axioms unsafe_middle
#print axioms nonempty_before_actual_split
end Copied
namespace Retained
open NodeLabelSuffixOriginsChecks
abbrev F : List Path := [[]]
abbrev labels : History [[]] retainedSource retainedTarget := .cons retainedStep (.nil _)
def old : Marked.RelativeOldHistory F [[]] (Marked.mark F retainedSource.erase) (.lam (.var 0)) :=
  .cons (.redRoot _ _ _) (by decide) (.nil _)
def trace : BetaNodeHistoryPreimage labels [] [.fn,.body] :=
  .one (step:=retainedStep) (by rfl) retainedOrigin (.nil _ _)
theorem selected (p : Path) (inside : p∈F) : retainedSource.degreeAt p=some (.atom 1) := by
  have same:=List.mem_singleton.mp inside
  subst p;rfl
theorem marked : ¬retainedTarget.label.OuterBarsSafe (fun x=>x≠Label.atom 1) :=
  retainedStep.created_label_not_safe (by rfl) (current:=retainedTarget) rfl (Or.inl rfl)
def sourceParent : SyntaxIncidence.ProperPosition retainedSource :=
  ⟨[.fn],Or.inr ⟨.atom 1,.lam (.atom 2) (.var (.atom 3) 0),rfl⟩⟩
theorem oldSource : SyntaxIncidence.Source retainedSource [.fn,.body] (some sourceParent) :=
  ⟨.body,.lam (.atom 1) (.lam (.atom 2) (.var (.atom 3) 0)),.lamBody (.atom 1),rfl,rfl,.body⟩

theorem actual_selected_function_lambda : ∃node,
    retainedSource.subterm [.fn,.body]=some node ∧
    SyntaxIncidence.Source retainedSource [.fn,.body] (some sourceParent) ∧
    EndpointChain retainedSource (some sourceParent) [[.fn]] := by
  obtain ⟨name,chosen,beta,body,argument,redex,node,vertex,lookup,endpoint,position,chain⟩ :=
    marked_node_source_selected old selected trace (current:=retainedTarget) rfl
      ((init_is_INIT _).outerBarsSafe _) marked
  have empty : name=[] := List.mem_singleton.mp chosen
  subst name
  have vertexEq:=SyntaxIncidence.Source.unique endpoint oldSource
  exact ⟨node,lookup,vertexEq ▸ endpoint,vertexEq ▸ chain⟩
#print axioms old
#print axioms trace
#print axioms actual_selected_function_lambda
end Retained
end Lamping.Checks.SelectedNodeSourceOriginsChecks
