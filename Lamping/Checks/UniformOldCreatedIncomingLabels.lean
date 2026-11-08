import Lamping.Lambda.UniformOldCreatedIncomingLabels
import Lamping.Checks.UniformOldNodeLabelSuffix
namespace Lamping.Checks.UniformOldCreatedIncomingLabelsChecks
open Lambda Lambda.Labelled
namespace Nested
open UniformOldNodeLabelSuffixChecks
-- Reuses the single actual INIT/global history and unsafe-middle two-OLD
-- fixture. The old node has a complete compound, rather than atomic, label.
theorem actual_compound_pair : ∃left right,
    source.subterm [.arg,.arg]=some left ∧source.subterm [.arg,.arg]=some right ∧left.label=right.label :=
  old.equal_marked_node_origin_labels (DegreeAligned.initial source F) labels selected
    nodeTrace nodeTrace rfl rfl source_safe target_marked rfl
end Nested
namespace Distinct
abbrev I : Term := WrappedSuccessfulChains.I
abbrev bare : Term := .app (.lam (.app (.var 0) (.var 0))) (.lam (.app I I))
abbrev original : LTerm := initLabels bare
abbrev source : LTerm := WrappedSuccessfulChains.contractRoot original
abbrev middle : LTerm := match source with
  | .app stamp (.lam head body) arg => .app stamp (.lam head (WrappedSuccessfulChains.contractRoot body)) arg
  | t=>t
abbrev target : LTerm := match middle with
  | .app stamp fn (.lam head body) => .app stamp fn (.lam head (WrappedSuccessfulChains.contractRoot body))
  | t=>t
abbrev left : Path := [.fn,.body]
abbrev right : Path := [.arg,.body]
abbrev oldLeft : Path := [.fn,.body,.arg]
abbrev oldRight : Path := [.arg,.body,.arg]
abbrev F : List Path := [left,right]
abbrev oldArgument : LTerm := .lam (.atom 9) (.var (.atom 10) 0)
abbrev leftNode : LTerm := LTerm.contract (.atom 6) (.atom 7) (.var (.atom 8) 0) oldArgument

theorem initial : INIT original := init_is_INIT _
def globalHistory : History [[]] original source := .cons (.root _ _ _ _) (.nil _)
def firstStep : StepAt left source middle := .fn (.body (.root _ _ _ _))
def secondStep : StepAt right middle target := .arg (.body (.root _ _ _ _))
def labels : History [left,right] source target := .cons firstStep (.cons secondStep (.nil _))
def old : Marked.RelativeOldHistory F [left,right] (Marked.mark F source.erase)
    (.app [[]] (.lam (.lam (.var 0))) (.lam (.lam (.var 0)))) :=
  .cons (.appL (.lam (.redRoot _ _ _))) (by decide)
    (.cons (.appR (.lam (.redRoot _ _ _))) (by decide) (.nil _))
theorem selected (p : Path) (inside : p∈F) : source.degreeAt p=some (.atom 7) := by
  rcases List.mem_cons.mp inside with rfl | inside
  · rfl
  · have same:=List.mem_singleton.mp inside;subst p;rfl

def leftTrace : BetaNodeHistoryPreimage labels left oldLeft := by
  apply BetaNodeHistoryPreimage.one (step:=firstStep)
    (show source.subterm left=some (.app (.atom 6) (.lam (.atom 7) (.var (.atom 8) 0)) oldArgument) from rfl)
    (BetaNodePreimage.copied (q:=[]) (relative:=[]) (old:=oldArgument) (by rfl) (by rfl))
  exact BetaNodeHistoryPreimage.one (step:=secondStep) (by rfl)
    (BetaNodePreimage.context (by rintro ⟨rest,impossible⟩;cases impossible)) (.nil _ _)
def rightTrace : BetaNodeHistoryPreimage labels right oldRight := by
  apply BetaNodeHistoryPreimage.one (step:=firstStep) (by rfl)
    (BetaNodePreimage.context (by rintro ⟨rest,impossible⟩;cases impossible))
  exact BetaNodeHistoryPreimage.one (step:=secondStep)
    (show middle.subterm right=some (.app (.atom 6) (.lam (.atom 7) (.var (.atom 8) 0)) oldArgument) from rfl)
    (BetaNodePreimage.copied (q:=[]) (relative:=[]) (old:=oldArgument) (by rfl) (by rfl)) (.nil _ _)

theorem source_safe : source.OuterBarsSafe (fun x=>x≠Label.atom 7) := by
  dsimp [source,original,bare,I,WrappedSuccessfulChains.I,WrappedSuccessfulChains.contractRoot,
    initLabels,initFrom,nodeCount,LTerm.contract,LTerm.subst,LTerm.single,LTerm.prepend,
    LTerm.rename,LTerm.lift,LTerm.label,Label.concat,Label.over,Label.under,Label.atom]
  simp only [LTerm.OuterBarsSafe,Label.OuterBarsSafe]
  decide

theorem marked : ¬leftNode.label.OuterBarsSafe (fun x=>x≠Label.atom 7) :=
  firstStep.created_label_not_safe (by rfl) (current:=leftNode) (by rfl) (Or.inl rfl)

theorem unsafe_middle : ¬middle.OuterBarsSafe (fun x=>x≠Label.atom 7) := by
  intro safe
  have atMiddle : middle.subterm left=some leftNode := rfl
  exact marked ((LTerm.outerBarsSafe_iff _ _).mp safe leftNode.label (LTerm.label_mem_of_subterm atMiddle))

theorem actual_different_position_pair : ∃a b,
    source.subterm oldLeft=some a ∧source.subterm oldRight=some b ∧a.label=b.label :=
  old.equal_marked_node_origin_labels (DegreeAligned.initial source F) labels selected
    leftTrace rightTrace (current:=leftNode) (otherCurrent:=leftNode)
    rfl rfl source_safe marked rfl

theorem coordinates_remain_distinct : oldLeft≠oldRight ∧left≠right := by decide
#print axioms initial
#print axioms globalHistory
#print axioms old
#print axioms leftTrace
#print axioms rightTrace
#print axioms unsafe_middle
#print axioms actual_different_position_pair
#print axioms coordinates_remain_distinct
end Distinct
#print axioms Nested.actual_compound_pair
end Lamping.Checks.UniformOldCreatedIncomingLabelsChecks
