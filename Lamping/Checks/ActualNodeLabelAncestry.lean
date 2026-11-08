import Lamping.Lambda.ActualNodeLabelAncestry
namespace Lamping.Checks.ActualNodeLabelAncestryChecks
open Lambda Lambda.Labelled
abbrev I : Term := .lam (.var 0)
abbrev source : LTerm := initLabels (.app (.lam (.app (.var 0) (.var 0))) (.lam (.app I I)))
abbrev body : LTerm := .app (.atom 2) (.var (.atom 3) 0) (.var (.atom 4) 0)
abbrev argument : LTerm := .lam (.atom 5) (.app (.atom 6) (.lam (.atom 7) (.var (.atom 8) 0)) (.lam (.atom 9) (.var (.atom 10) 0)))
abbrev middle : LTerm := LTerm.contract (.atom 0) (.atom 1) body argument
abbrev leftHead : Label := (Label.atom 3).concat (Label.atom 1).under |>.concat (.atom 5)
abbrev rightHead : Label := (Label.atom 4).concat (Label.atom 1).under |>.concat (.atom 5)
abbrev outerHead : Label := ((Label.atom 0).concat (Label.atom 1).over).concat (.atom 2)
abbrev innerResult : LTerm := LTerm.contract (.atom 6) (.atom 7) (.var (.atom 8) 0) (.lam (.atom 9) (.var (.atom 10) 0))
abbrev target : LTerm := .app outerHead (.lam leftHead innerResult) (.lam rightHead (.app (.atom 6) (.lam (.atom 7) (.var (.atom 8) 0)) (.lam (.atom 9) (.var (.atom 10) 0))))
def firstStep : StepAt [] source middle := .root _ _ _ _
def secondStep : StepAt [.fn,.body] middle target := .fn (.body (.root _ _ _ _))
def history : History [[],[.fn,.body]] source target := .cons firstStep (.cons secondStep (.nil _))
theorem initial : INIT source := init_is_INIT _
theorem closed : Closed source.erase := by change (0<1 ∧0<1) ∧(0<2 ∧0<2);decide

-- The two steps really have different selected degrees.
theorem actual_mixed_degrees : source.degreeAt []=some (.atom 1) ∧middle.degreeAt [.fn,.body]=some (.atom 7) := ⟨rfl,rfl⟩

-- Duplicated interior syntax has equal labels at genuinely different CURRENT coordinates.
theorem copied_equal_labels :
    middle.subterm [.fn,.body,.fn]=some (.lam (.atom 7) (.var (.atom 8) 0)) ∧
    middle.subterm [.arg,.body,.fn]=some (.lam (.atom 7) (.var (.atom 8) 0)) ∧
    ([.fn,.body,.fn] : Path)≠[.arg,.body,.fn] := ⟨rfl,rfl,by decide⟩

theorem copied_constructor_consumes_general :
    (.lam (.atom 7) (.var (.atom 8) 0) : LTerm).constructorTag=
    (.lam (.atom 7) (.var (.atom 8) 0) : LTerm).constructorTag :=
  (History.cons firstStep (.nil middle)).node_constructor_eq_of_label initial
    (p:=[.fn,.body,.fn]) (q:=[.arg,.body,.fn]) rfl rfl rfl

-- Different current labels still have the same original argument ancestor;
-- the created overlap carries both separators and is not a uniform OLD trace.
theorem mixed_lastAtom_ancestor : ∃oldPosition old,
    source.subterm oldPosition=some old ∧
    BetaNodeHistoryPreimage history [.fn,.body] oldPosition ∧
    BetaNodeHistoryPreimage history [.arg,.body,.arg] oldPosition ∧
    old.constructorTag=innerResult.constructorTag ∧
    old.constructorTag=(.lam (.atom 9) (.var (.atom 10) 0) : LTerm).constructorTag :=
  history.initial_node_origin_eq_of_lastAtom initial rfl rfl rfl

theorem mixed_labels_distinct : innerResult.label≠(.lam (.atom 9) (.var (.atom 10) 0) : LTerm).label := by decide

theorem one_initial_real_history : INIT source ∧History [[],[.fn,.body]] source target ∧Closed target.erase :=
  ⟨initial,history,history.closed closed⟩
#print axioms actual_mixed_degrees
#print axioms copied_equal_labels
#print axioms copied_constructor_consumes_general
#print axioms mixed_lastAtom_ancestor
#print axioms mixed_labels_distinct
#print axioms one_initial_real_history
end Lamping.Checks.ActualNodeLabelAncestryChecks
