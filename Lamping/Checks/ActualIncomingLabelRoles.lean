import Lamping.Lambda.ActualIncomingLabelRoles
import Lamping.Checks.ActualNodeLabelAncestry
namespace Lamping.Checks.ActualIncomingLabelRolesChecks
open Lambda Lambda.Labelled ActualNodeLabelAncestryChecks

/-- A real copied interior edge has two distinct current coordinates;
its common first atom forces the same incoming role without identifying them. -/
theorem copied_same_role_different_position :
    ([.fn,.body,.fn] : Path).getLast?=([.arg,.body,.fn] : Path).getLast? ∧
    ([.fn,.body,.fn] : Path)≠[.arg,.body,.fn] := by
  refine ⟨?_,copied_equal_labels.2.2⟩
  exact (History.cons firstStep (.nil middle)).incoming_role_eq_of_label initial
    copied_equal_labels.1 copied_equal_labels.2.1 rfl

/-- Final atoms alone do not fix incoming roles: the same argument lambda
is copied to FUNCTION and ARGUMENT positions, with different first atoms. -/
theorem lastAtom_does_not_fix_role :
    ((LTerm.prepend ((Label.atom 3).concat (Label.atom 1).under) argument).label.lastAtom=
      (LTerm.prepend ((Label.atom 4).concat (Label.atom 1).under) argument).label.lastAtom) ∧
    (([.fn] : Path).getLast?≠([.arg] : Path).getLast?) ∧
    ((LTerm.prepend ((Label.atom 3).concat (Label.atom 1).under) argument).label.firstAtom≠
      (LTerm.prepend ((Label.atom 4).concat (Label.atom 1).under) argument).label.firstAtom) := by decide

/-- The mixed-degree/root-overlap history has actual input ports, not an
abstract role certificate inserted as a hypothesis. -/
theorem mixed_overlap_route : ∃ctx finish,
    SourceRoute (sourceEdges [] .external source) ctx innerResult.label finish ∧
    ctx.incomingStep=some .body :=
  history.node_incoming_route initial (p:=[.fn,.body]) rfl

/-- Different actual incoming roles rule out equality of these current
labels, by the general theorem rather than label computation. -/
theorem role_separates_actual_labels :
    innerResult.label≠(.lam (.atom 9) (.var (.atom 10) 0) : LTerm).label := by
  intro equal
  have impossible := history.incoming_role_eq_of_label initial
    (p:=[.fn,.body]) (q:=[.arg,.body,.arg]) rfl rfl equal
  cases impossible

#print axioms copied_same_role_different_position
#print axioms lastAtom_does_not_fix_role
#print axioms mixed_overlap_route
#print axioms role_separates_actual_labels
end Lamping.Checks.ActualIncomingLabelRolesChecks
