import Lamping.Lamping.ContextualSourceEvaluation
import Lamping.Lamping.CurrentRedexPorts
namespace Lamping.Checks.ContextualEvaluation
open Lambda Lambda.Labelled
private def bodyTerm : LTerm := .lam (.atom 5) (.var (.atom 6) 1)
private def argumentTerm : LTerm := .lam (.atom 7) (.var (.atom 8) 0)
private def sourceTerm : LTerm := .lam (.atom 1) (.app (.atom 2) (.var (.atom 9) 0)
  (.app (.atom 3) (.lam (.atom 4) bodyTerm) argumentTerm))
private def targetTerm : LTerm := .lam (.atom 1) (.app (.atom 2) (.var (.atom 9) 0)
  (LTerm.contract (.atom 3) (.atom 4) bodyTerm argumentTerm))
private theorem actualStep : StepAt [.body,.arg] sourceTerm targetTerm :=
  .body (.arg (.root (.atom 3) (.atom 4) bodyTerm argumentTerm))

/-- The copied variable is under a retained binder, and the terminal is
inside the copied lambda argument. Both contextual stem labels survive. -/
theorem contextual_captured_copy :
    targetTerm.sourceTrail (fun n : Nat => [n]) [101] [202] [.body,.arg,.body,.body]=
      some [1,2,3,101,5,6,202,7,8] := by
  have equation := actualStep.sourceTrail_copy (fun n : Nat => [n]) [101] [202]
    (beta:=.atom 3) (alpha:=.atom 4) (body:=bodyTerm) (argument:=argumentTerm)
    rfl (q:=[.body]) rfl [.body]
  exact equation

theorem contextual_retained_lambda :
    targetTerm.sourceTrail (fun n : Nat => [n]) [101] [202] [.body,.arg]=some [1,2,3,101,5] := by
  have nonvariable : ∀ stamp k,bodyTerm≠.var stamp k := by intro stamp k equal; cases equal
  have equation := actualStep.sourceTrail_nonvariable (fun n : Nat => [n]) [101] [202]
    (beta:=.atom 3) (alpha:=.atom 4) (body:=bodyTerm) (argument:=argumentTerm)
    rfl (q:=[]) rfl nonvariable
  exact equation

theorem actual_stem_preserved :
    targetTerm.sourceStem (fun n : Nat => [n]) [101] [202] [.body,.arg]=some [1,2] := by
  exact (actualStep.sourceStem_eq (fun n : Nat => [n]) [101] [202]).symm

/-- Here the active atom really evaluates to the fixed principal word.
The generic splice consumes the previous whole bound-variable access. -/
theorem contextual_previous_body_splice :
    targetTerm.sourceTrail (fun n : Nat => [n]) [4] [202] [.body,.arg,.body,.body]=
      (sourceTerm.sourceTrail (fun n : Nat => [n]) [4] [202]
        [.body,.arg,.fn,.body,.body]).map (fun before => before++[202,7,8]) := by
  have equation := actualStep.sourceTrail_copy_splice (fun n : Nat => [n]) [4] [202]
    (beta:=.atom 3) (alpha:=.atom 4) (body:=bodyTerm) (argument:=argumentTerm)
    rfl rfl (q:=[.body]) rfl [.body]
  exact equation

theorem contextual_retained_lambda_ambient :
    targetTerm.sourceTrail (fun n : Nat => [n]) [4] [202] [.body,.arg]=
      sourceTerm.sourceTrail (fun n : Nat => [n]) [4] [202] [.body,.arg,.fn,.body] := by
  have nonvariable : ∀ stamp k,bodyTerm≠.var stamp k := by intro stamp k equal; cases equal
  exact actualStep.sourceTrail_retained_nonvariable (fun n : Nat => [n]) [4] [202]
    rfl rfl (q:=[]) rfl nonvariable

private def keptBody : LTerm := .lam (.atom 5) (.var (.atom 6) 0)
private def keptSource : LTerm := .lam (.atom 1) (.app (.atom 2) (.var (.atom 9) 0)
  (.app (.atom 3) (.lam (.atom 4) keptBody) argumentTerm))
private def keptTarget : LTerm := .lam (.atom 1) (.app (.atom 2) (.var (.atom 9) 0)
  (LTerm.contract (.atom 3) (.atom 4) keptBody argumentTerm))
private theorem keptStep : StepAt [.body,.arg] keptSource keptTarget :=
  .body (.arg (.root (.atom 3) (.atom 4) keptBody argumentTerm))

theorem contextual_protected_variable_ambient :
    keptTarget.sourceTrail (fun n : Nat => [n]) [4] [202] [.body,.arg,.body]=
      keptSource.sourceTrail (fun n : Nat => [n]) [4] [202] [.body,.arg,.fn,.body,.body] := by
  exact keptStep.sourceTrail_retained_variable (fun n : Nat => [n]) [4] [202]
    rfl rfl (q:=[.body]) (k:=0) rfl (by decide)

theorem actual_strict_ancestor_word :
    targetTerm.sourceTrail (fun n : Nat => [n]) [101] [202] [.body]=some [1,2] := by
  have outside : ¬∃ suffix,[Step.body]=[Step.body,Step.arg]++suffix := by
    rintro ⟨suffix,equal⟩
    have lengths := congrArg List.length equal
    simp only [List.length_cons,List.length_nil,List.length_append] at lengths
    omega
  exact actualStep.sourceTrail_outside (fun n : Nat => [n]) [101] [202] [.body] outside

theorem actual_lambda_ambient_child_word :
    sourceTerm.sourceTrail (fun n : Nat => [n]) [101] [202] [.body,.arg,.fn,.body,.body]=
      some [1,2,3,4,5,6] := by
  have equation := LTerm.sourceTrail_child_descendant (fun n : Nat => [n]) [101] [202]
    (t:=sourceTerm) (p:=[.body,.arg,.fn]) (childStep:=.body)
    (parent:=.lam (.atom 4) bodyTerm) (child:=bodyTerm) rfl rfl [.body]
  exact equation

#print axioms contextual_captured_copy
#print axioms contextual_retained_lambda
#print axioms actual_stem_preserved
#print axioms contextual_previous_body_splice
#print axioms contextual_retained_lambda_ambient
#print axioms contextual_protected_variable_ambient
#print axioms actual_strict_ancestor_word
#print axioms actual_lambda_ambient_child_word
#print axioms StepAt.sourceTrail_copy
#print axioms StepAt.sourceTrail_nonvariable
#print axioms StepAt.contractum_at_site
#print axioms StepAt.sourceStem_eq
#print axioms StepAt.sourceTrail_copy_splice
#print axioms StepAt.sourceTrail_retained_nonvariable
#print axioms StepAt.sourceTrail_retained_variable
#print axioms StepAt.sourceTrail_outside
#print axioms LTerm.sourceTrail_child_descendant
-- The port APIs below are dependency checks, not new physical-site fixtures.
#print axioms TermRoutes.redex_routes
#print axioms AG.SyntaxTrailImage.app_finish
#print axioms AG.SyntaxTrailImage.lam_finish
#print axioms AG.BetaSourcePorts.app_trail_last
#print axioms AG.BetaSourcePorts.lam_trail_last
#print axioms AG.PathSite.relative_current_redex_ports
end Lamping.Checks.ContextualEvaluation
