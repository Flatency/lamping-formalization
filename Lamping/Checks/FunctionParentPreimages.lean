import Lamping.Lambda.FunctionParentPreimages

namespace Lamping.Checks.FunctionParentPreimagesChecks
open Lambda Lambda.Labelled

def zero : Label:=.atom 0
def identity : LTerm:=.lam zero (.var zero 0)
def oldRedex : LTerm:=.app zero identity identity
def retainedSource : LTerm:=.app zero (.lam zero oldRedex) identity
def retainedTarget : LTerm:=LTerm.contract zero zero oldRedex identity
def copiedSource : LTerm:=.app zero identity oldRedex
def copiedTarget : LTerm:=LTerm.contract zero zero (.var zero 0) oldRedex
def contextSource : LTerm:=.app zero oldRedex (.app zero identity identity)
def contextTarget : LTerm:=.app zero oldRedex (LTerm.contract zero zero (.var zero 0) identity)

theorem retained_step : StepAt [] retainedSource retainedTarget:=.root zero zero oldRedex identity
theorem copied_step : StepAt [] copiedSource copiedTarget:=.root zero zero (.var zero 0) oldRedex
theorem context_step : StepAt [.arg] contextSource contextTarget:=.arg (.root zero zero (.var zero 0) identity)

theorem retained_function_origin :
    BetaNodePreimage oldRedex identity [] [.fn] [.fn,.body,.fn] :=
  .retained (show oldRedex.subterm [.fn]=some identity from rfl) (by intro stamp impossible;cases impossible)

theorem copied_function_origin :
    BetaNodePreimage (.var zero 0) oldRedex [] [.fn] [.arg,.fn] :=
  .copied (body:=.var zero 0) (site:=[]) (q:=[]) (relative:=[.fn])
    (show ArgumentOccurrence (.var 0) [] from rfl)
    (show oldRedex.subterm [.fn]=some identity from rfl)

theorem context_function_origin :
    BetaNodePreimage (.var zero 0) identity [.arg] [.fn,.fn] [.fn,.fn] := by
  apply BetaNodePreimage.context
  rintro ⟨relative,equal⟩
  cases equal

/-- A genuine retained old redex constructs the current root APP parent. -/
theorem retained_actual_parent :
    ∃ appStamp argument,retainedTarget.subterm []=some (.app appStamp identity argument) ∧
      BetaNodePreimage oldRedex identity [] [] [.fn,.body] := by
  obtain ⟨parent,appStamp,argument,split,lookup,origin⟩:=
    retained_step.function_preimage_redex_parent
      (oldParent:=[.fn,.body]) rfl rfl retained_function_origin
      (show retainedTarget.subterm [.fn]=some (.lam zero (.var zero 0)) from rfl)
  have parentEmpty : parent=[] :=
    (List.append_cancel_right (show ([]:Path)++[.fn]=parent++[.fn] from split)).symm
  subst parent
  exact ⟨appStamp,argument,lookup,origin⟩

/-- An actual copied argument FUNCTION child constructs its copied APP parent. -/
theorem copied_actual_parent :
    ∃ appStamp argument,copiedTarget.subterm []=some (.app appStamp identity argument) ∧
      BetaNodePreimage (.var zero 0) oldRedex [] [] [.arg] := by
  obtain ⟨parent,appStamp,argument,split,lookup,origin⟩:=
    copied_step.function_preimage_redex_parent (oldParent:=[.arg]) rfl rfl copied_function_origin
      (show copiedTarget.subterm [.fn]=some (.lam zero (.var zero 0)) from rfl)
  have parentEmpty : parent=[] :=
    (List.append_cancel_right (show ([]:Path)++[.fn]=parent++[.fn] from split)).symm
  subst parent
  exact ⟨appStamp,argument,lookup,origin⟩

/-- The real context case retains the literal old FN parent coordinate. -/
theorem context_actual_parent :
    ∃ appStamp argument,contextTarget.subterm [.fn]=some (.app appStamp identity argument) ∧
      BetaNodePreimage (.var zero 0) identity [.arg] [.fn] [.fn] := by
  obtain ⟨parent,appStamp,argument,split,lookup,origin⟩:=
    context_step.function_preimage_redex_parent (oldParent:=[.fn]) rfl rfl context_function_origin
      (show contextTarget.subterm [.fn,.fn]=some (.lam zero (.var zero 0)) from rfl)
  have parentEq : parent=[.fn] :=
    (List.append_cancel_right (show ([.fn]:Path)++[.fn]=parent++[.fn] from split)).symm
  subst parent
  exact ⟨appStamp,argument,lookup,origin⟩

/-- The contracted FUNCTION lambda has no retained/copy/context descendant.
It cannot be a positive input to the new parent theorem. -/
theorem contracted_function_deleted (body argument : LTerm) (p : Path) :
    ¬BetaNodePreimage body argument [] p [.fn] := by
  intro origin
  rcases origin.coordinates with ⟨equal,outside⟩ |
      ⟨relative,old,atCurrent,atOld,oldLookup,nonselected⟩ |
      ⟨q,relative,old,occurs,atCurrent,atOld,oldLookup⟩
  · exact outside ⟨p,rfl⟩
  · have lengths:=congrArg List.length atOld
    simp only [List.length_cons,List.length_nil,List.length_append] at lengths
    omega
  · cases atOld

#print axioms retained_step
#print axioms copied_step
#print axioms context_step
#print axioms retained_function_origin
#print axioms copied_function_origin
#print axioms context_function_origin
#print axioms retained_actual_parent
#print axioms copied_actual_parent
#print axioms context_actual_parent
#print axioms contracted_function_deleted
end Lamping.Checks.FunctionParentPreimagesChecks
