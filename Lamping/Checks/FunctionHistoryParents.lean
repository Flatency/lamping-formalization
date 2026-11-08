import Lamping.Lambda.FunctionHistoryParents
import Lamping.Checks.FunctionParentPreimages

namespace Lamping.Checks.FunctionHistoryParentsChecks
open Lambda Lambda.Labelled FunctionParentPreimagesChecks

def retainedHistory : History [[]] retainedSource retainedTarget:=.cons retained_step (.nil _)
def copiedHistory : History [[]] copiedSource copiedTarget:=.cons copied_step (.nil _)

theorem retained_trace : BetaNodeHistoryPreimage retainedHistory [.fn] [.fn,.body,.fn] :=
  .one (step:=retained_step) (remaining:=.nil retainedTarget) rfl retained_function_origin (.nil _ _)
theorem copied_trace : BetaNodeHistoryPreimage copiedHistory [.fn] [.arg,.fn] :=
  .one (step:=copied_step) (remaining:=.nil copiedTarget) rfl copied_function_origin (.nil _ _)

theorem nil_actual_parent :
    ∃appStamp argument,oldRedex.subterm []=some (.app appStamp identity argument) ∧
      BetaNodeHistoryPreimage (.nil oldRedex) [] [] := by
  obtain ⟨parent,appStamp,argument,split,lookup,origin⟩:=
    BetaNodeHistoryPreimage.function_redex_parent (labels:=.nil oldRedex) (name:=[])
      rfl (.nil _ [.fn]) (show oldRedex.subterm [.fn]=some (.lam zero (.var zero 0)) from rfl)
  have empty : parent=[] :=
    (List.append_cancel_right (show ([]:Path)++[.fn]=parent++[.fn] from split)).symm
  subst parent
  exact ⟨appStamp,argument,lookup,origin⟩

theorem retained_actual_parent :
    ∃appStamp argument,retainedTarget.subterm []=some (.app appStamp identity argument) ∧
      BetaNodeHistoryPreimage retainedHistory [] [.fn,.body] := by
  obtain ⟨parent,appStamp,argument,split,lookup,origin⟩:=
    BetaNodeHistoryPreimage.function_redex_parent (labels:=retainedHistory) (name:=[.fn,.body])
      rfl retained_trace (show retainedTarget.subterm [.fn]=some (.lam zero (.var zero 0)) from rfl)
  have empty : parent=[] :=
    (List.append_cancel_right (show ([]:Path)++[.fn]=parent++[.fn] from split)).symm
  subst parent
  exact ⟨appStamp,argument,lookup,origin⟩

theorem copied_actual_parent :
    ∃appStamp argument,copiedTarget.subterm []=some (.app appStamp identity argument) ∧
      BetaNodeHistoryPreimage copiedHistory [] [.arg] := by
  obtain ⟨parent,appStamp,argument,split,lookup,origin⟩:=
    BetaNodeHistoryPreimage.function_redex_parent (labels:=copiedHistory) (name:=[.arg])
      rfl copied_trace (show copiedTarget.subterm [.fn]=some (.lam zero (.var zero 0)) from rfl)
  have empty : parent=[] :=
    (List.append_cancel_right (show ([]:Path)++[.fn]=parent++[.fn] from split)).symm
  subst parent
  exact ⟨appStamp,argument,lookup,origin⟩

def firstResult : LTerm:=LTerm.contract zero zero (.var zero 0) identity
def twoSource : LTerm:=.app zero oldRedex (.app zero identity (.app zero identity identity))
def twoMiddle : LTerm:=.app zero oldRedex (.app zero identity firstResult)
def twoTarget : LTerm:=.app zero oldRedex (LTerm.contract zero zero (.var zero 0) firstResult)

theorem stepOne : StepAt [.arg,.arg] twoSource twoMiddle:=.arg (.arg (.root zero zero (.var zero 0) identity))
theorem stepTwo : StepAt [.arg] twoMiddle twoTarget:=.arg (.root zero zero (.var zero 0) firstResult)
def twoHistory : History [[.arg,.arg],[.arg]] twoSource twoTarget:=
  .cons stepOne (.cons stepTwo (.nil _))

theorem two_trace : BetaNodeHistoryPreimage twoHistory [.fn,.fn] [.fn,.fn] := by
  have first : BetaNodePreimage (.var zero 0) identity [.arg,.arg] [.fn,.fn] [.fn,.fn] := by
    apply BetaNodePreimage.context
    rintro ⟨relative,equal⟩;cases equal
  have second : BetaNodePreimage (.var zero 0) firstResult [.arg] [.fn,.fn] [.fn,.fn] := by
    apply BetaNodePreimage.context
    rintro ⟨relative,equal⟩;cases equal
  exact .one (step:=stepOne) (remaining:=.cons stepTwo (.nil twoTarget)) rfl first
    (.one (step:=stepTwo) (remaining:=.nil twoTarget) rfl second (.nil _ _))

/-- Two genuine contractions on the right leave the old left redex's
FUNCTION lambda and its literal FN parent intact through the SAME trace. -/
theorem two_actual_parent :
    ∃appStamp argument,twoTarget.subterm [.fn]=some (.app appStamp identity argument) ∧
      BetaNodeHistoryPreimage twoHistory [.fn] [.fn] := by
  obtain ⟨parent,appStamp,argument,split,lookup,origin⟩:=
    BetaNodeHistoryPreimage.function_redex_parent (labels:=twoHistory) (name:=[.fn])
      rfl two_trace (show twoTarget.subterm [.fn,.fn]=some (.lam zero (.var zero 0)) from rfl)
  have parentEq : parent=[.fn] :=
    (List.append_cancel_right (show ([.fn]:Path)++[.fn]=parent++[.fn] from split)).symm
  subst parent
  exact ⟨appStamp,argument,lookup,origin⟩

theorem consumed_function_no_trace (body argument : LTerm) (p : Path) :
    ¬BetaNodeHistoryPreimage (.cons (.root zero zero body argument) (.nil _)) p [.fn] := by
  intro trace
  cases trace with
  | one redex origin tail => exact contracted_function_deleted _ _ _ origin

#print axioms retained_trace
#print axioms copied_trace
#print axioms nil_actual_parent
#print axioms retained_actual_parent
#print axioms copied_actual_parent
#print axioms stepOne
#print axioms stepTwo
#print axioms two_trace
#print axioms two_actual_parent
#print axioms consumed_function_no_trace
end Lamping.Checks.FunctionHistoryParentsChecks
