import Lamping.Lambda.LambdaOuterAtomSupport
import Lamping.Checks.ResidualTagImages
import Lamping.Checks.NodeLabelSuffixOrigins
import Lamping.Checks.HistoryEndpointAvailability

namespace Lamping.Checks.LambdaOuterAtomSupportChecks
open Lambda Lambda.Labelled

/-- A real zero-step original lambda keeps its exact coordinate. -/
theorem nil_lambda :
    ∃label body,(LTerm.lam (.atom 1) (.var (.atom 2) 0))=.lam label body ∧
      label.lastAtom=some 1 ∧
      BetaNodeHistoryPreimage (.nil NodeLabelSuffixOriginsChecks.source) [.fn] [.fn] :=
  (History.nil NodeLabelSuffixOriginsChecks.source).original_lambda_outer_atom_origin NodeLabelSuffixOriginsChecks.initial
    (oldPosition:=[.fn]) rfl rfl (by decide)

def retainedHistory : History [[]] NodeLabelSuffixOriginsChecks.retainedSource NodeLabelSuffixOriginsChecks.retainedTarget :=
  .cons NodeLabelSuffixOriginsChecks.retainedStep (.nil _)

/-- Actual marked compound lambda: constructor and original BODY coordinate
are internally recovered from atom2, not supplied as an origin premise. -/
theorem retained_lambda :
    ∃label body,NodeLabelSuffixOriginsChecks.retainedTarget=.lam label body ∧label.lastAtom=some 2 ∧
      BetaNodeHistoryPreimage retainedHistory [] [.fn,.body] :=
  retainedHistory.original_lambda_outer_atom_origin (init_is_INIT _)
    (oldPosition:=[.fn,.body]) rfl rfl (by decide)

theorem retained_reverse_outer :
    Letter.atom 2∈NodeLabelSuffixOriginsChecks.retainedTarget.label.readLetters false := by decide

def copiedHistory : History [[]] ResidualTagImagesChecks.Copied.source ResidualTagImagesChecks.Copied.target := .cons ResidualTagImagesChecks.Copied.step (.nil _)
abbrev copiedLambda : LTerm := .lam (.atom 6) (.var (.atom 7) 0)

theorem copied_left_lambda :
    ∃label body,copiedLambda=.lam label body ∧label.lastAtom=some 6 ∧
      BetaNodeHistoryPreimage copiedHistory [.fn,.fn] [.arg,.fn] :=
  copiedHistory.original_lambda_outer_atom_origin ResidualTagImagesChecks.Copied.initial
    (oldPosition:=[.arg,.fn]) rfl rfl (by decide)

theorem copied_right_lambda :
    ∃label body,copiedLambda=.lam label body ∧label.lastAtom=some 6 ∧
      BetaNodeHistoryPreimage copiedHistory [.arg,.fn] [.arg,.fn] :=
  copiedHistory.original_lambda_outer_atom_origin ResidualTagImagesChecks.Copied.initial
    (oldPosition:=[.arg,.fn]) rfl rfl (by decide)

theorem different_current_copies : ([.fn,.fn]:Path)≠[.arg,.fn] := by decide

/-- Genuine canonical two-step, different-degree history. Atom9 survives a
compound prefix while lambda4 and lambda7 occur only inside bar payloads. -/
theorem two_step_lambda :
    ∃label body,HistoryEndpointAvailabilityChecks.finalArgument=.lam label body ∧label.lastAtom=some 9 ∧
      BetaNodeHistoryPreimage HistoryEndpointAvailabilityChecks.labels [.arg] [.arg,.arg,.arg] :=
  HistoryEndpointAvailabilityChecks.labels.original_lambda_outer_atom_origin NodeLabelSuffixOriginsChecks.initial
    (oldPosition:=[.arg,.arg,.arg]) rfl rfl (by decide)

theorem two_step_not_atomic : ¬IsAtomic HistoryEndpointAvailabilityChecks.finalArgument.label := by
  rintro ⟨n,impossible⟩
  cases impossible

theorem variable_prefix_nonlambda :
    Letter.atom 5∈NodeLabelSuffixOriginsChecks.currentArgument.label.letters ∧
    NodeLabelSuffixOriginsChecks.source.subterm [.arg,.fn,.body]=some (.var (.atom 5) 0) ∧
    (¬∃label body,NodeLabelSuffixOriginsChecks.currentArgument=.lam label body) ∧
    NodeLabelSuffixOriginsChecks.currentArgument.label.lastAtom=some 6 := by
  refine ⟨by decide,rfl,?_,rfl⟩
  rintro ⟨label,body,impossible⟩
  cases impossible

theorem consumed_lambda_payload_only :
    Letter.atom 4∉NodeLabelSuffixOriginsChecks.currentArgument.label.letters ∧
    Letter.over (.atom 4)∈NodeLabelSuffixOriginsChecks.currentArgument.label.letters ∧
    Letter.under (.atom 4)∈NodeLabelSuffixOriginsChecks.currentArgument.label.letters := by decide

namespace RootCopy
abbrev source : LTerm := initLabels (.app WrappedSuccessfulChains.I WrappedSuccessfulChains.I)
abbrev target : LTerm := WrappedSuccessfulChains.contractRoot source
def step : StepAt [] source target := .root _ _ _ _
def labels : History [[]] source target := .cons step (.nil _)

theorem copied_root_lambda :
    ∃label body,target=.lam label body ∧label.lastAtom=some 3 ∧
      BetaNodeHistoryPreimage labels [] [.arg] :=
  labels.original_lambda_outer_atom_origin (init_is_INIT _)
    (oldPosition:=[.arg]) rfl rfl (by decide)

/-- APP0 and VAR2 really become plain prefixes of a current lambda. They
are not original-lambda atoms and cannot use the new restricted theorem. -/
theorem app_variable_prefix_negative :
    source.subterm []=some (.app (.atom 0)
      (.lam (.atom 1) (.var (.atom 2) 0)) (.lam (.atom 3) (.var (.atom 4) 0))) ∧
    target.label.letters=[.atom 0,.over (.atom 1),.atom 2,.under (.atom 1),.atom 3] ∧
    target.constructorTag=1 ∧target.label.lastAtom=some 3 ∧
    target.label.lastAtom≠some 0 ∧target.label.lastAtom≠some 2 := by
  exact ⟨rfl,rfl,rfl,rfl,by decide,by decide⟩
end RootCopy

#print axioms nil_lambda
#print axioms retained_lambda
#print axioms retained_reverse_outer
#print axioms copied_left_lambda
#print axioms copied_right_lambda
#print axioms different_current_copies
#print axioms two_step_lambda
#print axioms two_step_not_atomic
#print axioms variable_prefix_nonlambda
#print axioms consumed_lambda_payload_only
#print axioms RootCopy.copied_root_lambda
#print axioms RootCopy.app_variable_prefix_negative
end Lamping.Checks.LambdaOuterAtomSupportChecks
