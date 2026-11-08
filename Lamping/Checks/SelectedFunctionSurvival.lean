import Lamping.Lambda.SelectedFunctionSurvival
import Lamping.Checks.ResidualTagImages
import Lamping.Checks.NodeLabelSuffixOrigins
import Lamping.Checks.SingleUnsafeCopyFunctionAppInputs

namespace Lamping.Checks.SelectedFunctionSurvivalChecks
open Lambda Lambda.Labelled

namespace Retained
open ResidualTagImagesChecks.Retained
def history : Labelled.History [[]] source target := .cons step (.nil _)
def markedHistory : Marked.History [[]] marked result := .cons reduction (.nil _)
def trace : BetaNodeHistoryPreimage history [] [.fn,.body] :=
  .one (step:=step) (remaining:=.nil _) rfl origin (.nil _ _)
theorem historical_tag : []∈Marked.tracePositions [.fn,.body] result := by
  obtain ⟨l,f,a,lookup⟩ : ∃l f a,target.subterm []=some (.app l f a) := ⟨_,_,_,rfl⟩
  exact markedHistory.trace_node_image (Marked.valid_mark F source.erase)
    (Marked.erase_mark F source.erase).symm trace lookup (by decide)
end Retained

namespace Copied
open ResidualTagImagesChecks.Copied
def history : Labelled.History [[]] source target := .cons step (.nil _)
def markedHistory : Marked.History [[]] marked result := .cons reduction (.nil _)
def leftTrace : BetaNodeHistoryPreimage history [.fn] [.arg] :=
  .one (step:=step) (remaining:=.nil _) rfl leftOrigin (.nil _ _)
def rightTrace : BetaNodeHistoryPreimage history [.arg] [.arg] :=
  .one (step:=step) (remaining:=.nil _) rfl rightOrigin (.nil _ _)
theorem two_actual_copy_tags :
    [.fn]∈Marked.tracePositions [.arg] result ∧ [.arg]∈Marked.tracePositions [.arg] result := by
  have leftLookup : ∃l f a,target.subterm [.fn]=some (.app l f a) := ⟨_,_,_,rfl⟩
  have rightLookup : ∃l f a,target.subterm [.arg]=some (.app l f a) := ⟨_,_,_,rfl⟩
  obtain ⟨l,f,a,atLeft⟩ := leftLookup
  obtain ⟨k,g,b,atRight⟩ := rightLookup
  exact ⟨markedHistory.trace_node_image (Marked.valid_mark F source.erase)
    (Marked.erase_mark F source.erase).symm leftTrace atLeft (by decide),
    markedHistory.trace_node_image (Marked.valid_mark F source.erase)
      (Marked.erase_mark F source.erase).symm rightTrace atRight (by decide)⟩
end Copied

namespace Complete
open NodeLabelSuffixOriginsChecks
abbrev F : List Path := [[.arg]]
abbrev endpoint : Marked := .app [[]] (.lam (.var 0))
  (.app [[.arg,.arg]] (.lam (.var 0)) (.lam (.var 0)))
def old : Marked.RelativeOldHistory F [[.arg]] (Marked.mark F source.erase) endpoint :=
  .cons (.appR (.redRoot _ _ _)) (by decide) (.nil _)
theorem normal : Marked.Normal endpoint := by simp [Marked.Normal]
theorem zero_step_selected_residual :
    [.arg]∈Marked.setResidualPositions F (Marked.mark F source.erase) := by
  obtain ⟨parent,_,_,coordinate,_,_,_,member⟩ :=
    (Marked.RelativeOldHistory.nil (F:=F) (Marked.mark F source.erase)).function_origin_selected_residual
      (.nil source) (by decide) redex_lookup (.nil source [.arg,.fn])
      (show source.subterm [.arg,.fn]=some (.lam (.atom 4) (.var (.atom 5) 0)) from rfl)
  have same : parent=[.arg] :=
    (List.append_cancel_right (show ([.arg]:Path)++[.fn]=parent++[.fn] from coordinate)).symm
  exact same ▸ member
theorem selected_function_consumed :
    ¬BetaNodeHistoryPreimage actualHistory [.arg,.fn] [.arg,.fn] := by
  exact old.normal_no_selected_function_origin actualHistory normal (by decide)
    redex_lookup (show target.subterm [.arg,.fn]=some (.lam (.atom 7) (.var (.atom 8) 0)) from rfl)
def rootFunctionTrace : BetaNodeHistoryPreimage actualHistory [.fn] [.fn] :=
  .one (step:=actualStep) (remaining:=.nil _) redex_lookup
    (.context (by rintro ⟨rest,equal⟩;cases equal)) (.nil _ _)
theorem unselected_function_really_survives :
    target.subterm [.fn]=some (.lam (.atom 1) (.var (.atom 2) 0)) ∧
    BetaNodeHistoryPreimage actualHistory [.fn] [.fn] ∧
    []∈Marked.tracePositions [] endpoint ∧ []∉F := ⟨rfl,rootFunctionTrace,by decide,by decide⟩
end Complete

namespace Incomplete
open SingleUnsafeCopyFunctionAppInputsChecks
abbrev oldArg : LTerm := match source with | .app _ _ a => a |t=>t
abbrev oldStamp : Label := oldArg.label
abbrev oldLambda : Label := match oldArg with | .app _ (.lam l _) _ => l |t=>t.label
abbrev oldBody : LTerm := match oldArg with | .app _ (.lam _ b) _ => b |t=>t
abbrev oldArgument : LTerm := match oldArg with | .app _ _ a => a |t=>t
def functionTrace : BetaNodeHistoryPreimage preHistory [.arg,.fn] [.arg,.fn] :=
  .one (step:=.fn (.root _ _ _ _)) (remaining:=.nil _) rfl
    (.context (by rintro ⟨rest,equal⟩;cases equal)) (.nil _ _)
theorem actual_selected_survivor :
    ∃parent stamp argument,[.arg,.fn]=parent++[.fn] ∧
      middle.subterm parent=some (.app stamp (.lam oldLambda oldBody) argument) ∧
      BetaNodeHistoryPreimage preHistory parent [.arg] ∧
      parent∈Marked.tracePositions [.arg] markedMiddle ∧
      parent∈Marked.setResidualPositions F markedMiddle := by
  exact event.beforeOld.function_origin_selected_residual preHistory (by decide)
    (show source.subterm [.arg]=some (.app oldStamp (.lam oldLambda oldBody) oldArgument) from rfl)
    functionTrace (show middle.subterm [.arg,.fn]=some (.lam oldLambda oldBody) from rfl)
theorem endpoint_not_normal : ¬Marked.Normal markedMiddle := by
  intro normal
  exact event.beforeOld.normal_no_selected_function_origin preHistory normal (by decide)
    (show source.subterm [.arg]=some (.app oldStamp (.lam oldLambda oldBody) oldArgument) from rfl)
    (show middle.subterm [.arg,.fn]=some (.lam oldLambda oldBody) from rfl) functionTrace
end Incomplete

#print axioms Retained.historical_tag
#print axioms Copied.two_actual_copy_tags
#print axioms Complete.normal
#print axioms Complete.zero_step_selected_residual
#print axioms Complete.selected_function_consumed
#print axioms Complete.unselected_function_really_survives
#print axioms Incomplete.actual_selected_survivor
#print axioms Incomplete.endpoint_not_normal
end Lamping.Checks.SelectedFunctionSurvivalChecks
