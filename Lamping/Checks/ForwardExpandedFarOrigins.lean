import Lamping.Lamping.ForwardExpandedFarOrigins
import Lamping.Checks.WrappedSuccessfulChains

namespace Lamping.Checks.ForwardExpandedFarOriginsChecks
open Graph Lambda Lambda.Labelled AG SyntaxIncidence
namespace Overlap
abbrev I : Term := .lam (.var 0)
abbrev original : LTerm := initLabels (.app I (.app (.app I (.app I I)) I))
abbrev source : LTerm := WrappedSuccessfulChains.contractRoot original
abbrev body : LTerm := .var (.atom 6) 0
abbrev argument : LTerm := .app (.atom 7) (.lam (.atom 8) (.var (.atom 9) 0))
  (.lam (.atom 10) (.var (.atom 11) 0))
abbrev target : LTerm := .app source.label (LTerm.contract (.atom 4) (.atom 5) body argument)
  (.lam (.atom 12) (.var (.atom 13) 0))
abbrev F : List Path := [[.fn]]

def prefixHistory : History [[]] original source := .cons (.root _ _ _ _) (.nil _)
def turn : StepAt [.fn] source target := .fn (.root _ _ _ _)
def event : SelectedOldTurn F source (.atom 5) [] source target [.fn] where
  markedBefore := Marked.mark F source.erase
  markedAfter := .app [] (.app [[.fn,.arg]] (.lam (.var 0)) (.lam (.var 0))) (.lam (.var 0))
  beforeOld := .nil _
  reduction := by
    change Marked.ReductionAt [.fn]
      (.app [] (.red [[.fn]] (.var 0) (.app [[.fn,.arg]] (.lam (.var 0)) (.lam (.var 0)))) (.lam (.var 0)))
      (.app [] (.app [[.fn,.arg]] (.lam (.var 0)) (.lam (.var 0))) (.lam (.var 0)))
    exact .appL (.redRoot _ _ _)
  member := by decide
  labels := .nil _
  turn := turn
  beta := .atom 4
  body := body
  argument := argument
  redex := rfl

theorem initial : INIT original := init_is_INIT _
theorem originalClosed : Closed original.erase := by
  simp [Closed,Scoped,original,initLabels,initFrom,nodeCount,LTerm.erase]
theorem sourceClosed : Closed source.erase := prefixHistory.closed originalClosed
theorem targetClosed : Closed target.erase := event.final_history.closed sourceClosed
theorem sourceNotInit : ¬INIT source := root_contract_not_INIT _ _ _ _

def origin : BetaIncomingReadingOrigin body argument [.fn] [.fn] [] [] [.fn] [.fn,.fn,.body] :=
  .resultFunction rfl rfl
def reading : PrerequisiteReadsDirected target [] [.fn] true := ⟨Or.inl ⟨_,_,_,rfl,rfl⟩,rfl⟩
def remaining : PrerequisiteChain target [] [[.fn],[.fn,.fn]] :=
  .app rfl (by intro stamp b impossible;cases impossible) (.redex_app (p:=[.fn]) rfl)
def sourceTail : PrerequisiteChain source [.fn,.arg] [[.fn,.arg,.fn]] := .redex_app (p:=[.fn,.arg]) rfl
def sourceArgument : ProperPosition source := ⟨[.fn,.arg],Or.inl ⟨_,_,_,rfl⟩⟩
def sourceSelected : ProperPosition source := ⟨[.fn,.fn],Or.inr ⟨_,_,rfl⟩⟩

theorem knownNodeOrigin : BetaNodePreimage body argument [.fn] [.fn] [.fn,.arg] := by
  simpa only [List.append_nil] using
    (BetaNodePreimage.copied (site:=[.fn]) (q:=[]) (relative:=[]) (old:=argument)
      (show ArgumentOccurrence body.erase [] from rfl) (show argument.subterm []=some argument from rfl))

private theorem five_edges (es : List Path) (ds : List Bool)
    (expansion : CreatedReadingExpansion body [.fn] [.fn] [.fn,.fn,.body] true es ds) :
    es=[[.fn],[.fn,.fn],[.fn,.fn,.body],[.fn,.fn],[.fn,.arg]] := by
  cases expansion with
  | resultFunction other => exact False.elim (other (.atom 6) rfl)
  | resultOverlap shape => rfl

theorem actual_expanded_source :
    ∃out : ForwardExpandedFarOutput event [] [.fn] [] [.fn] [.fn,.fn,.body] [[.fn,.fn]],
      out.middlePosition=[.fn,.arg] ∧out.sourcePosition=[.fn,.arg] ∧
      out.sourceEdges=[[.fn,.arg,.fn]] ∧
      out.expandedEdges=[[.fn],[.fn,.fn],[.fn,.fn,.body],[.fn,.fn],[.fn,.arg]] ∧
      out.expandedFar=some sourceArgument ∧out.sourceFar=some sourceArgument := by
  obtain ⟨out⟩:=event.forward_expanded_far_output sourceClosed origin reading
    (show target.subterm [.fn]=some (LTerm.contract (.atom 4) (.atom 5) body argument) from rfl)
    remaining (by decide)
  have middleEq:=out.nodeOrigin.unique knownNodeOrigin
  have sourceEq := out.prefixTrace.unique (.nil source out.middlePosition)
  have actualSource : out.sourcePosition=[.fn,.arg] := sourceEq.trans middleEq
  have actualChain : PrerequisiteChain source [.fn,.arg] out.sourceEdges := by
    rw [←actualSource];exact out.sourceChain
  have edgesEq:=actualChain.unique sourceTail
  have expandedAt : Target source [.fn,.arg] out.expandedFar := by rw [←middleEq];exact out.expandedTarget
  have sourceAt : Target source [.fn,.arg] out.sourceFar := by rw [←actualSource];exact out.sourceTarget
  have knownTarget : Target source [.fn,.arg] (some sourceArgument) := Or.inl rfl
  have expandedEq:=Target.unique expandedAt knownTarget
  have farEq:=Target.unique sourceAt knownTarget
  have five : out.expandedEdges=[[.fn],[.fn,.fn],[.fn,.fn,.body],[.fn,.fn],[.fn,.arg]] := by
    exact five_edges _ _ out.expansion
  exact ⟨out,middleEq,actualSource,edgesEq,five,expandedEq,farEq⟩

theorem triple_LAST_targets_another_vertex :
    Target source [.fn,.fn,.body] (some sourceSelected) ∧
    (sourceSelected.val≠sourceArgument.val) :=
  ⟨Or.inr ⟨_,0,_,_,[],rfl,rfl,rfl,rfl⟩,by decide⟩

theorem real_nonempty_after_and_prior :
    INIT original ∧Closed original.erase ∧History [[],[.fn]] original target ∧
      ¬INIT source ∧PrerequisiteChain target [] [[.fn],[.fn,.fn]] :=
  ⟨initial,originalClosed,prefixHistory.append event.final_history,sourceNotInit,remaining⟩
end Overlap
#print axioms Overlap.actual_expanded_source
#print axioms Overlap.triple_LAST_targets_another_vertex
#print axioms Overlap.real_nonempty_after_and_prior
end Lamping.Checks.ForwardExpandedFarOriginsChecks
