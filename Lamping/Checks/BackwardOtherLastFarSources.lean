import Lamping.Lamping.BackwardOtherLastFarSources
import Lamping.Checks.BackwardOtherLastTargets
namespace Lamping.Checks.BackwardOtherLastFarSourcesChecks
open Graph Lambda Lambda.Labelled AG SyntaxIncidence
namespace EmptyCopy
open UniformOldCreatedIncomingLabelsChecks.Distinct
abbrev event := SelectedOldOtherLastOriginsChecks.event
abbrev origin := SelectedOldOtherLastOriginsChecks.readingOrigin
abbrev trace := SelectedOldOtherLastOriginsChecks.ownLastTrace
abbrev last : Path := right++[.fn,.body]

def remaining : PrerequisiteChain target right [right,[.arg],[.fn]] :=
  .lam (parent:=[.arg]) (step:=.body) rfl (by decide)
    (.lam (parent:=[]) (step:=.arg) rfl (by decide) (.redex_app rfl))

def sourceBinder : ProperPosition source:=⟨right++[.fn],Or.inr ⟨.atom 7,.var (.atom 8) 0,rfl⟩⟩
theorem originalSource : Source source last (some sourceBinder) :=
  ⟨.body,.lam (.atom 7) (.var (.atom 8) 0),_,rfl,rfl,.body⟩

theorem actual_original_far_chain : ∃edges,EndpointChain source (some sourceBinder) edges := by
  obtain ⟨currentFar,far,original,oldFar,oldEdges,currentSource,currentChain,farSource,oldLookup,oldSource,oldChain,history⟩:=
    event.backward_original_far_available origin SelectedOldOtherLastOriginsChecks.actual_reading remaining (by decide) trace
  have eq:=Source.unique oldSource originalSource
  rw [eq] at oldChain
  exact ⟨oldEdges,oldChain⟩

theorem actual_current_parent_not_far :
    ∃currentFar : ProperPosition target,∃far : ProperPosition middle,∃edges,
      Source target right (some currentFar) ∧EndpointChain target (some currentFar) [[.arg],[.fn]] ∧
      Source middle last (some far) ∧EndpointChain middle (some far) edges ∧
      currentFar.val=[.arg] ∧far.val=right++[.fn] ∧currentFar.val≠far.val := by
  obtain ⟨currentFar,far,edges,currentSource,currentChain,farSource,farChain,relation⟩:=
    event.backward_far_source_available origin SelectedOldOtherLastOriginsChecks.actual_reading remaining (by decide)
  let currentParent : ProperPosition target:=⟨[.arg],Or.inr ⟨_,_,rfl⟩⟩
  let oldBinder : ProperPosition middle:=⟨right++[.fn],Or.inr ⟨.atom 7,.var (.atom 8) 0,rfl⟩⟩
  have cp : Source target right (some currentParent) := ⟨.body,_,_,rfl,rfl,.body⟩
  have op : Source middle last (some oldBinder) := ⟨.body,_,_,rfl,rfl,.body⟩
  have ce:=Option.some.inj (Source.unique currentSource cp)
  have oe:=Option.some.inj (Source.unique farSource op)
  refine ⟨currentFar,far,edges,currentSource,currentChain,farSource,farChain,?_,?_,?_⟩
  · exact congrArg Subtype.val ce
  · exact congrArg Subtype.val oe
  · rw [ce,oe];decide

def ownUncreated : UncreatedNodeHistoryPreimage event.labels last last :=
  .one (step:=firstStep) (by rfl) (.context (by rintro ⟨rest,impossible⟩;cases impossible))
    (by decide) (.nil _ _)

theorem actual_uncreated_source_ancestry : ∃far : ProperPosition middle,∃oldFar : ProperPosition source,∃edges,
    Source middle last (some far) ∧Source source last (some oldFar) ∧EndpointChain source (some oldFar) edges ∧
    BetaVertexHistoryPreimage event.labels (some far) (some oldFar) := by
  obtain ⟨currentFar,far,original,oldFar,oldEdges,currentSource,currentChain,farSource,oldLookup,oldSource,oldChain,history⟩:=
    event.backward_original_far_available origin SelectedOldOtherLastOriginsChecks.actual_reading remaining (by decide) trace
  exact ⟨far,oldFar,oldEdges,farSource,oldSource,oldChain,history ownUncreated⟩


theorem q0_not_current_after_parent_hom :
    let currentParent : ProperPosition target:=⟨[.arg],Or.inr ⟨_,_,rfl⟩⟩
    let selectedLambda : ProperPosition middle:=⟨right++[.fn],Or.inr ⟨.atom 7,.var (.atom 8) 0,rfl⟩⟩
    ¬BetaVertexPreimage event.body event.argument right middle target (some currentParent) (some selectedLambda) := by
  dsimp only
  intro actual
  cases actual with
  | proper origin =>
    have unchanged : BetaNodePreimage event.body event.argument right [.arg] [.arg] := .context (by
      rintro ⟨relative,eq⟩
      have length:=congrArg List.length eq
      simp only [right,List.length_cons,List.length_nil,List.length_append] at length
      omega)
    have impossible:=origin.unique unchanged
    change right++[.fn]=[.arg] at impossible
    cases impossible
end EmptyCopy

namespace NonemptyCopy
abbrev I : Term:=WrappedSuccessfulChains.I
abbrev source : LTerm:=initLabels (.app (.lam (.app (.var 0) (.var 0))) I)
abbrev body : LTerm:=.app (.atom 2) (.var (.atom 3) 0) (.var (.atom 4) 0)
abbrev arg : LTerm:=.lam (.atom 5) (.var (.atom 6) 0)
abbrev target : LTerm:=LTerm.contract (.atom 0) (.atom 1) body arg
abbrev F : List Path:=[[]]
def event : SelectedOldTurn F source (.atom 1) [] source target [] where
  markedBefore := Marked.mark F source.erase
  markedAfter := .app [] (.lam (.var 0)) (.lam (.var 0))
  beforeOld := .nil _
  reduction := .redRoot _ _ _
  member := by decide
  labels := .nil _
  turn := .root _ _ _ _
  beta := .atom 0
  body := body
  argument := arg
  redex := rfl

def origin : BetaIncomingReadingOrigin body arg [] [.arg] [.arg] [.arg] [.arg] [.fn,.body,.arg] :=
  .copyLambda (q:=[.arg]) rfl rfl rfl rfl

theorem reading : PrerequisiteReadsDirected target [.arg] [.arg] false := ⟨Or.inr ⟨_,_,rfl,rfl⟩,rfl⟩
def remaining : PrerequisiteChain target [.arg] [[.arg],[.fn]] := .lam (parent:=[]) (step:=.arg) rfl (by decide) (.redex_app rfl)

theorem actual_retained_parent_far : ∃currentFar : ProperPosition target,∃far : ProperPosition source,∃edges,
    Source target [.arg] (some currentFar) ∧EndpointChain target (some currentFar) [[.fn]] ∧
    Source source [.fn,.body,.arg] (some far) ∧EndpointChain source (some far) edges ∧
    (BetaVertexPreimage body arg [] source target (some currentFar) (some far) ∨far.val=[.fn]) :=
  event.backward_far_source_available origin reading remaining (by decide)

theorem actual_original_retained_far : ∃currentFar : ProperPosition target,∃far : ProperPosition source,
    ∃original oldFar oldEdges,
      Source target [.arg] (some currentFar) ∧EndpointChain target (some currentFar) [[.fn]] ∧
      Source source [.fn,.body,.arg] (some far) ∧source.subterm [.fn,.body,.arg]=some original ∧
      Source source [.fn,.body,.arg] (some oldFar) ∧EndpointChain source (some oldFar) oldEdges ∧
      (UncreatedNodeHistoryPreimage event.labels [.fn,.body,.arg] [.fn,.body,.arg] →
       BetaVertexHistoryPreimage event.labels (some far) (some oldFar)) :=
  event.backward_original_far_available origin reading remaining (by decide) (.nil _ _)

-- A FUNCTION terminal read has no AFTER reader. Its real far APP chain
-- is derived separately from the true function-variable/binder geometry.
def terminalOrigin : BetaIncomingReadingOrigin body arg [] [.fn] [.fn] [.arg] [.arg] [.fn,.body,.fn] :=
  .copyLambda (q:=[.fn]) rfl rfl rfl rfl

theorem terminalRead : PrerequisiteReadsDirected target [.fn] [.fn] false := ⟨Or.inr ⟨_,_,rfl,rfl⟩,rfl⟩
def terminalChain : PrerequisiteChain target [.fn] [[.fn]] := .redex_lam (p:=[]) rfl

def bodyApp : ProperPosition source:=⟨[.fn,.body],Or.inl ⟨.atom 2,.var (.atom 3) 0,.var (.atom 4) 0,rfl⟩⟩
theorem terminal_far_app_available : Source source [.fn,.body,.fn] (some bodyApp) ∧
    EndpointChain source (some bodyApp) [[.fn,.body,.fn],[.fn]] :=
  ⟨⟨.fn,body,_,rfl,rfl,.fn⟩,
   .app rfl (by intro a b eq;cases eq) (.var (parent:=[.fn]) (rest:=[.fn]) rfl rfl rfl rfl (.redex_lam (p:=[]) rfl))⟩

theorem actual_initial_closed_history : INIT source ∧History [[]] source target ∧Closed source.erase :=
  ⟨init_is_INIT _,.cons event.turn (.nil _),by change (0<1 ∧0<1) ∧0<1;decide⟩
end NonemptyCopy

namespace ResultContext
abbrev I : Term:=WrappedSuccessfulChains.I
abbrev source : LTerm:=initLabels (.app I (.app (.lam (.lam (.var 0))) I))
abbrev body : LTerm:=.lam (.atom 5) (.var (.atom 6) 0)
abbrev arg : LTerm:=.lam (.atom 7) (.var (.atom 8) 0)
abbrev target : LTerm:=.app (.atom 0) (.lam (.atom 1) (.var (.atom 2) 0)) (LTerm.contract (.atom 3) (.atom 4) body arg)
abbrev F : List Path:=[[.arg]]
def event : SelectedOldTurn F source (.atom 4) [] source target [.arg] where
  markedBefore := Marked.mark F source.erase
  markedAfter := .app [[]] (.lam (.var 0)) (.lam (.var 0))
  beforeOld := .nil _
  reduction := .appR (.redRoot _ _ _)
  member := by decide
  labels := .nil _
  turn := .arg (.root _ _ _ _)
  beta := .atom 3
  body := body
  argument := arg
  redex := rfl

def origin : BetaIncomingReadingOrigin body arg [.arg] [.arg] [.arg] [.arg,.fn,.body] [.arg,.fn,.body] [.arg] :=
  .resultLambda rfl rfl rfl

theorem reading : PrerequisiteReadsDirected target [.arg] [.arg] false := ⟨Or.inr ⟨_,_,rfl,rfl⟩,rfl⟩
def remaining : PrerequisiteChain target [.arg] [[.arg],[.fn]] := .lam (parent:=[]) (step:=.arg) rfl (by decide) (.redex_app rfl)

def root : ProperPosition source:=⟨[],Or.inl ⟨_,_,_,rfl⟩⟩
theorem actual_original_context_far : ∃edges,Source source [.arg] (some root) ∧EndpointChain source (some root) edges := by
  obtain ⟨currentFar,far,original,oldFar,oldEdges,currentSource,currentChain,farSource,oldLookup,oldSource,oldChain,history⟩:=
    event.backward_original_far_available origin reading remaining (by decide) (.nil _ _)
  have sourceRoot : Source source [.arg] (some root) := ⟨.arg,_,_,rfl,rfl,.arg⟩
  have eq:=Source.unique oldSource sourceRoot
  rw [eq] at oldChain
  exact ⟨oldEdges,sourceRoot,oldChain⟩

theorem actual_initial_history : INIT source ∧History [[.arg]] source target :=
  ⟨init_is_INIT _,.cons event.turn (.nil _)⟩
end ResultContext

namespace ExternalException
open BackwardOtherLastTargetsChecks.ResultLambda

theorem actual_root_external_far : Source source [] none ∧¬∃edges,EndpointChain source none edges :=
  ⟨rfl,by rintro ⟨edges,impossible⟩;exact impossible⟩

theorem actual_no_successful_root_lambda : NoPrerequisite target [] := by
  rintro ⟨edges,chain⟩
  have lookup : target.subterm []=some (.lam _ (.var (.atom 3) 0)) := rfl
  rcases chain.lambda_cases lookup with ⟨parent,a,arg,split,atApp,eq⟩ | ⟨parent,child,tail,split,notFn,eq,actual⟩
  · have length:=congrArg List.length split;simp at length
  · have length:=congrArg List.length split;simp at length
end ExternalException

#print axioms SelectedOldTurn.backward_far_source_available
#print axioms SelectedOldTurn.backward_original_far_available
#print axioms EmptyCopy.actual_original_far_chain
#print axioms EmptyCopy.actual_current_parent_not_far
#print axioms EmptyCopy.actual_uncreated_source_ancestry
#print axioms EmptyCopy.q0_not_current_after_parent_hom
#print axioms NonemptyCopy.actual_retained_parent_far
#print axioms NonemptyCopy.actual_original_retained_far
#print axioms NonemptyCopy.actual_initial_closed_history
#print axioms NonemptyCopy.terminalChain
#print axioms NonemptyCopy.terminal_far_app_available
#print axioms ResultContext.actual_original_context_far
#print axioms ResultContext.actual_initial_history
#print axioms ExternalException.actual_root_external_far
#print axioms ExternalException.actual_no_successful_root_lambda
end Lamping.Checks.BackwardOtherLastFarSourcesChecks
