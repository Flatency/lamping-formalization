import Lamping.Lamping.TerminalCreatedReadingFarChains
import Lamping.Checks.BackwardOtherLastFarSources
namespace Lamping.Checks.TerminalCreatedReadingFarChainsChecks
open Graph Lambda Lambda.Labelled AG SyntaxIncidence

private def MiddleSupply (middle : LTerm) (site : Path) (es : List Path) : Prop :=
  ∃far : ProperPosition middle,
    ∃_low : ExpandedLastSelectedEndpoint middle site (es.getLastD []) false (some far),
      EndpointChain middle (some far) [es.getLastD [],site++[.fn]] ∧
      ∃stamp fn arg,middle.subterm far.val=some (.app stamp fn arg)

private def OriginalSupply
    {F pre : List Path} {source middle target : LTerm} {degree : Label} {site : Path}
    (event : SelectedOldTurn F source degree pre middle target site) (es : List Path) : Prop :=
  ∃far : ProperPosition middle,
    ∃_low : ExpandedLastSelectedEndpoint middle site (es.getLastD []) false (some far),
      EndpointChain middle (some far) [es.getLastD [],site++[.fn]] ∧
      ∃(oldEdge : Path) (original : LTerm) (oldFrom oldTo : ProperPosition source)
        (sourceEdges targetEdges : List Path),
        BetaNodeHistoryPreimage event.labels (es.getLastD []) oldEdge ∧
        source.subterm oldEdge=some original ∧
        Source source oldEdge (some oldFrom) ∧Target source oldEdge (some oldTo) ∧
        EndpointChain source (some oldFrom) sourceEdges ∧
        EndpointChain source (some oldTo) targetEdges

namespace NonemptyCopy
open BackwardOtherLastFarSourcesChecks.NonemptyCopy
abbrev es : List Path := [[.arg],[.fn],[.fn,.body,.fn]]
def expansion : CreatedReadingExpansion body [] [.arg] [.fn,.body,.fn] false es [false,true,false] := .copyLambda (by decide)
theorem actual_terminal_both : MiddleSupply source [] es ∧OriginalSupply event es :=
  ⟨terminalOrigin.terminal_expanded_last_endpoint_chains event.turn event.redex terminalRead terminalChain expansion,
   event.terminal_expanded_last_original_endpoint_chains terminalOrigin terminalRead terminalChain expansion⟩
end NonemptyCopy

namespace ResultFunctionContext
abbrev I : Term:=WrappedSuccessfulChains.I
abbrev source : LTerm:=initLabels (.app (.app (.lam (.lam (.var 0))) I) I)
abbrev body : LTerm:=.lam (.atom 3) (.var (.atom 4) 0)
abbrev argument : LTerm:=.lam (.atom 5) (.var (.atom 6) 0)
abbrev target : LTerm:=.app (.atom 0) (LTerm.contract (.atom 1) (.atom 2) body argument) (.lam (.atom 7) (.var (.atom 8) 0))
def event : SelectedOldTurn [[.fn]] source (.atom 2) [] source target [.fn] where
  markedBefore := Marked.mark [[.fn]] source.erase
  markedAfter := .app [] (.lam (.var 0)) (.lam (.var 0))
  beforeOld := .nil _
  reduction := .appL (.redRoot _ _ _)
  member := by decide
  labels := .nil _
  turn := .fn (.root _ _ _ _)
  beta := .atom 1
  body := body
  argument := argument
  redex := rfl
def origin : BetaIncomingReadingOrigin body argument [.fn] [.fn] [.fn] [.fn,.fn,.body] [.fn,.fn,.body] [.fn] := .resultLambda rfl rfl rfl
theorem reading : PrerequisiteReadsDirected target [.fn] [.fn] false := ⟨Or.inr ⟨_,_,rfl,rfl⟩,rfl⟩
def terminal : PrerequisiteChain target [.fn] [[.fn]] := .redex_lam (p:=[]) rfl
abbrev es : List Path := [[.fn,.fn,.body],[.fn,.fn],[.fn]]
def expansion : CreatedReadingExpansion body [.fn] [.fn,.fn,.body] [.fn] false es [false,false,false] := .resultLambda
theorem actual_terminal_both : MiddleSupply source [.fn] es ∧OriginalSupply event es :=
  ⟨origin.terminal_expanded_last_endpoint_chains event.turn event.redex reading terminal expansion,
   event.terminal_expanded_last_original_endpoint_chains origin reading terminal expansion⟩
theorem actual_original_init_history : INIT source ∧History [[.fn]] source target ∧Closed source.erase :=
  ⟨init_is_INIT _,.cons event.turn (.nil _),by change ((0<2) ∧(0<1)) ∧(0<1);decide⟩
theorem actual_far_two_edges : ∃far : ProperPosition source,
    Source source [.fn] (some far) ∧far.val=[] ∧EndpointChain source (some far) [[.fn],[.fn,.fn]] := by
  obtain ⟨far,low,chain,_⟩:=actual_terminal_both.1
  have spec : Source source [.fn] (some (⟨[],Or.inl ⟨_,_,_,rfl⟩⟩ : ProperPosition source)) := ⟨.fn,_,_,rfl,rfl,.fn⟩
  have same:=Option.some.inj (Source.unique low.sourceSpec spec)
  exact ⟨far,low.sourceSpec,congrArg Subtype.val same,chain⟩
end ResultFunctionContext

namespace CopyOverlapFunctionContext
abbrev I : Term:=WrappedSuccessfulChains.I
abbrev source : LTerm:=initLabels (.app (.app I I) I)
abbrev body : LTerm:=.var (.atom 3) 0
abbrev argument : LTerm:=.lam (.atom 4) (.var (.atom 5) 0)
abbrev target : LTerm:=.app (.atom 0) (LTerm.contract (.atom 1) (.atom 2) body argument) (.lam (.atom 6) (.var (.atom 7) 0))
def event : SelectedOldTurn [[.fn]] source (.atom 2) [] source target [.fn] where
  markedBefore := Marked.mark [[.fn]] source.erase
  markedAfter := .app [] (.lam (.var 0)) (.lam (.var 0))
  beforeOld := .nil _
  reduction := .appL (.redRoot _ _ _)
  member := by decide
  labels := .nil _
  turn := .fn (.root _ _ _ _)
  beta := .atom 1
  body := body
  argument := argument
  redex := rfl
def origin : BetaIncomingReadingOrigin body argument [.fn] [.fn] [.fn] [.fn,.arg] [.fn,.arg] [.fn,.fn,.body] := .copyLambda (q:=[]) rfl rfl rfl rfl
theorem reading : PrerequisiteReadsDirected target [.fn] [.fn] false := ⟨Or.inr ⟨_,_,rfl,rfl⟩,rfl⟩
def terminal : PrerequisiteChain target [.fn] [[.fn]] := .redex_lam (p:=[]) rfl
abbrev es : List Path := [[.fn,.arg],[.fn,.fn],[.fn,.fn,.body],[.fn,.fn],[.fn]]
def expansion : CreatedReadingExpansion body [.fn] [.fn,.arg] [.fn,.fn,.body] false es [false,true,false,false,false] := .copyOverlap
theorem actual_terminal_both : MiddleSupply source [.fn] es ∧OriginalSupply event es :=
  ⟨origin.terminal_expanded_last_endpoint_chains event.turn event.redex reading terminal expansion,
   event.terminal_expanded_last_original_endpoint_chains origin reading terminal expansion⟩
theorem actual_five_edge_last : es.length=5 ∧es.getLastD []=[.fn] ∧es.getLastD []≠[.fn,.fn,.body] ∧
    CreatedReadingExpansion body [.fn] [.fn,.arg] [.fn,.fn,.body] false es [false,true,false,false,false] :=
  ⟨rfl,rfl,by decide,expansion⟩
theorem actual_original_init_history : INIT source ∧History [[.fn]] source target ∧Closed source.erase :=
  ⟨init_is_INIT _,.cons event.turn (.nil _),by change ((0<1) ∧(0<1)) ∧(0<1);decide⟩
end CopyOverlapFunctionContext

theorem root_external_guard :
    Source BackwardOtherLastTargetsChecks.ResultLambda.source [] none ∧
    (¬∃edges,EndpointChain BackwardOtherLastTargetsChecks.ResultLambda.source none edges) ∧
    NoPrerequisite BackwardOtherLastTargetsChecks.ResultLambda.target [] :=
  ⟨BackwardOtherLastFarSourcesChecks.ExternalException.actual_root_external_far.1,
   BackwardOtherLastFarSourcesChecks.ExternalException.actual_root_external_far.2,
   BackwardOtherLastFarSourcesChecks.ExternalException.actual_no_successful_root_lambda⟩

#print axioms NonemptyCopy.actual_terminal_both
#print axioms ResultFunctionContext.actual_terminal_both
#print axioms ResultFunctionContext.actual_original_init_history
#print axioms ResultFunctionContext.actual_far_two_edges
#print axioms CopyOverlapFunctionContext.actual_terminal_both
#print axioms CopyOverlapFunctionContext.actual_five_edge_last
#print axioms CopyOverlapFunctionContext.actual_original_init_history
#print axioms root_external_guard
end Lamping.Checks.TerminalCreatedReadingFarChainsChecks
