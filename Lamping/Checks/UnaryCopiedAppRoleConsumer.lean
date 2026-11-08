import Lamping.Lamping.FragmentChildStepSeparation
import Lamping.Checks.UnaryArgumentConsumer
set_option maxHeartbeats 4000000
namespace Lamping.Checks.UnaryCopiedAppRoleConsumer.Cro
open AG Graph Lambda Lambda.Labelled FunctionWrappedReachable
abbrev fnEdge := FunctionWrappedConsumer.edge
abbrev argEdge := UnaryArgumentConsumer.Cro.edge
abbrev fnPosition : Path := [.fn,.body,.fn]
abbrev argPosition : Path := [.fn,.body,.arg]

theorem actual_source_role_separation
    (fnFragment : SourceEdgeFragment current croApp.site.net (.inl ()) fnEdge fnPosition)
    (argFragment : SourceEdgeFragment current croApp.site.net (.inl ()) argEdge argPosition) :
    fnFragment.segments≠argFragment.segments := by
  obtain ⟨parent,word,_⟩ := Matches.observation croApp.site.net FunctionWrappedConsumer.source_matches
    (⟨[.fn,.body],rfl⟩ : Position current.erase)
  exact fnFragment.ne_of_child_steps FunctionWrappedConsumer.source_matches argFragment
    FunctionWrappedConsumer.role UnaryArgumentConsumer.Cro.role parent parent
    (by rw [word];rfl) (by rw [word];rfl) (by intro impossible;cases impossible)

theorem actual_target_role_separation
    (fnFragment : SourceEdgeFragment current croApp.site.reduce (.inl ()) fnEdge fnPosition)
    (argFragment : SourceEdgeFragment current croApp.site.reduce (.inl ()) argEdge argPosition) :
    fnFragment.segments≠argFragment.segments := by
  exact fnFragment.ne_of_child_steps actual_final_matches argFragment
    FunctionWrappedConsumer.role UnaryArgumentConsumer.Cro.role FunctionWrappedConsumer.appParent FunctionWrappedConsumer.appParent
    (by change _=accessWord croApp.site.reduce FunctionWrappedConsumer.appParentEdges++[.fn];rw [FunctionWrappedConsumer.appParentWord];rfl)
    (by change _=accessWord croApp.site.reduce FunctionWrappedConsumer.appParentEdges++[.arg];rw [FunctionWrappedConsumer.appParentWord];rfl)
    (by intro impossible;cases impossible)

theorem actual_role_pair
    (sourceFn : SourceEdgeFragment current croApp.site.net (.inl ()) fnEdge fnPosition)
    (sourceArg : SourceEdgeFragment current croApp.site.net (.inl ()) argEdge argPosition)
    (targetFn : SourceEdgeFragment current croApp.site.reduce (.inl ()) fnEdge fnPosition)
    (targetArg : SourceEdgeFragment current croApp.site.reduce (.inl ()) argEdge argPosition) :
    sourceFn.segments≠sourceArg.segments ∧targetFn.segments≠targetArg.segments ∧
      (targetFn.segments=targetArg.segments ↔sourceFn.segments=sourceArg.segments) := by
  have oldDifferent:=actual_source_role_separation sourceFn sourceArg
  have newDifferent:=actual_target_role_separation targetFn targetArg
  exact ⟨oldDifferent,newDifferent,⟨fun same=>(newDifferent same).elim,fun same=>(oldDifferent same).elim⟩⟩

/-- Both children leave the actual copied APP; their terminals remain unrestricted in the generic theorem. -/
theorem actual_reachable_copied_app_role_supply :
    INIT original ∧Closed original.erase ∧History [[.fn]] original current ∧
    GraphTrace (ActualNet.initial term) (ActualNet.ofNet croApp.site.reduce)
      [.beta 0,.croAction .lam 0 1 (by decide),.croAction .cro 0 1 (by decide),.croAction .app 0 1 (by decide)] ∧
    Matches croApp.site.net (.inl ()) current.erase ∧Matches croApp.site.reduce (.inl ()) current.erase ∧
    FunctionWrappedConsumer.appParent.val.getLast?=some (croApp.site.reduce.wire (.inl ⟨.inr (.inl ()),appCtx⟩)) ∧
    Nonempty (SourceEdgeFragment current croApp.site.net (.inl ()) fnEdge fnPosition) ∧
    Nonempty (SourceEdgeFragment current croApp.site.reduce (.inl ()) fnEdge fnPosition) ∧
    Nonempty (SourceEdgeFragment current croApp.site.net (.inl ()) argEdge argPosition) ∧
    Nonempty (SourceEdgeFragment current croApp.site.reduce (.inl ()) argEdge argPosition) ∧
    fnPosition≠argPosition ∧
    PrerequisiteChain current [.fn,.body] [[.fn,.body,.fn],[.fn]] ∧
    PrerequisiteChain current argPosition (argPosition::WrappedSuccessfulChains.bodyEdges) ∧
    ∀ (sourceFn : SourceEdgeFragment current croApp.site.net (.inl ()) fnEdge fnPosition)
      (sourceArg : SourceEdgeFragment current croApp.site.net (.inl ()) argEdge argPosition)
      (targetFn : SourceEdgeFragment current croApp.site.reduce (.inl ()) fnEdge fnPosition)
      (targetArg : SourceEdgeFragment current croApp.site.reduce (.inl ()) argEdge argPosition),
      sourceFn.segments≠sourceArg.segments ∧targetFn.segments≠targetArg.segments ∧
      (targetFn.segments=targetArg.segments ↔sourceFn.segments=sourceArg.segments) := by
  obtain ⟨oldFn,newFn,fnChain⟩ := FunctionWrappedConsumer.actual_fragments_and_successful_chain
  obtain ⟨oldArg,newArg,argChain⟩ := UnaryArgumentConsumer.Cro.actual_fragments_and_chain
  exact ⟨WrappedSuccessfulChains.initial,WrappedSuccessfulChains.sourceClosed,WrappedSuccessfulChains.actualHistory,actual_four_step_trace,
    FunctionWrappedConsumer.source_matches,actual_final_matches,FunctionWrappedConsumer.appParentFinish,
    oldFn,newFn,oldArg,newArg,by decide,fnChain,argChain,actual_role_pair⟩
#print axioms actual_role_pair
#print axioms actual_reachable_copied_app_role_supply
end Lamping.Checks.UnaryCopiedAppRoleConsumer.Cro
namespace Lamping.Checks.UnaryCopiedAppRoleConsumer.Bra
open AG Graph Lambda Lambda.Labelled BraFunctionReachable
abbrev fnEdge := BraFunctionConsumer.edge
abbrev argEdge := UnaryArgumentConsumer.Bra.edge
abbrev fnPosition : Path := [.arg,.body,.fn]
abbrev argPosition : Path := [.arg,.body,.arg]

theorem actual_source_role_separation
    (fnFragment : SourceEdgeFragment current braApp.site.net (.inl ()) fnEdge fnPosition)
    (argFragment : SourceEdgeFragment current braApp.site.net (.inl ()) argEdge argPosition) :
    fnFragment.segments≠argFragment.segments := by
  obtain ⟨parent,word,_⟩ := Matches.observation braApp.site.net BraFunctionConsumer.source_matches
    (⟨[.arg,.body],rfl⟩ : Position current.erase)
  exact fnFragment.ne_of_child_steps BraFunctionConsumer.source_matches argFragment
    BraFunctionConsumer.role UnaryArgumentConsumer.Bra.role parent parent
    (by rw [word];rfl) (by rw [word];rfl) (by intro impossible;cases impossible)

theorem actual_target_role_separation
    (fnFragment : SourceEdgeFragment current braApp.site.reduce (.inl ()) fnEdge fnPosition)
    (argFragment : SourceEdgeFragment current braApp.site.reduce (.inl ()) argEdge argPosition) :
    fnFragment.segments≠argFragment.segments := by
  exact fnFragment.ne_of_child_steps actual_final_matches argFragment
    BraFunctionConsumer.role UnaryArgumentConsumer.Bra.role BraFunctionConsumer.appParent BraFunctionConsumer.appParent
    (by change _=accessWord braApp.site.reduce BraFunctionConsumer.appParentEdges++[.fn];rw [BraFunctionConsumer.appParentWord];rfl)
    (by change _=accessWord braApp.site.reduce BraFunctionConsumer.appParentEdges++[.arg];rw [BraFunctionConsumer.appParentWord];rfl)
    (by intro impossible;cases impossible)

theorem actual_role_pair
    (sourceFn : SourceEdgeFragment current braApp.site.net (.inl ()) fnEdge fnPosition)
    (sourceArg : SourceEdgeFragment current braApp.site.net (.inl ()) argEdge argPosition)
    (targetFn : SourceEdgeFragment current braApp.site.reduce (.inl ()) fnEdge fnPosition)
    (targetArg : SourceEdgeFragment current braApp.site.reduce (.inl ()) argEdge argPosition) :
    sourceFn.segments≠sourceArg.segments ∧targetFn.segments≠targetArg.segments ∧
      (targetFn.segments=targetArg.segments ↔sourceFn.segments=sourceArg.segments) := by
  have oldDifferent:=actual_source_role_separation sourceFn sourceArg
  have newDifferent:=actual_target_role_separation targetFn targetArg
  exact ⟨oldDifferent,newDifferent,⟨fun same=>(newDifferent same).elim,fun same=>(oldDifferent same).elim⟩⟩

/-- Both children leave the actual copied APP; their terminals remain unrestricted in the generic theorem. -/
theorem actual_reachable_copied_app_role_supply :
    INIT original ∧Closed original.erase ∧History [[]] original current ∧
    GraphTrace (ActualNet.initial term) (ActualNet.ofNet braApp.site.reduce)
      [.beta 0,.braAction .lam 0 1 (by decide),.braAction .cro 0 1 (by decide),.braAction .app 0 1 (by decide)] ∧
    Matches braApp.site.net (.inl ()) current.erase ∧Matches braApp.site.reduce (.inl ()) current.erase ∧
    BraFunctionConsumer.appParent.val.getLast?=some (braApp.site.reduce.wire (.inl ⟨.inr (.inl ()),appCtx⟩)) ∧
    Nonempty (SourceEdgeFragment current braApp.site.net (.inl ()) fnEdge fnPosition) ∧
    Nonempty (SourceEdgeFragment current braApp.site.reduce (.inl ()) fnEdge fnPosition) ∧
    Nonempty (SourceEdgeFragment current braApp.site.net (.inl ()) argEdge argPosition) ∧
    Nonempty (SourceEdgeFragment current braApp.site.reduce (.inl ()) argEdge argPosition) ∧
    fnPosition≠argPosition ∧
    PrerequisiteChain current [.arg,.body] [[.arg,.body,.fn],[.arg],[.fn]] ∧
    PrerequisiteChain current argPosition (argPosition::BraSuccessfulChains.bodyEdges) ∧
    ∀ (sourceFn : SourceEdgeFragment current braApp.site.net (.inl ()) fnEdge fnPosition)
      (sourceArg : SourceEdgeFragment current braApp.site.net (.inl ()) argEdge argPosition)
      (targetFn : SourceEdgeFragment current braApp.site.reduce (.inl ()) fnEdge fnPosition)
      (targetArg : SourceEdgeFragment current braApp.site.reduce (.inl ()) argEdge argPosition),
      sourceFn.segments≠sourceArg.segments ∧targetFn.segments≠targetArg.segments ∧
      (targetFn.segments=targetArg.segments ↔sourceFn.segments=sourceArg.segments) := by
  obtain ⟨oldFn,newFn,fnChain⟩ := BraFunctionConsumer.actual_fragments_and_successful_chain
  obtain ⟨oldArg,newArg,argChain⟩ := UnaryArgumentConsumer.Bra.actual_fragments_and_chain
  exact ⟨BraSuccessfulChains.initial,BraSuccessfulChains.sourceClosed,BraSuccessfulChains.actualHistory,actual_four_step_trace,
    BraFunctionConsumer.source_matches,actual_final_matches,BraFunctionConsumer.appParentFinish,
    oldFn,newFn,oldArg,newArg,by decide,fnChain,argChain,actual_role_pair⟩
#print axioms actual_role_pair
#print axioms actual_reachable_copied_app_role_supply
end Lamping.Checks.UnaryCopiedAppRoleConsumer.Bra
