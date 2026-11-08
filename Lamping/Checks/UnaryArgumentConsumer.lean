import Lamping.Lamping.ActionCopiedArgumentComparison
import Lamping.Checks.FunctionWrappedConsumer
import Lamping.Checks.BraFunctionConsumer
set_option maxHeartbeats 4000000
namespace Lamping.Checks.UnaryArgumentConsumer
namespace Cro
open AG Graph Lambda Lambda.Labelled FunctionWrappedReachable
abbrev position : Path := [.fn,.body,.arg]
abbrev argumentTerm : LTerm := .lam (.atom 7) (.var (.atom 8) 0)
abbrev edge := sourceEdge FunctionWrappedConsumer.env (.appArg (.atom 5)) argumentTerm

def occurrence : SourceSubterm [] .external current position FunctionWrappedConsumer.env
    (.appArg (.atom 5)) argumentTerm := .fn (.body (.arg .nil))
theorem role : SourceDeparture FunctionWrappedConsumer.bodyTerm .arg edge.fromPort := .arg

def argument_chain : PrerequisiteChain current position (position::WrappedSuccessfulChains.bodyEdges) :=
  .lam (parent:=[.fn,.body]) (step:=.arg) rfl (by decide) WrappedSuccessfulChains.body_chain

theorem lambda_access_kept (path : RootAccess croApp.site.reduce (.inl ()))
    (typed : accessKind croApp.site.reduce path.val=some .lam) :
    ∃ port : NodePort signature croApp.Kept croApp.kept,
      path.val.getLast?=some (croApp.site.reduce.wire (.inl ⟨.inl port.1,port.2⟩)) := by
  cases last : path.val.getLast? with
  | none => simp only [accessKind,last,Option.bind_none] at typed;cases typed
  | some e =>
    rw [accessKind,last] at typed
    cases arrival : croApp.site.reduce.wire e with
    | inr rest => simp only [Option.bind_some,arrival] at typed;cases typed
    | inl port =>
      rcases port with ⟨node,p⟩
      simp only [Option.bind_some,arrival] at typed
      cases node with
      | inl n =>
        refine ⟨⟨n,p⟩,?_⟩
        rw [←arrival,Pairing.involutive]
      | inr fresh =>
        cases fresh with
        | inl u =>
          cases u
          change portKind (.op .app) p=some .lam at typed
          cases p with
          | inl u => cases u;cases typed
          | inr b => cases b <;> cases typed
        | inr b => cases b <;> cases p <;> cases typed

theorem actual_kept_lambda_finish
    (fragment : SourceEdgeFragment current croApp.site.reduce (.inl ()) edge position) :
    ∃ port : NodePort signature croApp.Kept croApp.kept,
      fragment.access.val.getLast?=some (croApp.site.reduce.wire (.inl ⟨.inl port.1,port.2⟩)) := by
  obtain ⟨observed,word,u,lookup,observes⟩ := Matches.observation croApp.site.reduce actual_final_matches
    (⟨position,rfl⟩ : Position current.erase)
  have sameTerm : u=.lam (.var 0) := Option.some.inj (lookup.symm.trans rfl)
  subst u
  have sameAccess : observed=fragment.access := actual_final_matches.accessWord_injective (word.trans fragment.word.symm)
  have kind : accessKind croApp.site.reduce fragment.access.val=some .lam := by
    rw [←sameAccess];exact observes.1
  exact lambda_access_kept fragment.access kind

theorem actual_argument_pair_equality
    (sourceLeft sourceRight : SourceEdgeFragment current croApp.site.net (.inl ()) edge position)
    (targetLeft targetRight : SourceEdgeFragment current croApp.site.reduce (.inl ()) edge position) :
    targetLeft.segments=targetRight.segments ↔sourceLeft.segments=sourceRight.segments := by
  obtain ⟨flow,_,_,_,_⟩ := cro_certified
  obtain ⟨principal⟩ := croApp.site.actionPrincipal_exists
  obtain ⟨oldParent,oldWord,_⟩ := Matches.observation croApp.site.net FunctionWrappedConsumer.source_matches
    (⟨[.fn,.body],rfl⟩ : Position current.erase)
  have targetWord : position=accessWord croApp.site.reduce FunctionWrappedConsumer.appParent.val++[.arg] := by
    change _=accessWord croApp.site.reduce FunctionWrappedConsumer.appParentEdges++[.arg]
    rw [FunctionWrappedConsumer.appParentWord];rfl
  have sourceWord : position=accessWord croApp.site.net oldParent.val++[.arg] := by rw [oldWord];rfl
  obtain ⟨leftEnd,leftFinish⟩ := actual_kept_lambda_finish targetLeft
  obtain ⟨rightEnd,rightFinish⟩ := actual_kept_lambda_finish targetRight
  exact sourceLeft.cro_copied_argument_kept_equality croApp.site (croApp.sourceIso.flowBalance flow)
    (.inl ()) rfl FunctionWrappedConsumer.source_matches actual_final_matches principal
    targetLeft sourceRight targetRight role role oldParent oldParent FunctionWrappedConsumer.appParent FunctionWrappedConsumer.appParent
    sourceWord sourceWord targetWord targetWord FunctionWrappedConsumer.appParentFinish FunctionWrappedConsumer.appParentFinish
    leftEnd.1 rightEnd.1 leftEnd.2 rightEnd.2 leftFinish rightFinish

theorem actual_fragments_and_chain :
    Nonempty (SourceEdgeFragment current croApp.site.net (.inl ()) edge position) ∧
    Nonempty (SourceEdgeFragment current croApp.site.reduce (.inl ()) edge position) ∧
    PrerequisiteChain current position (position::WrappedSuccessfulChains.bodyEdges) :=
  ⟨FunctionWrappedConsumer.source_matches.base_source_edge_fragment WrappedSuccessfulChains.targetClosed occurrence,
    actual_final_matches.base_source_edge_fragment WrappedSuccessfulChains.targetClosed occurrence,argument_chain⟩

/-- This ARG edge is the incoming edge of an actual lambda, and hence is a
real successful lambda-context reading. The closed carrier and global
labelled history are reused, with no reinitialization or source Joint. -/
theorem actual_reachable_argument_comparison :
    INIT original ∧Closed original.erase ∧History [[.fn]] original current ∧
    GraphTrace (ActualNet.initial term) (ActualNet.ofNet croApp.site.reduce)
      [.beta 0,.croAction .lam 0 1 (by decide),.croAction .cro 0 1 (by decide),.croAction .app 0 1 (by decide)] ∧
    Matches croApp.site.net (.inl ()) current.erase ∧Matches croApp.site.reduce (.inl ()) current.erase ∧
    Nonempty (SourceEdgeFragment current croApp.site.net (.inl ()) edge position) ∧
    Nonempty (SourceEdgeFragment current croApp.site.reduce (.inl ()) edge position) ∧
    PrerequisiteChain current position (position::WrappedSuccessfulChains.bodyEdges) ∧
    ∀ (sourceLeft sourceRight : SourceEdgeFragment current croApp.site.net (.inl ()) edge position)
      (targetLeft targetRight : SourceEdgeFragment current croApp.site.reduce (.inl ()) edge position),
      targetLeft.segments=targetRight.segments ↔sourceLeft.segments=sourceRight.segments := by
  obtain ⟨sourceExists,targetExists,chain⟩ := actual_fragments_and_chain
  exact ⟨WrappedSuccessfulChains.initial,WrappedSuccessfulChains.sourceClosed,WrappedSuccessfulChains.actualHistory,actual_four_step_trace,
    FunctionWrappedConsumer.source_matches,actual_final_matches,sourceExists,targetExists,chain,actual_argument_pair_equality⟩
#print axioms argument_chain
#print axioms actual_kept_lambda_finish
#print axioms actual_argument_pair_equality
#print axioms actual_reachable_argument_comparison
end Cro
namespace Bra
open AG Graph Lambda Lambda.Labelled BraFunctionReachable
abbrev position : Path := [.arg,.body,.arg]
abbrev argumentTerm : LTerm := .lam (.atom 9) (.var (.atom 10) 0)
abbrev edge := sourceEdge BraFunctionConsumer.env (.appArg (.atom 7)) argumentTerm

def occurrence : SourceSubterm [] .external current position BraFunctionConsumer.env
    (.appArg (.atom 7)) argumentTerm := .arg (.body (.arg .nil))
theorem role : SourceDeparture BraFunctionConsumer.bodyTerm .arg edge.fromPort := .arg

def argument_chain : PrerequisiteChain current position (position::BraSuccessfulChains.bodyEdges) :=
  .lam (parent:=[.arg,.body]) (step:=.arg) rfl (by decide) BraSuccessfulChains.body_chain

theorem lambda_access_kept (path : RootAccess braApp.site.reduce (.inl ()))
    (typed : accessKind braApp.site.reduce path.val=some .lam) :
    ∃ port : NodePort signature braApp.Kept braApp.kept,
      path.val.getLast?=some (braApp.site.reduce.wire (.inl ⟨.inl port.1,port.2⟩)) := by
  cases last : path.val.getLast? with
  | none => simp only [accessKind,last,Option.bind_none] at typed;cases typed
  | some e =>
    rw [accessKind,last] at typed
    cases arrival : braApp.site.reduce.wire e with
    | inr rest => simp only [Option.bind_some,arrival] at typed;cases typed
    | inl port =>
      rcases port with ⟨node,p⟩
      simp only [Option.bind_some,arrival] at typed
      cases node with
      | inl n =>
        refine ⟨⟨n,p⟩,?_⟩
        rw [←arrival,Pairing.involutive]
      | inr fresh =>
        cases fresh with
        | inl u =>
          cases u
          change portKind (.op .app) p=some .lam at typed
          cases p with
          | inl u => cases u;cases typed
          | inr b => cases b <;> cases typed
        | inr b => cases b <;> cases p <;> cases typed

theorem actual_kept_lambda_finish
    (fragment : SourceEdgeFragment current braApp.site.reduce (.inl ()) edge position) :
    ∃ port : NodePort signature braApp.Kept braApp.kept,
      fragment.access.val.getLast?=some (braApp.site.reduce.wire (.inl ⟨.inl port.1,port.2⟩)) := by
  obtain ⟨observed,word,u,lookup,observes⟩ := Matches.observation braApp.site.reduce actual_final_matches
    (⟨position,rfl⟩ : Position current.erase)
  have sameTerm : u=.lam (.var 0) := Option.some.inj (lookup.symm.trans rfl)
  subst u
  have sameAccess : observed=fragment.access := actual_final_matches.accessWord_injective (word.trans fragment.word.symm)
  have kind : accessKind braApp.site.reduce fragment.access.val=some .lam := by
    rw [←sameAccess];exact observes.1
  exact lambda_access_kept fragment.access kind

theorem actual_argument_pair_equality
    (sourceLeft sourceRight : SourceEdgeFragment current braApp.site.net (.inl ()) edge position)
    (targetLeft targetRight : SourceEdgeFragment current braApp.site.reduce (.inl ()) edge position) :
    targetLeft.segments=targetRight.segments ↔sourceLeft.segments=sourceRight.segments := by
  obtain ⟨flow,_,_,_,_⟩ := cro_certified
  obtain ⟨principal⟩ := braApp.site.actionPrincipal_exists
  obtain ⟨oldParent,oldWord,_⟩ := Matches.observation braApp.site.net BraFunctionConsumer.source_matches
    (⟨[.arg,.body],rfl⟩ : Position current.erase)
  have targetWord : position=accessWord braApp.site.reduce BraFunctionConsumer.appParent.val++[.arg] := by
    change _=accessWord braApp.site.reduce BraFunctionConsumer.appParentEdges++[.arg]
    rw [BraFunctionConsumer.appParentWord];rfl
  have sourceWord : position=accessWord braApp.site.net oldParent.val++[.arg] := by rw [oldWord];rfl
  obtain ⟨leftEnd,leftFinish⟩ := actual_kept_lambda_finish targetLeft
  obtain ⟨rightEnd,rightFinish⟩ := actual_kept_lambda_finish targetRight
  exact sourceLeft.bra_copied_argument_kept_equality braApp.site (braApp.sourceIso.flowBalance flow)
    (.inl ()) rfl BraFunctionConsumer.source_matches actual_final_matches principal
    targetLeft sourceRight targetRight role role oldParent oldParent BraFunctionConsumer.appParent BraFunctionConsumer.appParent
    sourceWord sourceWord targetWord targetWord BraFunctionConsumer.appParentFinish BraFunctionConsumer.appParentFinish
    leftEnd.1 rightEnd.1 leftEnd.2 rightEnd.2 leftFinish rightFinish

theorem actual_fragments_and_chain :
    Nonempty (SourceEdgeFragment current braApp.site.net (.inl ()) edge position) ∧
    Nonempty (SourceEdgeFragment current braApp.site.reduce (.inl ()) edge position) ∧
    PrerequisiteChain current position (position::BraSuccessfulChains.bodyEdges) :=
  ⟨BraFunctionConsumer.source_matches.base_source_edge_fragment BraSuccessfulChains.targetClosed occurrence,
    actual_final_matches.base_source_edge_fragment BraSuccessfulChains.targetClosed occurrence,argument_chain⟩

/-- This ARG edge is the incoming edge of an actual lambda, and hence is a
real successful lambda-context reading. The closed carrier and global
labelled history are reused, with no reinitialization or source Joint. -/
theorem actual_reachable_argument_comparison :
    INIT original ∧Closed original.erase ∧History [[]] original current ∧
    GraphTrace (ActualNet.initial term) (ActualNet.ofNet braApp.site.reduce)
      [.beta 0,.braAction .lam 0 1 (by decide),.braAction .cro 0 1 (by decide),.braAction .app 0 1 (by decide)] ∧
    Matches braApp.site.net (.inl ()) current.erase ∧Matches braApp.site.reduce (.inl ()) current.erase ∧
    Nonempty (SourceEdgeFragment current braApp.site.net (.inl ()) edge position) ∧
    Nonempty (SourceEdgeFragment current braApp.site.reduce (.inl ()) edge position) ∧
    PrerequisiteChain current position (position::BraSuccessfulChains.bodyEdges) ∧
    ∀ (sourceLeft sourceRight : SourceEdgeFragment current braApp.site.net (.inl ()) edge position)
      (targetLeft targetRight : SourceEdgeFragment current braApp.site.reduce (.inl ()) edge position),
      targetLeft.segments=targetRight.segments ↔sourceLeft.segments=sourceRight.segments := by
  obtain ⟨sourceExists,targetExists,chain⟩ := actual_fragments_and_chain
  exact ⟨BraSuccessfulChains.initial,BraSuccessfulChains.sourceClosed,BraSuccessfulChains.actualHistory,actual_four_step_trace,
    BraFunctionConsumer.source_matches,actual_final_matches,sourceExists,targetExists,chain,actual_argument_pair_equality⟩
#print axioms argument_chain
#print axioms actual_kept_lambda_finish
#print axioms actual_argument_pair_equality
#print axioms actual_reachable_argument_comparison
end Bra
end Lamping.Checks.UnaryArgumentConsumer
