import Lamping.Checks.UnaryBindingReachable
import Lamping.Lamping.KeptParentCopiedBindingComparison
namespace Lamping.Checks.UnaryBindingConsumer
end Lamping.Checks.UnaryBindingConsumer

namespace Lamping.Checks.UnaryBindingConsumer.Cro
open AG Graph Lambda Lambda.Labelled FunctionWrappedReachable
open UnaryBindingReachable.Cro

theorem app_access_kept (path : RootAccess croLambda.site.reduce (.inl ()))
    (typed : accessKind croLambda.site.reduce path.val=some .app) :
    ∃ port : NodePort signature croLambda.Kept croLambda.kept,
      path.val.getLast?=some (croLambda.site.reduce.wire (.inl ⟨.inl port.1,port.2⟩)) := by
  cases last : path.val.getLast? with
  | none => simp only [accessKind,last,Option.bind_none] at typed;cases typed
  | some e =>
    rw [accessKind,last] at typed
    cases arrival : croLambda.site.reduce.wire e with
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
          cases p with
          | inl u => cases u;cases typed
          | inr b => cases b <;> cases typed
        | inr b =>
          cases b <;> cases p <;> cases typed

theorem actual_kept_app_parent :
    ∃ (parent : RootAccess croLambda.site.reduce (.inl ()))
      (port : NodePort signature croLambda.Kept croLambda.kept),
      accessWord croLambda.site.reduce parent.val=[.fn,.body] ∧
      parent.val.getLast?=some (croLambda.site.reduce.wire (.inl ⟨.inl port.1,port.2⟩)) := by
  let position : Position current.erase := ⟨[.fn,.body],rfl⟩
  obtain ⟨parent,word,u,lookup,observes⟩ := Matches.observation croLambda.site.reduce target_matches position
  have same : u=.app (.var 0) (.lam (.var 0)) := Option.some.inj (lookup.symm.trans rfl)
  subst u
  obtain ⟨port,finish⟩ := app_access_kept parent observes.1
  exact ⟨parent,port,word,finish⟩
#print axioms app_access_kept
#print axioms actual_kept_app_parent

abbrev bodyTerm : LTerm := .app (.atom 5) (.var (.atom 6) 0) (.lam (.atom 7) (.var (.atom 8) 0))
abbrev leafTerm : LTerm := .var (.atom 6) 0
abbrev env : List Label := [WrappedSuccessfulChains.functionLabel]
abbrev edge := sourceEdge env (.appFn (.atom 5)) leafTerm

def occurrence : SourceSubterm [] .external current [.fn,.body,.fn] env (.appFn (.atom 5)) leafTerm :=
  .fn (.body (.fn .nil))

theorem role : SourceDeparture bodyTerm .fn edge.fromPort := .fn

theorem actual_fragments_and_successful_chain :
    Nonempty (SourceEdgeFragment current croLambda.site.net (.inl ()) edge [.fn,.body,.fn]) ∧
    Nonempty (SourceEdgeFragment current croLambda.site.reduce (.inl ()) edge [.fn,.body,.fn]) ∧
    PrerequisiteChain current WrappedSuccessfulChains.bodyApp WrappedSuccessfulChains.bodyEdges :=
  ⟨source_matches.base_source_edge_fragment WrappedSuccessfulChains.targetClosed occurrence,
    target_matches.base_source_edge_fragment WrappedSuccessfulChains.targetClosed occurrence,WrappedSuccessfulChains.body_chain⟩

theorem actual_two_rule_trace : GraphTrace (ActualNet.initial term)
    (ActualNet.ofNet croLambda.site.reduce) [.beta 0,.croAction .lam 0 1 (by decide)] :=
  .cons concrete.graph_step (.cons croLambda.graph_step (.refl _))
#print axioms actual_fragments_and_successful_chain
#print axioms actual_two_rule_trace

theorem actual_piece_pair_equality
    (sourceLeft sourceRight : SourceEdgeFragment current croLambda.site.net (.inl ()) edge [.fn,.body,.fn])
    (targetLeft targetRight : SourceEdgeFragment current croLambda.site.reduce (.inl ()) edge [.fn,.body,.fn]) :
    targetLeft.segments=targetRight.segments ↔sourceLeft.segments=sourceRight.segments := by
  obtain ⟨flow,_,_,_,_⟩ := beta_certified
  obtain ⟨principal⟩ := croLambda.site.actionPrincipal_exists
  let parentPosition : Position current.erase := ⟨[.fn,.body],rfl⟩
  obtain ⟨oldParent,oldWord,_⟩ := Matches.observation croLambda.site.net source_matches parentPosition
  obtain ⟨newParent,port,newWord,parentAt⟩ := actual_kept_app_parent
  have sourceWord : [.fn,.body,.fn]=accessWord croLambda.site.net oldParent.val++[.fn] := by
    rw [oldWord];rfl
  have targetWord : [.fn,.body,.fn]=accessWord croLambda.site.reduce newParent.val++[.fn] := by
    rw [newWord];rfl
  have leftEnd := actual_variable_finish targetLeft.access targetLeft.word
  have rightEnd := actual_variable_finish targetRight.access targetRight.word
  exact sourceLeft.cro_kept_parent_copied_binding_equality croLambda.site
    (croLambda.sourceIso.flowBalance flow) (.inl ()) rfl source_matches target_matches principal
    targetLeft sourceRight targetRight role role oldParent oldParent newParent newParent
    sourceWord sourceWord targetWord targetWord port port parentAt parentAt leftEnd rightEnd

/-- A real earlier-stage successful FUNCTION instance supplies every premise;
comparison is between arbitrary choices at the same occurrence. -/
theorem actual_reachable_kept_parent_copied_binding :
    INIT original ∧Closed original.erase ∧History [[.fn]] original current ∧
    GraphTrace (ActualNet.initial term) (ActualNet.ofNet croLambda.site.reduce)
      [.beta 0,.croAction .lam 0 1 (by decide)] ∧
    Matches croLambda.site.net (.inl ()) current.erase ∧
    Matches croLambda.site.reduce (.inl ()) current.erase ∧
    Nonempty (SourceEdgeFragment current croLambda.site.net (.inl ()) edge [.fn,.body,.fn]) ∧
    Nonempty (SourceEdgeFragment current croLambda.site.reduce (.inl ()) edge [.fn,.body,.fn]) ∧
    PrerequisiteChain current WrappedSuccessfulChains.bodyApp WrappedSuccessfulChains.bodyEdges ∧
    ∀ (sourceLeft sourceRight : SourceEdgeFragment current croLambda.site.net (.inl ()) edge [.fn,.body,.fn])
      (targetLeft targetRight : SourceEdgeFragment current croLambda.site.reduce (.inl ()) edge [.fn,.body,.fn]),
      targetLeft.segments=targetRight.segments ↔sourceLeft.segments=sourceRight.segments := by
  obtain ⟨sourceExists,targetExists,chain⟩ := actual_fragments_and_successful_chain
  exact ⟨WrappedSuccessfulChains.initial,WrappedSuccessfulChains.sourceClosed,WrappedSuccessfulChains.actualHistory,
    actual_two_rule_trace,source_matches,target_matches,sourceExists,targetExists,chain,actual_piece_pair_equality⟩
#print axioms actual_piece_pair_equality
#print axioms actual_reachable_kept_parent_copied_binding
end Lamping.Checks.UnaryBindingConsumer.Cro

namespace Lamping.Checks.UnaryBindingConsumer.Bra
open AG Graph Lambda Lambda.Labelled BraFunctionReachable
open UnaryBindingReachable.Bra

theorem app_access_kept (path : RootAccess braLambda.site.reduce (.inl ()))
    (typed : accessKind braLambda.site.reduce path.val=some .app) :
    ∃ port : NodePort signature braLambda.Kept braLambda.kept,
      path.val.getLast?=some (braLambda.site.reduce.wire (.inl ⟨.inl port.1,port.2⟩)) := by
  cases last : path.val.getLast? with
  | none => simp only [accessKind,last,Option.bind_none] at typed;cases typed
  | some e =>
    rw [accessKind,last] at typed
    cases arrival : braLambda.site.reduce.wire e with
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
          cases p with
          | inl u => cases u;cases typed
          | inr b => cases b <;> cases typed
        | inr b =>
          cases b <;> cases p <;> cases typed

theorem actual_kept_app_parent :
    ∃ (parent : RootAccess braLambda.site.reduce (.inl ()))
      (port : NodePort signature braLambda.Kept braLambda.kept),
      accessWord braLambda.site.reduce parent.val=[.arg,.body] ∧
      parent.val.getLast?=some (braLambda.site.reduce.wire (.inl ⟨.inl port.1,port.2⟩)) := by
  let position : Position current.erase := ⟨[.arg,.body],rfl⟩
  obtain ⟨parent,word,u,lookup,observes⟩ := Matches.observation braLambda.site.reduce target_matches position
  have same : u=.app (.var 0) (.lam (.var 0)) := Option.some.inj (lookup.symm.trans rfl)
  subst u
  obtain ⟨port,finish⟩ := app_access_kept parent observes.1
  exact ⟨parent,port,word,finish⟩
#print axioms app_access_kept
#print axioms actual_kept_app_parent

abbrev bodyTerm : LTerm := .app (.atom 7) (.var (.atom 8) 0) (.lam (.atom 9) (.var (.atom 10) 0))
abbrev leafTerm : LTerm := .var (.atom 8) 0
abbrev env : List Label := [BraSuccessfulChains.argumentLabel]
abbrev edge := sourceEdge env (.appFn (.atom 7)) leafTerm

def occurrence : SourceSubterm [] .external current [.arg,.body,.fn] env (.appFn (.atom 7)) leafTerm :=
  .arg (.body (.fn .nil))

theorem role : SourceDeparture bodyTerm .fn edge.fromPort := .fn

theorem actual_fragments_and_successful_chain :
    Nonempty (SourceEdgeFragment current braLambda.site.net (.inl ()) edge [.arg,.body,.fn]) ∧
    Nonempty (SourceEdgeFragment current braLambda.site.reduce (.inl ()) edge [.arg,.body,.fn]) ∧
    PrerequisiteChain current BraSuccessfulChains.bodyApp BraSuccessfulChains.bodyEdges :=
  ⟨source_matches.base_source_edge_fragment BraSuccessfulChains.targetClosed occurrence,
    target_matches.base_source_edge_fragment BraSuccessfulChains.targetClosed occurrence,BraSuccessfulChains.body_chain⟩

theorem actual_two_rule_trace : GraphTrace (ActualNet.initial term)
    (ActualNet.ofNet braLambda.site.reduce) [.beta 0,.braAction .lam 0 1 (by decide)] :=
  .cons concrete.graph_step (.cons braLambda.graph_step (.refl _))
#print axioms actual_fragments_and_successful_chain
#print axioms actual_two_rule_trace

theorem actual_piece_pair_equality
    (sourceLeft sourceRight : SourceEdgeFragment current braLambda.site.net (.inl ()) edge [.arg,.body,.fn])
    (targetLeft targetRight : SourceEdgeFragment current braLambda.site.reduce (.inl ()) edge [.arg,.body,.fn]) :
    targetLeft.segments=targetRight.segments ↔sourceLeft.segments=sourceRight.segments := by
  obtain ⟨flow,_,_,_,_⟩ := beta_certified
  obtain ⟨principal⟩ := braLambda.site.actionPrincipal_exists
  let parentPosition : Position current.erase := ⟨[.arg,.body],rfl⟩
  obtain ⟨oldParent,oldWord,_⟩ := Matches.observation braLambda.site.net source_matches parentPosition
  obtain ⟨newParent,port,newWord,parentAt⟩ := actual_kept_app_parent
  have sourceWord : [.arg,.body,.fn]=accessWord braLambda.site.net oldParent.val++[.fn] := by
    rw [oldWord];rfl
  have targetWord : [.arg,.body,.fn]=accessWord braLambda.site.reduce newParent.val++[.fn] := by
    rw [newWord];rfl
  have leftEnd := actual_variable_finish targetLeft.access targetLeft.word
  have rightEnd := actual_variable_finish targetRight.access targetRight.word
  exact sourceLeft.bra_kept_parent_copied_binding_equality braLambda.site
    (braLambda.sourceIso.flowBalance flow) (.inl ()) rfl source_matches target_matches principal
    targetLeft sourceRight targetRight role role oldParent oldParent newParent newParent
    sourceWord sourceWord targetWord targetWord port port parentAt parentAt leftEnd rightEnd

/-- A real earlier-stage successful FUNCTION instance supplies every premise;
comparison is between arbitrary choices at the same occurrence. -/
theorem actual_reachable_kept_parent_copied_binding :
    INIT original ∧Closed original.erase ∧History [[]] original current ∧
    GraphTrace (ActualNet.initial term) (ActualNet.ofNet braLambda.site.reduce)
      [.beta 0,.braAction .lam 0 1 (by decide)] ∧
    Matches braLambda.site.net (.inl ()) current.erase ∧
    Matches braLambda.site.reduce (.inl ()) current.erase ∧
    Nonempty (SourceEdgeFragment current braLambda.site.net (.inl ()) edge [.arg,.body,.fn]) ∧
    Nonempty (SourceEdgeFragment current braLambda.site.reduce (.inl ()) edge [.arg,.body,.fn]) ∧
    PrerequisiteChain current BraSuccessfulChains.bodyApp BraSuccessfulChains.bodyEdges ∧
    ∀ (sourceLeft sourceRight : SourceEdgeFragment current braLambda.site.net (.inl ()) edge [.arg,.body,.fn])
      (targetLeft targetRight : SourceEdgeFragment current braLambda.site.reduce (.inl ()) edge [.arg,.body,.fn]),
      targetLeft.segments=targetRight.segments ↔sourceLeft.segments=sourceRight.segments := by
  obtain ⟨sourceExists,targetExists,chain⟩ := actual_fragments_and_successful_chain
  exact ⟨BraSuccessfulChains.initial,BraSuccessfulChains.sourceClosed,BraSuccessfulChains.actualHistory,
    actual_two_rule_trace,source_matches,target_matches,sourceExists,targetExists,chain,actual_piece_pair_equality⟩
#print axioms actual_piece_pair_equality
#print axioms actual_reachable_kept_parent_copied_binding
end Lamping.Checks.UnaryBindingConsumer.Bra

#print axioms Lamping.AG.SourceEdgeFragment.cro_kept_parent_copied_binding_cut
#print axioms Lamping.AG.SourceEdgeFragment.bra_kept_parent_copied_binding_cut
#print axioms Lamping.AG.SourceEdgeFragment.cro_kept_parent_copied_binding_equality
#print axioms Lamping.AG.SourceEdgeFragment.bra_kept_parent_copied_binding_equality
