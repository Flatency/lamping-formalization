import Lamping.Checks.UnaryBindingReachable
import Lamping.Checks.UnaryBindingConsumer
import Lamping.Lamping.KeptParentCopiedLambdaComparison

namespace Lamping.Checks.UnaryLambdaContextConsumer.Cro
open AG Graph Lambda Lambda.Labelled FunctionWrappedReachable
open UnaryBindingReachable.Cro

abbrev lambdaTerm : LTerm := match current with
  | .app _ fn _ => fn
  | term => term
abbrev edge := sourceEdge [] (.appFn current.label) lambdaTerm

def occurrence : SourceSubterm [] .external current [.fn] [] (.appFn current.label) lambdaTerm :=
  .fn .nil

theorem role : SourceDeparture current .fn edge.fromPort := .fn

def actual_chain : PrerequisiteChain current [.fn] [[.fn]] :=
  .redex_lam (p:=[]) rfl

theorem actual_context_finish
    (fragment : SourceEdgeFragment current croLambda.site.reduce (.inl ()) edge [.fn]) :
    fragment.access.val.getLast?=some (croLambda.site.reduce.wire (.inl ⟨.inr (.inl ()),.inl ()⟩)) := by
  have same : fragment.access=lambdaParent := target_matches.accessWord_injective
    (fragment.word.trans lambdaWord.symm)
  exact (congrArg (fun path : RootAccess croLambda.site.reduce (.inl ())=>path.val.getLast?) same).trans lambdaFinish

theorem actual_kept_root_parent :
    ∃ (parent : RootAccess croLambda.site.reduce (.inl ()))
      (port : NodePort signature croLambda.Kept croLambda.kept),
      accessWord croLambda.site.reduce parent.val=[] ∧
      parent.val.getLast?=some (croLambda.site.reduce.wire (.inl ⟨.inl port.1,port.2⟩)) := by
  let position : Position current.erase := ⟨[],rfl⟩
  obtain ⟨parent,word,u,lookup,observes⟩ := Matches.observation croLambda.site.reduce target_matches position
  have same : u=current.erase := Option.some.inj lookup.symm
  subst u
  obtain ⟨port,finish⟩ := UnaryBindingConsumer.Cro.app_access_kept parent observes.1
  exact ⟨parent,port,word,finish⟩

theorem actual_fragments_and_chain :
    Nonempty (SourceEdgeFragment current croLambda.site.net (.inl ()) edge [.fn]) ∧
    Nonempty (SourceEdgeFragment current croLambda.site.reduce (.inl ()) edge [.fn]) ∧
    PrerequisiteChain current [.fn] [[.fn]] :=
  ⟨source_matches.base_source_edge_fragment WrappedSuccessfulChains.targetClosed occurrence,
    target_matches.base_source_edge_fragment WrappedSuccessfulChains.targetClosed occurrence,actual_chain⟩

theorem actual_two_rule_trace : GraphTrace (ActualNet.initial term)
    (ActualNet.ofNet croLambda.site.reduce) [.beta 0,.croAction .lam 0 1 (by decide)] :=
  UnaryBindingConsumer.Cro.actual_two_rule_trace
#print axioms actual_chain
#print axioms actual_context_finish
#print axioms actual_kept_root_parent
#print axioms actual_fragments_and_chain
#print axioms actual_two_rule_trace

theorem actual_piece_pair_equality
    (sourceLeft sourceRight : SourceEdgeFragment current croLambda.site.net (.inl ()) edge [.fn])
    (targetLeft targetRight : SourceEdgeFragment current croLambda.site.reduce (.inl ()) edge [.fn]) :
    targetLeft.segments=targetRight.segments ↔sourceLeft.segments=sourceRight.segments := by
  obtain ⟨flow,_,_,_,_⟩ := beta_certified
  obtain ⟨principal⟩ := croLambda.site.actionPrincipal_exists
  let position : Position current.erase := ⟨[],rfl⟩
  obtain ⟨oldParent,oldWord,_⟩ := Matches.observation croLambda.site.net source_matches position
  obtain ⟨newParent,port,newWord,parentAt⟩ := actual_kept_root_parent
  have sourceWord : [.fn]=accessWord croLambda.site.net oldParent.val++[.fn] := by
    rw [oldWord];rfl
  have targetWord : [.fn]=accessWord croLambda.site.reduce newParent.val++[.fn] := by
    rw [newWord];rfl
  exact sourceLeft.cro_kept_parent_copied_lambda_equality croLambda.site
    (croLambda.sourceIso.flowBalance flow) (.inl ()) rfl source_matches target_matches principal
    targetLeft sourceRight targetRight role role oldParent oldParent newParent newParent
    sourceWord sourceWord targetWord targetWord port port parentAt parentAt
    (actual_context_finish targetLeft) (actual_context_finish targetRight)

/-- Real same-INIT/current data for this CONTEXT-terminal subclass.
The cro slot is FUNCTION; the bra slot is ARGUMENT, read backwards from lambda. -/
theorem actual_reachable_kept_parent_copied_lambda_context :
    INIT original ∧Closed original.erase ∧History [[.fn]] original current ∧
    GraphTrace (ActualNet.initial term) (ActualNet.ofNet croLambda.site.reduce)
      [.beta 0,.croAction .lam 0 1 (by decide)] ∧
    Matches croLambda.site.net (.inl ()) current.erase ∧
    Matches croLambda.site.reduce (.inl ()) current.erase ∧
    Nonempty (SourceEdgeFragment current croLambda.site.net (.inl ()) edge [.fn]) ∧
    Nonempty (SourceEdgeFragment current croLambda.site.reduce (.inl ()) edge [.fn]) ∧
    PrerequisiteChain current [.fn] [[.fn]] ∧
    ∀ (sourceLeft sourceRight : SourceEdgeFragment current croLambda.site.net (.inl ()) edge [.fn])
      (targetLeft targetRight : SourceEdgeFragment current croLambda.site.reduce (.inl ()) edge [.fn]),
      targetLeft.segments=targetRight.segments ↔sourceLeft.segments=sourceRight.segments := by
  obtain ⟨sourceExists,targetExists,chain⟩ := actual_fragments_and_chain
  exact ⟨WrappedSuccessfulChains.initial,WrappedSuccessfulChains.sourceClosed,WrappedSuccessfulChains.actualHistory,
    actual_two_rule_trace,source_matches,target_matches,sourceExists,targetExists,chain,actual_piece_pair_equality⟩
#print axioms actual_piece_pair_equality
#print axioms actual_reachable_kept_parent_copied_lambda_context
end Lamping.Checks.UnaryLambdaContextConsumer.Cro

namespace Lamping.Checks.UnaryLambdaContextConsumer.Bra
open AG Graph Lambda Lambda.Labelled BraFunctionReachable
open UnaryBindingReachable.Bra

abbrev lambdaTerm : LTerm := match current with
  | .app _ _ arg => arg
  | term => term
abbrev edge := sourceEdge [] (.appArg current.label) lambdaTerm

def occurrence : SourceSubterm [] .external current [.arg] [] (.appArg current.label) lambdaTerm :=
  .arg .nil

theorem role : SourceDeparture current .arg edge.fromPort := .arg

def actual_chain : PrerequisiteChain current [.arg] [[.arg],[.fn]] :=
  .lam (parent:=[]) (step:=.arg) rfl (by decide) (.redex_app rfl)

theorem actual_context_finish
    (fragment : SourceEdgeFragment current braLambda.site.reduce (.inl ()) edge [.arg]) :
    fragment.access.val.getLast?=some (braLambda.site.reduce.wire (.inl ⟨.inr (.inl ()),.inl ()⟩)) := by
  have same : fragment.access=lambdaParent := target_matches.accessWord_injective
    (fragment.word.trans lambdaWord.symm)
  exact (congrArg (fun path : RootAccess braLambda.site.reduce (.inl ())=>path.val.getLast?) same).trans lambdaFinish

theorem actual_kept_root_parent :
    ∃ (parent : RootAccess braLambda.site.reduce (.inl ()))
      (port : NodePort signature braLambda.Kept braLambda.kept),
      accessWord braLambda.site.reduce parent.val=[] ∧
      parent.val.getLast?=some (braLambda.site.reduce.wire (.inl ⟨.inl port.1,port.2⟩)) := by
  let position : Position current.erase := ⟨[],rfl⟩
  obtain ⟨parent,word,u,lookup,observes⟩ := Matches.observation braLambda.site.reduce target_matches position
  have same : u=current.erase := Option.some.inj lookup.symm
  subst u
  obtain ⟨port,finish⟩ := UnaryBindingConsumer.Bra.app_access_kept parent observes.1
  exact ⟨parent,port,word,finish⟩

theorem actual_fragments_and_chain :
    Nonempty (SourceEdgeFragment current braLambda.site.net (.inl ()) edge [.arg]) ∧
    Nonempty (SourceEdgeFragment current braLambda.site.reduce (.inl ()) edge [.arg]) ∧
    PrerequisiteChain current [.arg] [[.arg],[.fn]] :=
  ⟨source_matches.base_source_edge_fragment BraSuccessfulChains.targetClosed occurrence,
    target_matches.base_source_edge_fragment BraSuccessfulChains.targetClosed occurrence,actual_chain⟩

theorem actual_two_rule_trace : GraphTrace (ActualNet.initial term)
    (ActualNet.ofNet braLambda.site.reduce) [.beta 0,.braAction .lam 0 1 (by decide)] :=
  UnaryBindingConsumer.Bra.actual_two_rule_trace
#print axioms actual_chain
#print axioms actual_context_finish
#print axioms actual_kept_root_parent
#print axioms actual_fragments_and_chain
#print axioms actual_two_rule_trace

theorem actual_piece_pair_equality
    (sourceLeft sourceRight : SourceEdgeFragment current braLambda.site.net (.inl ()) edge [.arg])
    (targetLeft targetRight : SourceEdgeFragment current braLambda.site.reduce (.inl ()) edge [.arg]) :
    targetLeft.segments=targetRight.segments ↔sourceLeft.segments=sourceRight.segments := by
  obtain ⟨flow,_,_,_,_⟩ := beta_certified
  obtain ⟨principal⟩ := braLambda.site.actionPrincipal_exists
  let position : Position current.erase := ⟨[],rfl⟩
  obtain ⟨oldParent,oldWord,_⟩ := Matches.observation braLambda.site.net source_matches position
  obtain ⟨newParent,port,newWord,parentAt⟩ := actual_kept_root_parent
  have sourceWord : [.arg]=accessWord braLambda.site.net oldParent.val++[.arg] := by
    rw [oldWord];rfl
  have targetWord : [.arg]=accessWord braLambda.site.reduce newParent.val++[.arg] := by
    rw [newWord];rfl
  exact sourceLeft.bra_kept_parent_copied_lambda_equality braLambda.site
    (braLambda.sourceIso.flowBalance flow) (.inl ()) rfl source_matches target_matches principal
    targetLeft sourceRight targetRight role role oldParent oldParent newParent newParent
    sourceWord sourceWord targetWord targetWord port port parentAt parentAt
    (actual_context_finish targetLeft) (actual_context_finish targetRight)

/-- Real same-INIT/current data for this CONTEXT-terminal subclass.
The cro slot is FUNCTION; the bra slot is ARGUMENT, read backwards from lambda. -/
theorem actual_reachable_kept_parent_copied_lambda_context :
    INIT original ∧Closed original.erase ∧History [[]] original current ∧
    GraphTrace (ActualNet.initial term) (ActualNet.ofNet braLambda.site.reduce)
      [.beta 0,.braAction .lam 0 1 (by decide)] ∧
    Matches braLambda.site.net (.inl ()) current.erase ∧
    Matches braLambda.site.reduce (.inl ()) current.erase ∧
    Nonempty (SourceEdgeFragment current braLambda.site.net (.inl ()) edge [.arg]) ∧
    Nonempty (SourceEdgeFragment current braLambda.site.reduce (.inl ()) edge [.arg]) ∧
    PrerequisiteChain current [.arg] [[.arg],[.fn]] ∧
    ∀ (sourceLeft sourceRight : SourceEdgeFragment current braLambda.site.net (.inl ()) edge [.arg])
      (targetLeft targetRight : SourceEdgeFragment current braLambda.site.reduce (.inl ()) edge [.arg]),
      targetLeft.segments=targetRight.segments ↔sourceLeft.segments=sourceRight.segments := by
  obtain ⟨sourceExists,targetExists,chain⟩ := actual_fragments_and_chain
  exact ⟨BraSuccessfulChains.initial,BraSuccessfulChains.sourceClosed,BraSuccessfulChains.actualHistory,
    actual_two_rule_trace,source_matches,target_matches,sourceExists,targetExists,chain,actual_piece_pair_equality⟩
#print axioms actual_piece_pair_equality
#print axioms actual_reachable_kept_parent_copied_lambda_context
end Lamping.Checks.UnaryLambdaContextConsumer.Bra

#print axioms Lamping.AG.SourceEdgeFragment.cro_kept_parent_copied_lambda_cut
#print axioms Lamping.AG.SourceEdgeFragment.bra_kept_parent_copied_lambda_cut
#print axioms Lamping.AG.SourceEdgeFragment.cro_kept_parent_copied_lambda_equality
#print axioms Lamping.AG.SourceEdgeFragment.bra_kept_parent_copied_lambda_equality
