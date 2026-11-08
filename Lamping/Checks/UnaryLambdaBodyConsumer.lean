import Lamping.Checks.UnaryLambdaContextConsumer
import Lamping.Lamping.CopiedLambdaBodyKeptComparison
import Lamping.Lamping.CopiedLambdaBodyMixed

namespace Lamping.Checks.UnaryLambdaBodyConsumer.Cro
open AG Graph Lambda Lambda.Labelled FunctionWrappedReachable
open UnaryBindingReachable.Cro

abbrev lambdaTerm : LTerm := UnaryLambdaContextConsumer.Cro.lambdaTerm
abbrev bodyTerm : LTerm := match lambdaTerm with
  | .lam _ body => body
  | term => term
abbrev edge := sourceEdge [lambdaTerm.label] (.lamBody lambdaTerm.label) bodyTerm
abbrev position : Path := [.fn,.body]

def occurrence : SourceSubterm [] .external current position [lambdaTerm.label] (.lamBody lambdaTerm.label) bodyTerm :=
  .fn (.body .nil)

theorem role : SourceDeparture lambdaTerm .body edge.fromPort := .body

theorem auxiliary : AuxiliaryAt current position := by
  constructor
  · rintro ⟨p,stamp,fn,arg,split,_lookup⟩
    have last:=congrArg List.getLast? split
    simp [position] at last
  · rintro ⟨stamp,body,lookup⟩;cases lookup

theorem never_reading_member (chain : PrerequisiteChain current p es) : position∉es := by
  intro member
  exact chain.not_auxiliary member auxiliary

abbrev bodyEdge : SyntaxIncidence.Edge current := ⟨position,rfl⟩
def lambdaVertex : SyntaxIncidence.Vertex current := some ⟨[.fn],Or.inr ⟨_,_,rfl⟩⟩
def appVertex : SyntaxIncidence.Vertex current := some ⟨position,Or.inl ⟨_,_,_,rfl⟩⟩

theorem source_coordinate : SyntaxIncidence.source current bodyEdge=lambdaVertex :=
  SyntaxIncidence.source_eq_of_spec current bodyEdge
    ⟨.body,lambdaTerm,.lamBody lambdaTerm.label,rfl,rfl,.body⟩
theorem target_coordinate : SyntaxIncidence.target current WrappedSuccessfulChains.targetClosed bodyEdge=appVertex :=
  SyntaxIncidence.target_eq_of_spec current WrappedSuccessfulChains.targetClosed bodyEdge (Or.inl rfl)

theorem endpoint_chains :
    EndpointChain current (SyntaxIncidence.source current bodyEdge) [[.fn]] ∧
    EndpointChain current (SyntaxIncidence.target current WrappedSuccessfulChains.targetClosed bodyEdge) WrappedSuccessfulChains.bodyEdges := by
  rw [source_coordinate,target_coordinate]
  exact ⟨UnaryLambdaContextConsumer.Cro.actual_chain,WrappedSuccessfulChains.body_chain⟩

theorem actual_kept_app_finish
    (fragment : SourceEdgeFragment current croLambda.site.reduce (.inl ()) edge position) :
    ∃ port : NodePort signature croLambda.Kept croLambda.kept,
      fragment.access.val.getLast?=some (croLambda.site.reduce.wire (.inl ⟨.inl port.1,port.2⟩)) := by
  let bodyPosition : Position current.erase := ⟨position,rfl⟩
  obtain ⟨observed,word,u,lookup,observes⟩ := Matches.observation croLambda.site.reduce target_matches bodyPosition
  have sameTerm : u=.app (.var 0) (.lam (.var 0)) := Option.some.inj (lookup.symm.trans rfl)
  subst u
  have sameAccess : observed=fragment.access := target_matches.accessWord_injective (word.trans fragment.word.symm)
  have kind : accessKind croLambda.site.reduce fragment.access.val=some .app := by
    rw [←sameAccess];exact observes.1
  exact UnaryBindingConsumer.Cro.app_access_kept fragment.access kind

theorem actual_piece_pair_equality
    (sourceLeft sourceRight : SourceEdgeFragment current croLambda.site.net (.inl ()) edge position)
    (targetLeft targetRight : SourceEdgeFragment current croLambda.site.reduce (.inl ()) edge position) :
    targetLeft.segments=targetRight.segments ↔sourceLeft.segments=sourceRight.segments := by
  obtain ⟨flow,_,_,_,_⟩ := beta_certified
  obtain ⟨principal⟩ := croLambda.site.actionPrincipal_exists
  let parentPosition : Position current.erase := ⟨[.fn],rfl⟩
  obtain ⟨oldParent,oldWord,_⟩ := Matches.observation croLambda.site.net source_matches parentPosition
  have sourceWord : position=accessWord croLambda.site.net oldParent.val++[.body] := by rw [oldWord];rfl
  have targetWord : position=accessWord croLambda.site.reduce lambdaParent.val++[.body] := by
    change position=accessWord croLambda.site.reduce lambdaEdges++[.body]
    rw [lambdaWord];rfl
  obtain ⟨leftEnd,leftFinish⟩ := actual_kept_app_finish targetLeft
  obtain ⟨rightEnd,rightFinish⟩ := actual_kept_app_finish targetRight
  exact sourceLeft.cro_copied_lambda_body_kept_equality croLambda.site
    (croLambda.sourceIso.flowBalance flow) (.inl ()) rfl source_matches target_matches principal
    targetLeft sourceRight targetRight role role oldParent oldParent lambdaParent lambdaParent
    sourceWord sourceWord targetWord targetWord lambdaFinish lambdaFinish
    leftEnd.1 rightEnd.1 leftEnd.2 rightEnd.2 leftFinish rightFinish

theorem actual_fragments :
    Nonempty (SourceEdgeFragment current croLambda.site.net (.inl ()) edge position) ∧
    Nonempty (SourceEdgeFragment current croLambda.site.reduce (.inl ()) edge position) :=
  ⟨source_matches.base_source_edge_fragment WrappedSuccessfulChains.targetClosed occurrence,
    target_matches.base_source_edge_fragment WrappedSuccessfulChains.targetClosed occurrence⟩

theorem actual_reachable_auxiliary_body_comparison :
    INIT original ∧Closed original.erase ∧History [[.fn]] original current ∧
    GraphTrace (ActualNet.initial term) (ActualNet.ofNet croLambda.site.reduce)
      [.beta 0,.croAction .lam 0 1 (by decide)] ∧
    Matches croLambda.site.net (.inl ()) current.erase ∧Matches croLambda.site.reduce (.inl ()) current.erase ∧
    AuxiliaryAt current position ∧
    EndpointChain current (SyntaxIncidence.source current bodyEdge) [[.fn]] ∧
    EndpointChain current (SyntaxIncidence.target current WrappedSuccessfulChains.targetClosed bodyEdge) WrappedSuccessfulChains.bodyEdges ∧
    Nonempty (SourceEdgeFragment current croLambda.site.net (.inl ()) edge position) ∧
    Nonempty (SourceEdgeFragment current croLambda.site.reduce (.inl ()) edge position) ∧
    ∀ (sourceLeft sourceRight : SourceEdgeFragment current croLambda.site.net (.inl ()) edge position)
      (targetLeft targetRight : SourceEdgeFragment current croLambda.site.reduce (.inl ()) edge position),
      targetLeft.segments=targetRight.segments ↔sourceLeft.segments=sourceRight.segments := by
  obtain ⟨sourceExists,targetExists⟩ := actual_fragments
  obtain ⟨parentChain,appChain⟩ := endpoint_chains
  exact ⟨WrappedSuccessfulChains.initial,WrappedSuccessfulChains.sourceClosed,WrappedSuccessfulChains.actualHistory,
    UnaryBindingConsumer.Cro.actual_two_rule_trace,source_matches,target_matches,auxiliary,
    parentChain,appChain,sourceExists,targetExists,actual_piece_pair_equality⟩
#print axioms auxiliary
#print axioms never_reading_member
#print axioms endpoint_chains
#print axioms actual_kept_app_finish
#print axioms actual_piece_pair_equality
#print axioms actual_reachable_auxiliary_body_comparison

abbrev rootFunction : LTerm := match current with
  | .app _ fn _ => fn
  | term => term
abbrev rootFunctionEdge := sourceEdge [] (.appFn current.label) rootFunction

def root_function_occurrence : SourceSubterm [] .external current [.fn] [] (.appFn current.label) rootFunction :=
  .fn .nil

theorem root_function_role : SourceDeparture current .fn rootFunctionEdge.fromPort := .fn

theorem source_app_access_kept (path : RootAccess croLambda.site.net (.inl ()))
    (typed : accessKind croLambda.site.net path.val=some .app) :
    ∃ port : NodePort signature croLambda.Kept croLambda.kept,
      path.val.getLast?=some (croLambda.site.net.wire (.inl ⟨.inl port.1,port.2⟩)) := by
  cases last : path.val.getLast? with
  | none => simp only [accessKind,last,Option.bind_none] at typed;cases typed
  | some e =>
    rw [accessKind,last] at typed
    cases arrival : croLambda.site.net.wire e with
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
        | inl u => cases u;cases p <;> cases typed
        | inr u =>
          cases u
          cases p with
          | inl u => cases u;cases typed
          | inr b => cases b <;> cases typed

theorem actual_source_root_parent :
    ∃ (parent : RootAccess croLambda.site.net (.inl ()))
      (port : NodePort signature croLambda.Kept croLambda.kept),
      accessWord croLambda.site.net parent.val=[] ∧
      parent.val.getLast?=some (croLambda.site.net.wire (.inl ⟨.inl port.1,port.2⟩)) := by
  let rootPosition : Position current.erase := ⟨[],rfl⟩
  obtain ⟨parent,word,u,lookup,observes⟩ := Matches.observation croLambda.site.net source_matches rootPosition
  have same : u=current.erase := Option.some.inj lookup.symm
  subst u
  obtain ⟨port,finish⟩ := source_app_access_kept parent observes.1
  exact ⟨parent,port,word,finish⟩

/-- A real distinct-position/class negative: root FUNCTION has retained APP
parent, while the BODY piece starts at the copied lambda. -/
theorem actual_body_vs_root_function
    (sourceBody : SourceEdgeFragment current croLambda.site.net (.inl ()) edge position)
    (targetBody : SourceEdgeFragment current croLambda.site.reduce (.inl ()) edge position)
    (sourceFunction : SourceEdgeFragment current croLambda.site.net (.inl ()) rootFunctionEdge [.fn])
    (targetFunction : SourceEdgeFragment current croLambda.site.reduce (.inl ()) rootFunctionEdge [.fn]) :
    sourceFunction.segments≠sourceBody.segments ∧targetFunction.segments≠targetBody.segments ∧
    (targetFunction.segments=targetBody.segments ↔sourceFunction.segments=sourceBody.segments) := by
  obtain ⟨flow,_,_,_,_⟩ := beta_certified
  obtain ⟨principal⟩ := croLambda.site.actionPrincipal_exists
  let parentPosition : Position current.erase := ⟨[.fn],rfl⟩
  obtain ⟨sourceParent,parentWord,_⟩ := Matches.observation croLambda.site.net source_matches parentPosition
  have oldBodyWord : position=accessWord croLambda.site.net sourceParent.val++[.body] := by rw [parentWord];rfl
  have newBodyWord : position=accessWord croLambda.site.reduce lambdaParent.val++[.body] := by
    change position=accessWord croLambda.site.reduce lambdaEdges++[.body]
    rw [lambdaWord];rfl
  obtain ⟨bodyEnd,bodyFinish⟩ := actual_kept_app_finish targetBody
  obtain ⟨oldRoot,oldPort,oldWord,oldFinish⟩ := actual_source_root_parent
  obtain ⟨newRoot,newPort,newWord,newFinish⟩ := UnaryLambdaContextConsumer.Cro.actual_kept_root_parent
  have oldFnWord : [.fn]=accessWord croLambda.site.net oldRoot.val++[.fn] := by rw [oldWord];rfl
  have newFnWord : [.fn]=accessWord croLambda.site.reduce newRoot.val++[.fn] := by rw [newWord];rfl
  exact sourceBody.cro_copied_lambda_body_vs_kept_parent croLambda.site
    (croLambda.sourceIso.flowBalance flow) (.inl ()) rfl source_matches target_matches principal
    targetBody role sourceParent lambdaParent oldBodyWord newBodyWord lambdaFinish bodyEnd.1 bodyEnd.2 bodyFinish
    sourceFunction targetFunction root_function_role oldRoot newRoot oldFnWord newFnWord
    oldPort.1 newPort.1 oldPort.2 newPort.2 oldFinish newFinish

theorem actual_four_mixed_fragments :
    Nonempty (SourceEdgeFragment current croLambda.site.net (.inl ()) edge position) ∧
    Nonempty (SourceEdgeFragment current croLambda.site.reduce (.inl ()) edge position) ∧
    Nonempty (SourceEdgeFragment current croLambda.site.net (.inl ()) rootFunctionEdge [.fn]) ∧
    Nonempty (SourceEdgeFragment current croLambda.site.reduce (.inl ()) rootFunctionEdge [.fn]) ∧position≠[.fn] := by
  obtain ⟨sourceBody,targetBody⟩ := actual_fragments
  exact ⟨sourceBody,targetBody,
    source_matches.base_source_edge_fragment WrappedSuccessfulChains.targetClosed root_function_occurrence,
    target_matches.base_source_edge_fragment WrappedSuccessfulChains.targetClosed root_function_occurrence,by decide⟩
#print axioms actual_body_vs_root_function
#print axioms actual_four_mixed_fragments
end Lamping.Checks.UnaryLambdaBodyConsumer.Cro

namespace Lamping.Checks.UnaryLambdaBodyConsumer.Bra
open AG Graph Lambda Lambda.Labelled BraFunctionReachable
open UnaryBindingReachable.Bra

abbrev lambdaTerm : LTerm := UnaryLambdaContextConsumer.Bra.lambdaTerm
abbrev bodyTerm : LTerm := match lambdaTerm with
  | .lam _ body => body
  | term => term
abbrev edge := sourceEdge [lambdaTerm.label] (.lamBody lambdaTerm.label) bodyTerm
abbrev position : Path := [.arg,.body]

def occurrence : SourceSubterm [] .external current position [lambdaTerm.label] (.lamBody lambdaTerm.label) bodyTerm :=
  .arg (.body .nil)

theorem role : SourceDeparture lambdaTerm .body edge.fromPort := .body

theorem auxiliary : AuxiliaryAt current position := by
  constructor
  · rintro ⟨p,stamp,fn,arg,split,_lookup⟩
    have last:=congrArg List.getLast? split
    simp [position] at last
  · rintro ⟨stamp,body,lookup⟩;cases lookup

theorem never_reading_member (chain : PrerequisiteChain current p es) : position∉es := by
  intro member
  exact chain.not_auxiliary member auxiliary

abbrev bodyEdge : SyntaxIncidence.Edge current := ⟨position,rfl⟩
def lambdaVertex : SyntaxIncidence.Vertex current := some ⟨[.arg],Or.inr ⟨_,_,rfl⟩⟩
def appVertex : SyntaxIncidence.Vertex current := some ⟨position,Or.inl ⟨_,_,_,rfl⟩⟩

theorem source_coordinate : SyntaxIncidence.source current bodyEdge=lambdaVertex :=
  SyntaxIncidence.source_eq_of_spec current bodyEdge
    ⟨.body,lambdaTerm,.lamBody lambdaTerm.label,rfl,rfl,.body⟩
theorem target_coordinate : SyntaxIncidence.target current BraSuccessfulChains.targetClosed bodyEdge=appVertex :=
  SyntaxIncidence.target_eq_of_spec current BraSuccessfulChains.targetClosed bodyEdge (Or.inl rfl)

theorem endpoint_chains :
    EndpointChain current (SyntaxIncidence.source current bodyEdge) [[.arg],[.fn]] ∧
    EndpointChain current (SyntaxIncidence.target current BraSuccessfulChains.targetClosed bodyEdge) BraSuccessfulChains.bodyEdges := by
  rw [source_coordinate,target_coordinate]
  exact ⟨UnaryLambdaContextConsumer.Bra.actual_chain,BraSuccessfulChains.body_chain⟩

theorem actual_kept_app_finish
    (fragment : SourceEdgeFragment current braLambda.site.reduce (.inl ()) edge position) :
    ∃ port : NodePort signature braLambda.Kept braLambda.kept,
      fragment.access.val.getLast?=some (braLambda.site.reduce.wire (.inl ⟨.inl port.1,port.2⟩)) := by
  let bodyPosition : Position current.erase := ⟨position,rfl⟩
  obtain ⟨observed,word,u,lookup,observes⟩ := Matches.observation braLambda.site.reduce target_matches bodyPosition
  have sameTerm : u=.app (.var 0) (.lam (.var 0)) := Option.some.inj (lookup.symm.trans rfl)
  subst u
  have sameAccess : observed=fragment.access := target_matches.accessWord_injective (word.trans fragment.word.symm)
  have kind : accessKind braLambda.site.reduce fragment.access.val=some .app := by
    rw [←sameAccess];exact observes.1
  exact UnaryBindingConsumer.Bra.app_access_kept fragment.access kind

theorem actual_piece_pair_equality
    (sourceLeft sourceRight : SourceEdgeFragment current braLambda.site.net (.inl ()) edge position)
    (targetLeft targetRight : SourceEdgeFragment current braLambda.site.reduce (.inl ()) edge position) :
    targetLeft.segments=targetRight.segments ↔sourceLeft.segments=sourceRight.segments := by
  obtain ⟨flow,_,_,_,_⟩ := beta_certified
  obtain ⟨principal⟩ := braLambda.site.actionPrincipal_exists
  let parentPosition : Position current.erase := ⟨[.arg],rfl⟩
  obtain ⟨oldParent,oldWord,_⟩ := Matches.observation braLambda.site.net source_matches parentPosition
  have sourceWord : position=accessWord braLambda.site.net oldParent.val++[.body] := by rw [oldWord];rfl
  have targetWord : position=accessWord braLambda.site.reduce lambdaParent.val++[.body] := by
    change position=accessWord braLambda.site.reduce lambdaEdges++[.body]
    rw [lambdaWord];rfl
  obtain ⟨leftEnd,leftFinish⟩ := actual_kept_app_finish targetLeft
  obtain ⟨rightEnd,rightFinish⟩ := actual_kept_app_finish targetRight
  exact sourceLeft.bra_copied_lambda_body_kept_equality braLambda.site
    (braLambda.sourceIso.flowBalance flow) (.inl ()) rfl source_matches target_matches principal
    targetLeft sourceRight targetRight role role oldParent oldParent lambdaParent lambdaParent
    sourceWord sourceWord targetWord targetWord lambdaFinish lambdaFinish
    leftEnd.1 rightEnd.1 leftEnd.2 rightEnd.2 leftFinish rightFinish

theorem actual_fragments :
    Nonempty (SourceEdgeFragment current braLambda.site.net (.inl ()) edge position) ∧
    Nonempty (SourceEdgeFragment current braLambda.site.reduce (.inl ()) edge position) :=
  ⟨source_matches.base_source_edge_fragment BraSuccessfulChains.targetClosed occurrence,
    target_matches.base_source_edge_fragment BraSuccessfulChains.targetClosed occurrence⟩

theorem actual_reachable_auxiliary_body_comparison :
    INIT original ∧Closed original.erase ∧History [[]] original current ∧
    GraphTrace (ActualNet.initial term) (ActualNet.ofNet braLambda.site.reduce)
      [.beta 0,.braAction .lam 0 1 (by decide)] ∧
    Matches braLambda.site.net (.inl ()) current.erase ∧Matches braLambda.site.reduce (.inl ()) current.erase ∧
    AuxiliaryAt current position ∧
    EndpointChain current (SyntaxIncidence.source current bodyEdge) [[.arg],[.fn]] ∧
    EndpointChain current (SyntaxIncidence.target current BraSuccessfulChains.targetClosed bodyEdge) BraSuccessfulChains.bodyEdges ∧
    Nonempty (SourceEdgeFragment current braLambda.site.net (.inl ()) edge position) ∧
    Nonempty (SourceEdgeFragment current braLambda.site.reduce (.inl ()) edge position) ∧
    ∀ (sourceLeft sourceRight : SourceEdgeFragment current braLambda.site.net (.inl ()) edge position)
      (targetLeft targetRight : SourceEdgeFragment current braLambda.site.reduce (.inl ()) edge position),
      targetLeft.segments=targetRight.segments ↔sourceLeft.segments=sourceRight.segments := by
  obtain ⟨sourceExists,targetExists⟩ := actual_fragments
  obtain ⟨parentChain,appChain⟩ := endpoint_chains
  exact ⟨BraSuccessfulChains.initial,BraSuccessfulChains.sourceClosed,BraSuccessfulChains.actualHistory,
    UnaryBindingConsumer.Bra.actual_two_rule_trace,source_matches,target_matches,auxiliary,
    parentChain,appChain,sourceExists,targetExists,actual_piece_pair_equality⟩
#print axioms auxiliary
#print axioms never_reading_member
#print axioms endpoint_chains
#print axioms actual_kept_app_finish
#print axioms actual_piece_pair_equality
#print axioms actual_reachable_auxiliary_body_comparison

abbrev rootFunction : LTerm := match current with
  | .app _ fn _ => fn
  | term => term
abbrev rootFunctionEdge := sourceEdge [] (.appFn current.label) rootFunction

def root_function_occurrence : SourceSubterm [] .external current [.fn] [] (.appFn current.label) rootFunction :=
  .fn .nil

theorem root_function_role : SourceDeparture current .fn rootFunctionEdge.fromPort := .fn

theorem source_app_access_kept (path : RootAccess braLambda.site.net (.inl ()))
    (typed : accessKind braLambda.site.net path.val=some .app) :
    ∃ port : NodePort signature braLambda.Kept braLambda.kept,
      path.val.getLast?=some (braLambda.site.net.wire (.inl ⟨.inl port.1,port.2⟩)) := by
  cases last : path.val.getLast? with
  | none => simp only [accessKind,last,Option.bind_none] at typed;cases typed
  | some e =>
    rw [accessKind,last] at typed
    cases arrival : braLambda.site.net.wire e with
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
        | inl u => cases u;cases p <;> cases typed
        | inr u =>
          cases u
          cases p with
          | inl u => cases u;cases typed
          | inr b => cases b <;> cases typed

theorem actual_source_root_parent :
    ∃ (parent : RootAccess braLambda.site.net (.inl ()))
      (port : NodePort signature braLambda.Kept braLambda.kept),
      accessWord braLambda.site.net parent.val=[] ∧
      parent.val.getLast?=some (braLambda.site.net.wire (.inl ⟨.inl port.1,port.2⟩)) := by
  let rootPosition : Position current.erase := ⟨[],rfl⟩
  obtain ⟨parent,word,u,lookup,observes⟩ := Matches.observation braLambda.site.net source_matches rootPosition
  have same : u=current.erase := Option.some.inj lookup.symm
  subst u
  obtain ⟨port,finish⟩ := source_app_access_kept parent observes.1
  exact ⟨parent,port,word,finish⟩

/-- A real distinct-position/class negative: root FUNCTION has retained APP
parent, while the BODY piece starts at the copied lambda. -/
theorem actual_body_vs_root_function
    (sourceBody : SourceEdgeFragment current braLambda.site.net (.inl ()) edge position)
    (targetBody : SourceEdgeFragment current braLambda.site.reduce (.inl ()) edge position)
    (sourceFunction : SourceEdgeFragment current braLambda.site.net (.inl ()) rootFunctionEdge [.fn])
    (targetFunction : SourceEdgeFragment current braLambda.site.reduce (.inl ()) rootFunctionEdge [.fn]) :
    sourceFunction.segments≠sourceBody.segments ∧targetFunction.segments≠targetBody.segments ∧
    (targetFunction.segments=targetBody.segments ↔sourceFunction.segments=sourceBody.segments) := by
  obtain ⟨flow,_,_,_,_⟩ := beta_certified
  obtain ⟨principal⟩ := braLambda.site.actionPrincipal_exists
  let parentPosition : Position current.erase := ⟨[.arg],rfl⟩
  obtain ⟨sourceParent,parentWord,_⟩ := Matches.observation braLambda.site.net source_matches parentPosition
  have oldBodyWord : position=accessWord braLambda.site.net sourceParent.val++[.body] := by rw [parentWord];rfl
  have newBodyWord : position=accessWord braLambda.site.reduce lambdaParent.val++[.body] := by
    change position=accessWord braLambda.site.reduce lambdaEdges++[.body]
    rw [lambdaWord];rfl
  obtain ⟨bodyEnd,bodyFinish⟩ := actual_kept_app_finish targetBody
  obtain ⟨oldRoot,oldPort,oldWord,oldFinish⟩ := actual_source_root_parent
  obtain ⟨newRoot,newPort,newWord,newFinish⟩ := UnaryLambdaContextConsumer.Bra.actual_kept_root_parent
  have oldFnWord : [.fn]=accessWord braLambda.site.net oldRoot.val++[.fn] := by rw [oldWord];rfl
  have newFnWord : [.fn]=accessWord braLambda.site.reduce newRoot.val++[.fn] := by rw [newWord];rfl
  exact sourceBody.bra_copied_lambda_body_vs_kept_parent braLambda.site
    (braLambda.sourceIso.flowBalance flow) (.inl ()) rfl source_matches target_matches principal
    targetBody role sourceParent lambdaParent oldBodyWord newBodyWord lambdaFinish bodyEnd.1 bodyEnd.2 bodyFinish
    sourceFunction targetFunction root_function_role oldRoot newRoot oldFnWord newFnWord
    oldPort.1 newPort.1 oldPort.2 newPort.2 oldFinish newFinish

theorem actual_four_mixed_fragments :
    Nonempty (SourceEdgeFragment current braLambda.site.net (.inl ()) edge position) ∧
    Nonempty (SourceEdgeFragment current braLambda.site.reduce (.inl ()) edge position) ∧
    Nonempty (SourceEdgeFragment current braLambda.site.net (.inl ()) rootFunctionEdge [.fn]) ∧
    Nonempty (SourceEdgeFragment current braLambda.site.reduce (.inl ()) rootFunctionEdge [.fn]) ∧position≠[.fn] := by
  obtain ⟨sourceBody,targetBody⟩ := actual_fragments
  exact ⟨sourceBody,targetBody,
    source_matches.base_source_edge_fragment BraSuccessfulChains.targetClosed root_function_occurrence,
    target_matches.base_source_edge_fragment BraSuccessfulChains.targetClosed root_function_occurrence,by decide⟩
#print axioms actual_body_vs_root_function
#print axioms actual_four_mixed_fragments
end Lamping.Checks.UnaryLambdaBodyConsumer.Bra

#print axioms Lamping.AG.SourceEdgeFragment.cro_copied_lambda_body_kept_cut
#print axioms Lamping.AG.SourceEdgeFragment.bra_copied_lambda_body_kept_cut
#print axioms Lamping.AG.SourceEdgeFragment.cro_copied_lambda_body_kept_equality
#print axioms Lamping.AG.SourceEdgeFragment.bra_copied_lambda_body_kept_equality

#print axioms Lamping.AG.SourceEdgeFragment.cro_copied_lambda_body_vs_kept_parent
#print axioms Lamping.AG.SourceEdgeFragment.bra_copied_lambda_body_vs_kept_parent
