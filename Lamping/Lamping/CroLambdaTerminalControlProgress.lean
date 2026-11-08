import Lamping.Lamping.CroLambdaTerminalWriterAccess
import Lamping.Lamping.CroLambdaCanonicalControlWord
import Lamping.Lamping.ActionKeptAssignedAccess
import Lamping.Lamping.ActionKeptFragmentComparison
import Lamping.Lamping.ActionCopiedBindingFragmentCuts

namespace Lamping.AG
open Graph Lambda Lambda.Labelled ExposureScheduling

private theorem app_port_word_empty (kind : Kind) (port : Port kind) (same : kind=Kind.op Op.app) :
    controlPortWord kind port=[] := by
  subst kind
  cases port <;> rfl

private theorem controlWord_append {N B W : Type}
    [FiniteNames N] [FiniteNames B] [FiniteNames W]
    (g : Net signature N B W) (before after : List (Endpoint g)) (nonempty : before≠[]) :
    controlWord g (before++after)=controlWord g before++after.flatMap (endpointControlWord g) := by
  cases before with
  | nil => exact False.elim (nonempty rfl)
  | cons head before => exact List.flatMap_append

private theorem connection_tokens {N B W : Type}
    [FiniteNames N] [FiniteNames B] [FiniteNames W] {g : Net signature N B W}
    (connection : RedexConnection g) :
    connection.edges.flatMap (endpointControlWord g)=controlWord g connection.edges := by
  obtain ⟨tail,split⟩ := List.head?_eq_some_iff.mp connection.start
  rw [split]
  change endpointControlWord g (Sum.inl ⟨connection.app,connection.appPort⟩)++
    tail.flatMap (endpointControlWord g)=tail.flatMap (endpointControlWord g)
  have empty : endpointControlWord g (Sum.inl ⟨connection.app,connection.appPort⟩)=[] :=
    app_port_word_empty (g.label connection.app).sort connection.appPort
      (congrArg (fun actual : Graph.Label signature => actual.sort) connection.appLabel)
  rw [empty]
  rfl

private theorem access_control_split {N B W : Type}
    [FiniteNames N] [FiniteNames B] [FiniteNames W] {g : Net signature N B W}
    {root : B} {term : Term} {redex : RedexOcc term} (access : ActualRedexAccess g root redex) :
    controlWord g access.child.val=controlWord g access.parent.val++controlWord g access.connection.edges := by
  have nonempty : access.parent.val≠[] := by
    intro empty
    have first := access.parent.property.2.1
    rw [empty] at first
    cases first
  rw [access.split,controlWord_append g _ _ nonempty,connection_tokens access.connection]

section
variable {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K → Graph.Label signature} {i j : Nat} {lt : i<j}
variable (site : PathSite (.croAction .lam i j lt) kept (B:=B) (W:=W) (V:=V))
local notation "schema" => Schema.croAction Op.lam i j lt
local notation "cut" => cutFragment site.net (pathPartition schema V) site.closed
local notation "rhs" => unaryRightCore Op.cro Op.lam (Bij.refl Unit) i (j-1)
local notation "oldLambda" => (Sum.inl (Sigma.mk (Sum.inr (Sum.inr ())) (Sum.inl ())) : Endpoint site.net)
local notation "oldBody" => (Sum.inl (Sigma.mk (Sum.inr (Sum.inr ())) (Sum.inr true)) : Endpoint site.net)

/-- This is finite case analysis of the concrete site's actual node carrier,
not an inference of a current coordinate from a global label decoder. -/
private theorem app_kept_port (node : K⊕(Unit⊕Unit))
    (port : Port (site.net.label node).sort) (index : Nat)
    (shape : site.net.label node=label Op.app index) :
    ∃ (keptNode : K) (keptPort : Port (kept keptNode).sort),
      (⟨node,port⟩ : NodePort signature _ site.net.label)=⟨Sum.inl keptNode,keptPort⟩ := by
  cases node with
  | inl k => exact ⟨k,port,rfl⟩
  | inr selected =>
    rcases selected with u|u
    · cases u
      have impossible : Kind.op Op.cro=Kind.op Op.app :=
        congrArg (fun actual : Graph.Label signature => actual.sort) shape
      cases impossible
    · cases u
      have impossible : Kind.op Op.lam=Kind.op Op.app :=
        congrArg (fun actual : Graph.Label signature => actual.sort) shape
      cases impossible

private theorem actual_parent_finish
    {root : B} {current : LTerm} {redex : RedexOcc current.erase}
    (source : ActualRedexAccess site.net root redex) (target : ActualRedexAccess site.reduce root redex)
    {directions : B → Bool} (matching : Matches site.net root current.erase)
    (inputs : RootInputs site.net root) (flow : FlowBalance site.net directions)
    (positive : directions root=true) (targetMatches : Matches site.reduce root current.erase) :
    ∃ (node : K) (port : Port (kept node).sort),
      source.parent.val.getLast?=some (site.net.wire (Sum.inl ⟨Sum.inl node,port⟩)) ∧
      target.parent.val.getLast?=some (site.reduce.wire (Sum.inl ⟨Sum.inl node,port⟩)) := by
  obtain ⟨node,port,ports⟩ := app_kept_port site source.connection.app source.ctx
    source.connection.appIndex source.connection.appLabel
  have sourceFinish : source.parent.val.getLast?=
      some (site.net.wire (Sum.inl ⟨Sum.inl node,port⟩)) :=
    source.parentFinish.trans (congrArg
      (fun np : NodePort signature _ site.net.label => some (site.net.wire (Sum.inl np))) ports)
  obtain ⟨parentInput,parentOutput,parentLabels⟩ := source.parent.property.1.1
  obtain ⟨copied,word,finish,_labels⟩ := site.action_kept_assigned_access (.cro .lam i j lt)
    matching inputs flow positive source.parent node port sourceFinish parentLabels
  have sameParent : copied=target.parent := targetMatches.accessWord_injective
    (word.trans (source.parentWord.trans target.parentWord.symm))
  refine ⟨node,port,sourceFinish,?_⟩
  rw [←sameParent]
  exact finish

private theorem physical_raw_word (es : List (Endpoint site.reduce)) :
    rawControlWord cut rhs (es.map (plugEnd (cut).label (rhs).label).invFun)=controlWord site.reduce es := by
  simpa only [List.map_map,Function.comp_def,(plugEnd (cut).label (rhs).label).right_inv,
    List.map_id_fun'] using
      (controlWord_plug_map cut rhs (es.map (plugEnd (cut).label (rhs).label).invFun)).symm

private theorem raw_append (before after : List (PlugSegment cut rhs)) (nonempty : before≠[]) :
    rawControlWord cut rhs (before++after)=rawControlWord cut rhs before++
      after.flatMap (Sum.elim (endpointControlWord cut) (endpointControlWord rhs)) := by
  cases before with
  | nil => exact False.elim (nonempty rfl)
  | cons head before => exact List.flatMap_append

/-- The actual terminal writer disappears from the complete SAME target
connection. New output middle and writer middle→old b remain explicit. -/
theorem ActualRedexAccess.cro_lam_control_count_progress
    {root : B} {current : LTerm} {redex : RedexOcc current.erase}
    (source : ActualRedexAccess site.net root redex)
    {directions : B → Bool} {depths : B → Int}
    (matching : Matches site.net root current.erase) (inputs : RootInputs site.net root)
    (flow : FlowBalance site.net directions) (positive : directions root=true)
    (balance : IndexedLevelBalance site.net depths) (rootDepth : depths root=0)
    (transparency : Transparency site.net root)
    (finish : source.child.val.getLast?=some (site.net.wire oldLambda))
    {a b : Context} (sourceLabels : Labelling site.net source.child.val a b) :
    ∃ (target : ActualRedexAccess site.reduce root redex) (middle : Context),
      Labelling site.reduce target.child.val a middle ∧
      Traversal i (.op .cro) (Sum.inr ()) (Sum.inl ()) middle b ∧
      controlWord site.net source.connection.edges=controlWord site.reduce target.connection.edges++[true] ∧
      controlCount site.reduce target.connection.edges+1=controlCount site.net source.connection.edges ∧
      controlCount site.reduce target.connection.edges<controlCount site.net source.connection.edges := by
  obtain ⟨target,principal,_pre,middle,_oldChildSplit,_preLabels,childLabels,childFinish,writer⟩ :=
    source.cro_lam_terminal_writer_child site matching inputs flow positive balance rootDepth transparency finish sourceLabels
  have targetMatches := site.action_matches_rootInputs (.cro .lam i j lt)
    flow root positive balance rootDepth inputs transparency matching
  obtain ⟨parentNode,parentPort,_oldParentFinish,parentFinish⟩ :=
    actual_parent_finish site source target matching inputs flow positive targetMatches
  obtain ⟨parentInput,parentOutput,parentLabels⟩ := target.parent.property.1.1
  have syntaxParentWord := source.parentWord.trans target.parentWord.symm
  have parentResult := site.action_kept_canonical_access (.cro .lam i j lt) flow root positive
    matching principal source.parent target.parent syntaxParentWord parentNode parentPort parentFinish parentLabels
  have parentTransport := parentResult.1.cro_lam_control_word site parentResult.2.1
    (parentLabels.plug_decomposition cut rhs)
  have controlParents : controlWord site.reduce target.parent.val=controlWord site.net source.parent.val :=
    (physical_raw_word site target.parent.val).symm.trans parentTransport
  have syntaxChildWord := source.childWord.trans target.childWord.symm
  have wholeCanonical := site.cro_lambda_canonical_access flow root positive matching principal
    source.child target.child syntaxChildWord childFinish childLabels
  have padded := site.cro_lambda_padding_labels flow root positive matching principal
    source.child target.child syntaxChildWord childFinish childLabels
  have wholeWord := wholeCanonical.cro_lam_control_word site padded.1 padded.2.2
  let rhsSplit : Bij (PlugSegment cut rhs) (Endpoint site.reduce) := plugEnd (cut).label (rhs).label
  let pad : List (PlugSegment cut rhs) :=
    [Sum.inr (Sum.inl ⟨Sum.inl (),Sum.inr true⟩),Sum.inr (Sum.inl ⟨Sum.inr true,Sum.inl ()⟩),
      Sum.inl (Sum.inr (Sum.inl (Sum.inr (Sum.inr true))))]
  change rawControlWord cut rhs (target.child.val.map rhsSplit.invFun++pad)=
    controlWord site.net (source.child.val++[oldBody]) at wholeWord
  have rawNonempty : target.child.val.map rhsSplit.invFun≠[] := by
    intro empty
    have heads := congrArg List.head? empty
    rw [List.head?_map,target.child.property.2.1,Option.map_some] at heads
    cases heads
  have paddedTargetWord : rawControlWord cut rhs (target.child.val.map rhsSplit.invFun++pad)=
      controlWord site.reduce target.child.val++[true] := by
    rw [raw_append site _ _ rawNonempty,physical_raw_word site target.child.val]
    rfl
  have oldPaddingWord : controlWord site.net (source.child.val++[oldBody])=
      controlWord site.net source.child.val := by
    rw [controlWord_append site.net _ _ sourceLabels.nonempty]
    change controlWord site.net source.child.val++[]=controlWord site.net source.child.val
    exact List.append_nil _
  have childWord : controlWord site.net source.child.val=controlWord site.reduce target.child.val++[true] :=
    oldPaddingWord.symm.trans (wholeWord.symm.trans paddedTargetWord)
  have joined : controlWord site.net source.parent.val++controlWord site.net source.connection.edges=
      controlWord site.net source.parent.val++(controlWord site.reduce target.connection.edges++[true]) := by
    calc
      _=controlWord site.net source.child.val := (access_control_split source).symm
      _=controlWord site.reduce target.child.val++[true] := childWord
      _=(controlWord site.reduce target.parent.val++controlWord site.reduce target.connection.edges)++[true] := by
        rw [access_control_split target]
      _=controlWord site.net source.parent.val++(controlWord site.reduce target.connection.edges++[true]) := by
        rw [controlParents,List.append_assoc]
  have connectionWord := List.append_cancel_left joined
  have count : controlCount site.reduce target.connection.edges+1=controlCount site.net source.connection.edges := by
    change (controlWord site.reduce target.connection.edges).length+1=(controlWord site.net source.connection.edges).length
    rw [connectionWord,List.length_append]
    rfl
  exact ⟨target,middle,childLabels,writer,connectionWord,count,by omega⟩
end
end Lamping.AG
