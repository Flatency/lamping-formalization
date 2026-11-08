import Lamping.Lamping.FanLambdaTerminalChildControlWord
import Lamping.Lamping.ActionKeptAssignedAccess
import Lamping.Lamping.ActionKeptFragmentComparison

namespace Lamping.AG
open Graph Lambda Lambda.Labelled ExposureScheduling

private theorem fanProgress_app_empty (kind : Kind) (p : Port kind)
    (same : kind=Kind.op Op.app) : controlPortWord kind p=[] := by
  subst kind
  cases p <;> rfl

private theorem fanProgress_access_split {N B W : Type}
    [FiniteNames N] [FiniteNames B] [FiniteNames W] {g : Net signature N B W}
    {root : B} {term : Term} {redex : RedexOcc term}
    (access : ActualRedexAccess g root redex) :
    controlWord g access.child.val=controlWord g access.parent.val++controlWord g access.connection.edges := by
  obtain ⟨connectionTail,connectionSplit⟩ := List.head?_eq_some_iff.mp access.connection.start
  have firstEmpty : endpointControlWord g
      (Sum.inl ⟨access.connection.app,access.connection.appPort⟩)=[] :=
    fanProgress_app_empty (g.label access.connection.app).sort access.connection.appPort
      (congrArg (fun l : Graph.Label signature => l.sort) access.connection.appLabel)
  have tokens : access.connection.edges.flatMap (endpointControlWord g)=controlWord g access.connection.edges := by
    rw [connectionSplit]
    change endpointControlWord g (Sum.inl ⟨access.connection.app,access.connection.appPort⟩)++
      connectionTail.flatMap (endpointControlWord g)=connectionTail.flatMap (endpointControlWord g)
    rw [firstEmpty]
    rfl
  have nonempty : access.parent.val≠[] := by
    intro empty
    have rooted := access.parent.property.2.1
    rw [empty] at rooted
    cases rooted
  rw [access.split]
  have appendWord : controlWord g (access.parent.val++access.connection.edges)=
      controlWord g access.parent.val++access.connection.edges.flatMap (endpointControlWord g) := by
    cases h : access.parent.val with
    | nil => exact False.elim (nonempty h)
    | cons head tail => exact List.flatMap_append
  exact appendWord.trans (congrArg (fun w=>controlWord g access.parent.val++w) tokens)

section
variable {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K → Graph.Label signature} {i j : Nat} {lt : i<j}
variable (site : PathSite (.fanAction .lam i j lt) kept (B:=B) (W:=W) (V:=V))
local notation "schema" => Schema.fanAction Op.lam i j lt
local notation "cut" => cutFragment site.net (pathPartition schema V) site.closed
local notation "rhs" => fanRight Op.lam i j
local notation "oldLambda" => (Sum.inl (Sigma.mk (Sum.inr (Sum.inr ())) (Sum.inl ())) : Endpoint site.net)

private theorem fanProgress_app_kept (node : K⊕(Unit⊕Unit))
    (port : Port (site.net.label node).sort) (index : Nat)
    (shape : site.net.label node=label Op.app index) :
    ∃ (k : K) (p : Port (kept k).sort),
      (⟨node,port⟩ : NodePort signature _ site.net.label)=⟨Sum.inl k,p⟩ := by
  cases node with
  | inl k => exact ⟨k,port,rfl⟩
  | inr chosen =>
    rcases chosen with u|u
    · cases u
      have impossible : Kind.op Op.fan=Kind.op Op.app :=
        congrArg (fun l : Graph.Label signature => l.sort) shape
      cases impossible
    · cases u
      have impossible : Kind.op Op.lam=Kind.op Op.app :=
        congrArg (fun l : Graph.Label signature => l.sort) shape
      cases impossible

/-- The same actual fan-selected target loses its final writer. Preserve the
literal retained APP parent before cancelling it from the full child words. -/
theorem ActualRedexAccess.fan_lam_control_count_progress
    {root : B} {current : LTerm} {redex : RedexOcc current.erase}
    (source : ActualRedexAccess site.net root redex)
    {directions : B → Bool} {depths : B → Int}
    (matching : Matches site.net root current.erase) (inputs : RootInputs site.net root)
    (flow : FlowBalance site.net directions) (positive : directions root=true)
    (balance : IndexedLevelBalance site.net depths) (rootDepth : depths root=0)
    (transparency : Transparency site.net root)
    (finish : source.child.val.getLast?=some (site.net.wire oldLambda))
    {a b : Context} (labels : Labelling site.net source.child.val a b) :
    ∃ (q : Bool) (target : ActualRedexAccess site.reduce root redex) (middle : Context),
      Labelling site.reduce target.child.val a middle ∧
      Traversal i (.op .fan) (Sum.inr q) (Sum.inl ()) middle b ∧
      controlWord site.net source.connection.edges=controlWord site.reduce target.connection.edges++[true] ∧
      controlCount site.reduce target.connection.edges+1=controlCount site.net source.connection.edges ∧
      controlCount site.reduce target.connection.edges<controlCount site.net source.connection.edges := by
  obtain ⟨q,target,middle,childLabels,writer,childWord⟩ :=
    source.fan_lam_child_control_word site matching inputs flow positive balance rootDepth transparency finish labels
  have targetMatches := site.action_matches_rootInputs (.fan .lam i j lt)
    flow root positive balance rootDepth inputs transparency matching
  obtain ⟨node,port,portEq⟩ := fanProgress_app_kept site source.connection.app source.ctx
    source.connection.appIndex source.connection.appLabel
  have sourceFinish : source.parent.val.getLast?=some (site.net.wire (Sum.inl ⟨Sum.inl node,port⟩)) :=
    source.parentFinish.trans (congrArg
      (fun np : NodePort signature _ site.net.label => some (site.net.wire (Sum.inl np))) portEq)
  obtain ⟨oldInput,oldOutput,oldLabels⟩ := source.parent.property.1.1
  obtain ⟨copied,copyWord,copyFinish,_copyLabels⟩ := site.action_kept_assigned_access (.fan .lam i j lt)
    matching inputs flow positive source.parent node port sourceFinish oldLabels
  have sameParent : copied=target.parent := targetMatches.accessWord_injective
    (copyWord.trans (source.parentWord.trans target.parentWord.symm))
  have targetFinish : target.parent.val.getLast?=some (site.reduce.wire (Sum.inl ⟨Sum.inl node,port⟩)) := by
    rw [←sameParent]
    exact copyFinish
  obtain ⟨principal⟩ := site.actionPrincipal_exists
  obtain ⟨parentInput,parentOutput,parentLabels⟩ := target.parent.property.1.1
  have result := site.action_kept_canonical_access (.fan .lam i j lt) flow root positive matching principal
    source.parent target.parent (source.parentWord.trans target.parentWord.symm) node port targetFinish parentLabels
  have rawParentWord := ActionCanonicalBlocks.lambda_control_word site rfl result.1 result.2.1
    (parentLabels.plug_decomposition cut rhs)
  let endIso : Bij (PlugSegment cut rhs) (Endpoint site.reduce) := plugEnd (cut).label (rhs).label
  change rawControlWord cut rhs (target.parent.val.map endIso.invFun)=
    controlWord site.net source.parent.val at rawParentWord
  have physicalParent : rawControlWord cut rhs (target.parent.val.map endIso.invFun)=
      controlWord site.reduce target.parent.val := by
    change rawControlWord cut rhs (target.parent.val.map endIso.invFun)=
      controlWord (plug cut rhs) target.parent.val
    simpa only [List.map_map,Function.comp_def,endIso,(plugEnd (cut).label (rhs).label).right_inv,
      List.map_id_fun'] using
      (controlWord_plug_map cut rhs (target.parent.val.map endIso.invFun)).symm
  have parentWord : controlWord site.reduce target.parent.val=controlWord site.net source.parent.val :=
    physicalParent.symm.trans rawParentWord
  have joined : controlWord site.net source.parent.val++controlWord site.net source.connection.edges=
      controlWord site.net source.parent.val++(controlWord site.reduce target.connection.edges++[true]) := by
    calc
      _=controlWord site.net source.child.val := (fanProgress_access_split source).symm
      _=controlWord site.reduce target.child.val++[true] := childWord
      _=(controlWord site.reduce target.parent.val++controlWord site.reduce target.connection.edges)++[true] := by
        rw [fanProgress_access_split target]
      _=controlWord site.net source.parent.val++(controlWord site.reduce target.connection.edges++[true]) := by
        rw [parentWord,List.append_assoc]
  have connectionWord := List.append_cancel_left joined
  have count : controlCount site.reduce target.connection.edges+1=controlCount site.net source.connection.edges := by
    change (controlWord site.reduce target.connection.edges).length+1=(controlWord site.net source.connection.edges).length
    rw [connectionWord,List.length_append]
    rfl
  exact ⟨q,target,middle,childLabels,writer,connectionWord,count,by omega⟩
end
end Lamping.AG
