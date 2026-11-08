import Lamping.Lamping.FanAppAssignedChild
import Lamping.Lamping.FanAppCopiedFunctionCuts

namespace Lamping.AG
open Graph Lambda Lambda.Labelled
section
variable {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K → Graph.Label signature} {i j : Nat} {lt : i<j}
variable (site : PathSite (.fanAction .app i j lt) kept (B:=B) (W:=W) (V:=V))
local notation "schema" => Schema.fanAction Op.app i j lt
local notation "cut" => cutFragment site.net (pathPartition schema V) site.closed
local notation "rhs" => fanRight Op.app i j
local notation "copiedContext" => (fun branch : Bool =>
  (Sum.inl (Sigma.mk (Sum.inr (Sum.inl branch)) appCtx) : Endpoint site.reduce))
local notation "copiedFunction" => (fun branch : Bool =>
  (Sum.inl (Sigma.mk (Sum.inr (Sum.inl branch)) (Sum.inl ())) : Endpoint site.reduce))
local notation "functionRaw" => (fun branch : Bool =>
  (Sum.inr (Sum.inl (Sigma.mk (Sum.inl branch) (Sum.inl ()))) : PlugSegment cut rhs))
local notation "exitRaw" => (fun branch : Bool =>
  (Sum.inl (Sum.inr (Sum.inl (Sum.inr (Sum.inl branch)))) : PlugSegment cut rhs))

/-- THIS actual target connection starts at the copied function selected by
its real source assignment. Its labels determine the new connection seam. -/
theorem ActualRedexAccess.fan_app_copied_function_prefix
    {root : B} {current : LTerm} {redex : RedexOcc current.erase}
    (source : ActualRedexAccess site.net root redex)
    {directions : B → Bool} {depths : B → Int}
    (matching : Matches site.net root current.erase) (inputs : RootInputs site.net root)
    (flow : FlowBalance site.net directions) (positive : directions root=true)
    (balance : IndexedLevelBalance site.net depths) (rootDepth : depths root=0)
    (transparency : Transparency site.net root)
    (sourceApp : source.parent.val.getLast?=some
      (site.net.wire (Sum.inl ⟨Sum.inr (Sum.inr ()),appCtx⟩)))
    (lamNode : K) (lamPort : Port (kept lamNode).sort)
    (sourceLam : source.child.val.getLast?=some
      (site.net.wire (Sum.inl ⟨Sum.inl lamNode,lamPort⟩)))
    {a b : Context} (sourceAssignment : Labelling site.net source.child.val a b) :
    ∃ (branch : Bool) (target : ActualRedexAccess site.reduce root redex),
      Labelling site.reduce target.child.val a b ∧
      target.parent.val.getLast?=some (site.reduce.wire (copiedContext branch)) ∧
      target.child.val.getLast?=some (site.reduce.wire (Sum.inl ⟨Sum.inl lamNode,lamPort⟩)) ∧
      ∃ (rawTail : List (PlugSegment cut rhs)) (newSeam : Context),
        Labelling site.reduce target.connection.edges newSeam b ∧
        target.connection.edges.map (plugEnd (cut).label (rhs).label).invFun=
          (functionRaw branch)::(exitRaw branch)::rawTail ∧
        PlugLabelling cut rhs ((exitRaw branch)::rawTail) newSeam b := by
  obtain ⟨branch,target,childLabels,parentFinish,childFinish,_readerPacket⟩ :=
    ActualRedexAccess.fan_app_assigned_child site source matching inputs flow positive
      balance rootDepth transparency sourceApp lamNode lamPort sourceLam sourceAssignment
  have wires := Option.some.inj (target.parentFinish.symm.trans parentFinish)
  have ports := congrArg site.reduce.wire.mate wires
  simp only [Pairing.involutive] at ports
  have contexts : (⟨target.connection.app,target.ctx⟩ : NodePort signature _ site.reduce.label)=
      ⟨Sum.inr (Sum.inl branch),appCtx⟩ := Sum.inl.inj ports
  have appEq : target.connection.app=Sum.inr (Sum.inl branch) := congrArg Sigma.fst contexts
  have functions : (⟨target.connection.app,target.connection.appPort⟩ : NodePort signature _ site.reduce.label)=
      ⟨Sum.inr (Sum.inl branch),Sum.inl ()⟩ := Sigma.ext appEq target.connection.appPrincipal
  have first : target.connection.edges.head?=some (copiedFunction branch) :=
    target.connection.start.trans (congrArg (fun p=>some (Sum.inl p)) functions)
  let rhsSplit : Bij (PlugSegment cut rhs) (Endpoint site.reduce) :=
    plugEnd (cut).label (rhs).label
  have rawHead : (target.connection.edges.map rhsSplit.invFun).head?=
      some (functionRaw branch) := by
    rw [List.head?_map,first]
    rfl
  obtain ⟨tail,connectionSplit⟩ := List.head?_eq_some_iff.mp first
  have wholeLabels : Labelling site.reduce
      (@List.append (Endpoint site.reduce) target.parent.val ((copiedFunction branch)::tail)) a b := by
    rw [←connectionSplit]
    change Labelling site.reduce (target.parent.val++target.connection.edges) a b
    rw [←target.split]
    exact childLabels
  obtain ⟨newSeam,_prefixLabels,suffixLabels⟩ := wholeLabels.split_segment
  have pieceLabels : Labelling site.reduce target.connection.edges newSeam b := by
    rw [connectionSplit]
    exact suffixLabels
  have sameKind : accessKind site.reduce target.connection.edges=accessKind site.reduce target.child.val := by
    simp only [accessKind,target.split,List.getLast?_append,target.connection.finish,Option.some_or]
  have typed : ∃ kind,accessKind site.reduce target.connection.edges=some kind := by
    rw [sameKind]
    exact target.child.property.2.2
  obtain ⟨rawTail,literal,suffix⟩ := fan_app_typed_function_prefix cut i j branch
    (pieceLabels.plug_decomposition cut rhs) rawHead
    (by simpa only [plug_decomposition_flatten] using typed)
  exact ⟨branch,target,childLabels,parentFinish,childFinish,rawTail,newSeam,pieceLabels,literal,suffix⟩
end
end Lamping.AG
