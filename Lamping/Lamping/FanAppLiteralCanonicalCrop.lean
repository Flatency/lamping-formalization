import Lamping.Lamping.FanAppCopiedFunctionPrefix
import Lamping.Lamping.ActionKeptFragmentComparison
import Lamping.Lamping.ActionRawOutsideCut

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
local notation "functionRaw" => (fun branch : Bool =>
  (Sum.inr (Sum.inl (Sigma.mk (Sum.inl branch) (Sum.inl ()))) : PlugSegment cut rhs))
local notation "exitCut" => (fun branch : Bool =>
  (Sum.inr (Sum.inl (Sum.inr (Sum.inl branch))) : Endpoint cut))
local notation "exitRaw" => (fun branch : Bool => (Sum.inl (exitCut branch) : PlugSegment cut rhs))
local notation "oldReader" => (fun branch : Bool =>
  (Sum.inl (Sigma.mk (Sum.inr (Sum.inl ())) (Sum.inr branch)) : Endpoint site.net))

/-- Literal OLD/target crop at the actually selected fan branch. The kept
child retains its original whole a,b, while the new seam is an output. -/
theorem ActualRedexAccess.fan_app_literal_crop
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
      ∃ (principal : SiteActionPrincipal site) (oldTail : List (Endpoint site.net))
        (rawTail : List (PlugSegment cut rhs)) (newSeam : Context),
        source.connection.edges=reverseEdges principal.edges++(oldReader branch)::oldTail ∧
        target.connection.edges.map (plugEnd (cut).label (rhs).label).invFun=
          (functionRaw branch)::(exitRaw branch)::rawTail ∧
        ActionCanonicalBlocks site principal ((exitRaw branch)::rawTail) ((oldReader branch)::oldTail) ∧
        PlugLabelling cut rhs ((exitRaw branch)::rawTail) newSeam b := by
  obtain ⟨branch,target,childLabels,parentFinish,keptFinish,rawTail,newSeam,
      _pieceLabels,rawPrefix,suffixLabels⟩ :=
    ActualRedexAccess.fan_app_copied_function_prefix site source matching inputs flow positive
      balance rootDepth transparency sourceApp lamNode lamPort sourceLam sourceAssignment
  change List (PlugSegment cut rhs) at rawTail
  let rhsSplit : Bij (PlugSegment cut rhs) (Endpoint site.reduce) :=
    plugEnd (cut).label (rhs).label
  change target.connection.edges.map rhsSplit.invFun=
    (functionRaw branch)::(exitRaw branch)::rawTail at rawPrefix
  obtain ⟨principal⟩ := site.actionPrincipal_exists
  have parentWord : accessWord site.net source.parent.val=accessWord site.reduce target.parent.val :=
    source.parentWord.trans target.parentWord.symm
  obtain ⟨parentInput,parentOutput,parentLabels⟩ := target.parent.property.1.1
  have parentCanonical := site.fan_app_function_padding_access flow root positive matching principal
    source.parent target.parent parentWord branch parentFinish parentLabels
  have wholeCanonical := (site.action_kept_canonical_access (.fan .app i j lt) flow root positive
    matching principal source.child target.child (source.childWord.trans target.childWord.symm)
    lamNode lamPort keptFinish childLabels).1
  change ActionCanonicalBlocks site principal
    (@List.append (PlugSegment cut rhs) (target.parent.val.map rhsSplit.invFun)
      [functionRaw branch,exitRaw branch])
    (source.parent.val++reverseEdges principal.edges++[oldReader branch]) at parentCanonical
  change ActionCanonicalBlocks site principal (target.child.val.map rhsSplit.invFun)
    source.child.val at wholeCanonical
  let parentRaw : List (PlugSegment cut rhs) := target.parent.val.map rhsSplit.invFun
  let wholeRaw : List (PlugSegment cut rhs) := target.child.val.map rhsSplit.invFun
  let padRaw : List (PlugSegment cut rhs) :=
    @List.append (PlugSegment cut rhs) parentRaw [functionRaw branch,exitRaw branch]
  have rawSplit : wholeRaw=@List.append (PlugSegment cut rhs) padRaw rawTail := by
    change target.child.val.map rhsSplit.invFun=
      @List.append (PlugSegment cut rhs)
        (@List.append (PlugSegment cut rhs) (target.parent.val.map rhsSplit.invFun)
          [functionRaw branch,exitRaw branch]) rawTail
    rw [target.split,List.map_append,rawPrefix]
    change (target.parent.val.map rhsSplit.invFun)++
        (functionRaw branch)::(exitRaw branch)::rawTail=
      ((target.parent.val.map rhsSplit.invFun)++[functionRaw branch,exitRaw branch])++rawTail
    simp only [List.append_assoc,List.cons_append,List.nil_append]
  have padLast : padRaw.getLast?=some (exitRaw branch) := by
    change (parentRaw++[functionRaw branch,exitRaw branch]).getLast?=some (exitRaw branch)
    simp only [List.getLast?_append,List.getLast?_cons_cons,List.getLast?_singleton,Option.some_or]
  obtain ⟨oldTail,_cutSeam,oldWhole,suffixCanonical,_padLabels,_cutLabels⟩ :=
    wholeCanonical.cut_at_raw_parent site parentCanonical (childLabels.plug_decomposition cut rhs)
      rawSplit (exitCut branch) padLast
  have oldConnection : source.connection.edges=
      reverseEdges principal.edges++(oldReader branch)::oldTail := by
    have wholeEquality := source.split.symm.trans oldWhole
    have commonParent : source.parent.val++source.connection.edges=
        source.parent.val++(reverseEdges principal.edges++(oldReader branch)::oldTail) := by
      simpa only [List.append_assoc,List.singleton_append] using wholeEquality
    exact List.append_cancel_left commonParent
  exact ⟨branch,target,childLabels,principal,oldTail,rawTail,newSeam,
    oldConnection,rawPrefix,suffixCanonical,suffixLabels⟩
end
end Lamping.AG
