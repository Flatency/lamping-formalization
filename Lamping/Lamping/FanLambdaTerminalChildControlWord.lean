import Lamping.Lamping.FanLambdaTerminalWriterAccess
import Lamping.Lamping.LambdaActionCanonicalControlWord
import Lamping.Lamping.FanCopiedLambdaContextCuts

namespace Lamping.AG
open Graph Lambda Lambda.Labelled ExposureScheduling
section
variable {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K → Graph.Label signature} {i j : Nat} {lt : i<j}
variable (site : PathSite (.fanAction .lam i j lt) kept (B:=B) (W:=W) (V:=V))
local notation "schema" => Schema.fanAction Op.lam i j lt
local notation "cut" => cutFragment site.net (pathPartition schema V) site.closed
local notation "rhs" => fanRight Op.lam i j
local notation "oldLambda" => (Sum.inl (Sigma.mk (Sum.inr (Sum.inr ())) (Sum.inl ())) : Endpoint site.net)

/-- The real fan context trim identifies the whole copied child. Its selected
Bool writer is removed, while the canonical complete prefix keeps its word. -/
theorem ActualRedexAccess.fan_lam_child_control_word
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
      controlWord site.net source.child.val=controlWord site.reduce target.child.val++[true] := by
  obtain ⟨q,target,principal,_writerPre,middle,_writerSplit,_writerLabels,newLabels,newFinish,writer⟩ :=
    source.fan_lam_terminal_writer_child site matching inputs flow positive balance rootDepth
      transparency finish labels
  have syntaxWord := source.childWord.trans target.childWord.symm
  obtain ⟨pending,oldPre,_sameMiddle,canonical,oldLabels,oldSplit,_oldFinish,rawSplit⟩ :=
    site.fan_lambda_context_canonical_trim flow root positive matching principal
      source.child target.child syntaxWord q newFinish newLabels
  have canonicalWord := ActionCanonicalBlocks.lambda_control_word site rfl canonical oldLabels
    (pending.prefixPath.labelling cut rhs)
  let endIso : Bij (PlugSegment cut rhs) (Endpoint site.reduce) := plugEnd (cut).label (rhs).label
  have rawNonempty : pending.pre≠[] := by
    intro empty
    have last := pending.prefixLast
    rw [empty] at last
    cases last
  have finalBoundaryWord : rawControlWord cut rhs
      (pending.pre++[Sum.inr (Sum.inr (Sum.inl (Sum.inl q)))])=rawControlWord cut rhs pending.pre := by
    cases h : pending.pre with
    | nil => exact False.elim (rawNonempty h)
    | cons head tail =>
      change (tail++[Sum.inr (Sum.inr (Sum.inl (Sum.inl q)))]).flatMap
        (Sum.elim (endpointControlWord cut) (endpointControlWord rhs))=
        tail.flatMap (Sum.elim (endpointControlWord cut) (endpointControlWord rhs))
      rw [List.flatMap_append]
      change tail.flatMap (Sum.elim (endpointControlWord cut) (endpointControlWord rhs))++[]=_
      exact List.append_nil _
  have physicalRaw : rawControlWord cut rhs (target.child.val.map endIso.invFun)=
      controlWord site.reduce target.child.val := by
    change rawControlWord cut rhs (target.child.val.map endIso.invFun)=
      controlWord (plug cut rhs) target.child.val
    simpa only [List.map_map,Function.comp_def,endIso,(plugEnd (cut).label (rhs).label).right_inv,
      List.map_id_fun'] using
      (controlWord_plug_map cut rhs (target.child.val.map endIso.invFun)).symm
  have targetWord : controlWord site.reduce target.child.val=controlWord site.net oldPre := by
    apply physicalRaw.symm.trans
    change rawControlWord cut rhs
      (target.child.val.map (plugEnd (cut).label (rhs).label).invFun)=controlWord site.net oldPre
    change target.child.val.map (plugEnd (cut).label (rhs).label).invFun=
      @List.append (PlugSegment cut rhs) pending.pre
        [(Sum.inr (Sum.inr (Sum.inl (Sum.inl q))) : PlugSegment cut rhs)] at rawSplit
    rw [rawSplit]
    exact finalBoundaryWord.trans canonicalWord
  have principalTokens : principal.edges.flatMap (endpointControlWord site.net)=[true] := by
    obtain ⟨tail,split⟩ := List.head?_eq_some_iff.mp principal.first
    have transparent := transparent_control_word site.net principal.edges principal.transparent
    rw [split] at transparent ⊢
    change tail.flatMap (endpointControlWord site.net)=[] at transparent
    change endpointControlWord site.net (Sum.inl ⟨Sum.inr (Sum.inl ()),Sum.inl ()⟩)++
      tail.flatMap (endpointControlWord site.net)=[true]
    rw [transparent]
    rfl
  have sourceWord : controlWord site.net source.child.val=controlWord site.net oldPre++[true] := by
    rw [oldSplit]
    have nonempty := oldLabels.nonempty
    have appendWord : controlWord site.net (oldPre++principal.edges)=
        controlWord site.net oldPre++principal.edges.flatMap (endpointControlWord site.net) := by
      cases h : oldPre with
      | nil => exact False.elim (nonempty h)
      | cons head tail => exact List.flatMap_append
    exact appendWord.trans (congrArg (fun w=>controlWord site.net oldPre++w) principalTokens)
  exact ⟨q,target,middle,newLabels,writer,
    sourceWord.trans (congrArg (fun w=>w++[true]) targetWord.symm)⟩
end
end Lamping.AG
