import Lamping.Lamping.BraLambdaTerminalWriterAccess
import Lamping.Lamping.LambdaActionCanonicalControlWord
import Lamping.Lamping.ActionCopiedBindingFragmentCuts

namespace Lamping.AG
open Graph Lambda Lambda.Labelled ExposureScheduling
section
variable {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K → Graph.Label signature} {i j : Nat} {lt : i<j}
variable (site : PathSite (.braAction .lam i j lt) kept (B:=B) (W:=W) (V:=V))
local notation "schema" => Schema.braAction Op.lam i j lt
local notation "cut" => cutFragment site.net (pathPartition schema V) site.closed
local notation "rhs" => unaryRightCore Op.bra Op.lam (Bij.refl Unit) i (j+1)
local notation "oldLambda" => (Sum.inl (Sigma.mk (Sum.inr (Sum.inr ())) (Sum.inl ())) : Endpoint site.net)
local notation "oldBody" => (Sum.inl (Sigma.mk (Sum.inr (Sum.inr ())) (Sum.inr true)) : Endpoint site.net)

/-- Whole rooted-child word, before cancelling the common actual APP parent.
The canonical padding has one writer; no caller supplies a crop or word law. -/
theorem ActualRedexAccess.bra_lam_child_control_word
    {root : B} {current : LTerm} {redex : RedexOcc current.erase}
    (source : ActualRedexAccess site.net root redex)
    {directions : B → Bool} {depths : B → Int}
    (matching : Matches site.net root current.erase) (inputs : RootInputs site.net root)
    (flow : FlowBalance site.net directions) (positive : directions root=true)
    (balance : IndexedLevelBalance site.net depths) (rootDepth : depths root=0)
    (transparency : Transparency site.net root)
    (finish : source.child.val.getLast?=some (site.net.wire oldLambda))
    {a b : Context} (labels : Labelling site.net source.child.val a b) :
    ∃ (target : ActualRedexAccess site.reduce root redex) (middle : Context),
      Labelling site.reduce target.child.val a middle ∧
      Traversal i (.op .bra) (Sum.inr ()) (Sum.inl ()) middle b ∧
      controlWord site.net source.child.val=controlWord site.reduce target.child.val++[true] := by
  obtain ⟨target,principal,_oldPre,middle,_split,_oldLabels,newLabels,newFinish,writer⟩ :=
    source.bra_lam_terminal_writer_child site matching inputs flow positive balance rootDepth
      transparency finish labels
  have word := source.childWord.trans target.childWord.symm
  have canonical := site.bra_lambda_canonical_access flow root positive matching principal
    source.child target.child word newFinish newLabels
  have padding := site.bra_lambda_padding_labels flow root positive matching principal
    source.child target.child word newFinish newLabels
  have fullWord := ActionCanonicalBlocks.lambda_control_word site rfl canonical padding.1 padding.2.2
  let splitEnd : Bij (PlugSegment cut rhs) (Endpoint site.reduce) := plugEnd (cut).label (rhs).label
  let raw : List (PlugSegment cut rhs) := target.child.val.map splitEnd.invFun
  let pad : List (PlugSegment cut rhs) :=
    [Sum.inr (Sum.inl (Sigma.mk (Sum.inl ()) (Sum.inr true))),
      Sum.inr (Sum.inl (Sigma.mk (Sum.inr true) (Sum.inl ()))),
      Sum.inl (Sum.inr (Sum.inl (Sum.inr (Sum.inr true))))]
  change rawControlWord cut rhs (raw++pad)=controlWord site.net (source.child.val++[oldBody]) at fullWord
  have rawNonempty : raw≠[] := by
    intro empty
    have heads := congrArg List.head? empty
    change (target.child.val.map splitEnd.invFun).head?=none at heads
    rw [List.head?_map,target.child.property.2.1,Option.map_some] at heads
    cases heads
  have appendWord : rawControlWord cut rhs (raw++pad)=
      rawControlWord cut rhs raw++pad.flatMap (Sum.elim (endpointControlWord cut) (endpointControlWord rhs)) := by
    cases rawEq : raw with
    | nil => exact False.elim (rawNonempty rawEq)
    | cons head tail => exact List.flatMap_append
  have physicalWord : rawControlWord cut rhs raw=controlWord site.reduce target.child.val := by
    change rawControlWord cut rhs (target.child.val.map splitEnd.invFun)=
      controlWord (plug cut rhs) target.child.val
    simpa only [List.map_map,Function.comp_def,splitEnd,(plugEnd (cut).label (rhs).label).right_inv,
      List.map_id_fun'] using
      (controlWord_plug_map cut rhs (target.child.val.map splitEnd.invFun)).symm
  have paddedTarget : rawControlWord cut rhs (raw++pad)=
      controlWord site.reduce target.child.val++[true] := by
    rw [appendWord,physicalWord]
    rfl
  have paddedSource : controlWord site.net (source.child.val++[oldBody])=
      controlWord site.net source.child.val := by
    have nonempty := labels.nonempty
    cases whole : source.child.val with
    | nil => exact False.elim (nonempty whole)
    | cons head tail =>
      change (tail++[oldBody]).flatMap (endpointControlWord site.net)=tail.flatMap (endpointControlWord site.net)
      rw [List.flatMap_append]
      change tail.flatMap (endpointControlWord site.net)++[]=tail.flatMap (endpointControlWord site.net)
      exact List.append_nil _
  exact ⟨target,middle,newLabels,writer,paddedSource.symm.trans (fullWord.symm.trans paddedTarget)⟩
end
end Lamping.AG
