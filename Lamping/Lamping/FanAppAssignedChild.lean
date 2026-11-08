import Lamping.Lamping.FanAppCopiedContextAccess
import Lamping.Lamping.ActionKeptAssignedAccess

namespace Lamping.AG
open Graph Lambda Lambda.Labelled
section
variable {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K → Graph.Label signature} {i j : Nat} {lt : i<j}
variable (site : PathSite (.fanAction .app i j lt) kept (B:=B) (W:=W) (V:=V))
local notation "copiedContext" => (fun branch : Bool =>
  (Sum.inl (Sigma.mk (Sum.inr (Sum.inl branch)) appCtx) : Endpoint site.reduce))

/-- Preserve the original child a,b at the actual kept endpoint and attach
its access to the SAME target as the source-derived copied-parent branch.
The reader packet records real parent contexts without identifying seams. -/
theorem ActualRedexAccess.fan_app_assigned_child
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
      ∃ parentInput parentOutput middle,
        Labelling site.net source.parent.val parentInput parentOutput ∧
        Labelling site.reduce target.parent.val parentInput middle ∧
        Traversal i (.op .fan) (Sum.inl ()) (Sum.inr branch) parentOutput middle := by
  obtain ⟨parentInput,parentOutput,parentLabels⟩ := source.parent.property.1.1
  obtain ⟨branch,target,parentFinish,middle,targetParentLabels,reader⟩ :=
    ActualRedexAccess.fan_app_copied_parent site source matching inputs flow positive
      balance rootDepth transparency sourceApp parentLabels
  obtain ⟨copied,childWord,childFinish,childLabels⟩ := site.action_kept_assigned_access
    (.fan .app i j lt) matching inputs flow positive source.child lamNode lamPort sourceLam sourceAssignment
  have targetMatches := site.action_matches_rootInputs (.fan .app i j lt)
    flow root positive balance rootDepth inputs transparency matching
  have sameChild : copied=target.child := targetMatches.accessWord_injective
    (childWord.trans (source.childWord.trans target.childWord.symm))
  have actualLabels : Labelling site.reduce target.child.val a b := by
    rw [←sameChild]
    exact childLabels
  have actualFinish : target.child.val.getLast?=some
      (site.reduce.wire (Sum.inl ⟨Sum.inl lamNode,lamPort⟩)) := by
    rw [←sameChild]
    exact childFinish
  exact ⟨branch,target,actualLabels,parentFinish,actualFinish,parentInput,parentOutput,middle,
    parentLabels,targetParentLabels,reader⟩
end
end Lamping.AG
