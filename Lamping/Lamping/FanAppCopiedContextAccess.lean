import Lamping.Lamping.MatchingRedexEndpointUniqueness
import Lamping.Lambda.Labels
import Lamping.Lamping.SourceActionProperAuxAccess
import Lamping.Lamping.ActionMatching

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

/-- Preserve the branch and physical copied APP context finish produced by
THIS source root assignment. No target endpoint or branch is a premise. -/
theorem PathSite.fan_app_copied_context_access
    {root : B} {term : Term} {directions : B → Bool}
    (matching : Matches site.net root term) (inputs : RootInputs site.net root)
    (flow : FlowBalance site.net directions) (positive : directions root=true)
    (source : RootAccess site.net root)
    (sourceFinish : source.val.getLast?=some
      (site.net.wire (Sum.inl ⟨Sum.inr (Sum.inr ()),appCtx⟩)))
    {parentInput parentOutput : Context}
    (sourceLabels : Labelling site.net source.val parentInput parentOutput) :
    ∃ (branch : Bool) (copied : RootAccess site.reduce root),
      accessWord site.reduce copied.val=accessWord site.net source.val ∧
      copied.val.getLast?=some (site.reduce.wire (copiedContext branch)) ∧
      ∃ middle,Labelling site.reduce copied.val parentInput middle ∧
        Traversal i (.op .fan) (Sum.inl ()) (Sum.inr branch) parentOutput middle := by
  obtain ⟨branch,uniform⟩ := site.source_control_branch matching inputs flow positive
    (Or.inl rfl) rfl source.val appCtx HEq.rfl
    sourceLabels source.property.2.1 sourceFinish
  obtain ⟨middle,reader⟩ := uniform parentInput parentOutput sourceLabels
  let inside : List (Endpoint rhs) :=
    [Sum.inr (Sum.inl (Sum.inr false)),Sum.inl ⟨Sum.inr false,Sum.inr branch⟩]
  have rhsLabels : Labelling rhs inside parentOutput middle :=
    .cons (.node _ _ _ reader) (.single _ _)
  obtain ⟨actual,actualLabels,actualRoot,actualLast,word⟩ :=
    site.source_pending_expansion (.fan .app i j lt) matching inputs flow positive
      sourceLabels source.property.2.1 (Sum.inr false) sourceFinish inside rhsLabels rfl
  have copiedFinish : actual.getLast?=some (site.reduce.wire (copiedContext branch)) := by
    change actual.getLast?=some
      (AG.plugRight cut rhs (Sum.inl ⟨Sum.inr false,Sum.inr branch⟩))
    simpa only [inside,List.getLast?_cons_cons,List.getLast?_singleton,Option.map_some] using actualLast
  have kindPreserved : accessKind site.reduce actual=accessKind site.net source.val := by
    simp only [accessKind,copiedFinish,sourceFinish,Option.bind_some,Pairing.involutive]
    rfl
  obtain ⟨targetFlow⟩ := site.reduce_flowBalance flow
  have forward := actualLabels.root_forward_of_flow targetFlow root actualRoot positive
  have typed : ∃ kind,accessKind site.reduce actual=some kind := by
    rw [kindPreserved]
    exact source.property.2.2
  have noTokens : accessTokens (schema).right.net inside=[] := by
    change accessTokens rhs inside=[]
    rfl
  rw [noTokens,List.append_nil] at word
  let copied : RootAccess site.reduce root :=
    ⟨actual,⟨⟨⟨parentInput,middle,actualLabels⟩,forward⟩,actualRoot,typed⟩⟩
  exact ⟨branch,copied,word,copiedFinish,middle,actualLabels,reader⟩

/-- Rooted-word uniqueness attaches the constructed branch finish to the
SAME current/redex parent; target Matches is derived from the real action. -/
theorem ActualRedexAccess.fan_app_copied_parent
    {root : B} {current : LTerm} {redex : RedexOcc current.erase}
    (source : ActualRedexAccess site.net root redex)
    {directions : B → Bool} {depths : B → Int}
    (matching : Matches site.net root current.erase) (inputs : RootInputs site.net root)
    (flow : FlowBalance site.net directions) (positive : directions root=true)
    (balance : IndexedLevelBalance site.net depths) (rootDepth : depths root=0)
    (transparency : Transparency site.net root)
    (sourceFinish : source.parent.val.getLast?=some
      (site.net.wire (Sum.inl ⟨Sum.inr (Sum.inr ()),appCtx⟩)))
    {parentInput parentOutput : Context}
    (sourceLabels : Labelling site.net source.parent.val parentInput parentOutput) :
    ∃ (branch : Bool) (target : ActualRedexAccess site.reduce root redex),
      target.parent.val.getLast?=some (site.reduce.wire (copiedContext branch)) ∧
      ∃ middle,Labelling site.reduce target.parent.val parentInput middle ∧
        Traversal i (.op .fan) (Sum.inl ()) (Sum.inr branch) parentOutput middle := by
  obtain ⟨branch,copied,sameWord,finish,middle,labels,reader⟩ :=
    site.fan_app_copied_context_access matching inputs flow positive
      source.parent sourceFinish sourceLabels
  have targetMatches := site.action_matches_rootInputs (.fan .app i j lt)
    flow root positive balance rootDepth inputs transparency matching
  obtain ⟨target⟩ := targetMatches.actual_redex_access redex
  have sameParent : copied=target.parent := targetMatches.accessWord_injective
    (sameWord.trans (source.parentWord.trans target.parentWord.symm))
  refine ⟨branch,target,?_,middle,?_,reader⟩
  · rw [←sameParent]
    exact finish
  · rw [←sameParent]
    exact labels
end
end Lamping.AG
