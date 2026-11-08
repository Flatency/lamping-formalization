import Lamping.Lambda.Labels
import Lamping.Lamping.SourceActionLambdaAccess
import Lamping.Lamping.ActionMatching
import Lamping.Lamping.MatchingRedexEndpointUniqueness

namespace Lamping.AG
open Graph Lambda Lambda.Labelled
section
variable {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K → Graph.Label signature} {i j : Nat} {lt : i<j}
variable (site : PathSite (.croAction .lam i j lt) kept (B:=B) (W:=W) (V:=V))
local notation "schema" => Schema.croAction Op.lam i j lt
local notation "cut" => cutFragment site.net (pathPartition schema V) site.closed
local notation "rhs" => unaryRightCore Op.cro Op.lam (Bij.refl Unit) i (j-1)
local notation "oldAux" => (Sum.inl (Sigma.mk (Sum.inr (Sum.inl ())) (Sum.inr ())) : Endpoint site.net)
local notation "oldLambda" => (Sum.inl (Sigma.mk (Sum.inr (Sum.inr ())) (Sum.inl ())) : Endpoint site.net)
local notation "copiedLambda" => (Sum.inl (Sigma.mk (Sum.inr (Sum.inl ())) (Sum.inl ())) : Endpoint site.reduce)

/-- Construct the actual copied-lambda finish and retain the old terminal
writer. The new output is the actual middle, not a postulated old seam. -/
theorem PathSite.cro_lam_terminal_writer_access
    {root : B} {term : Term} {directions : B → Bool}
    (matching : Matches site.net root term) (inputs : RootInputs site.net root)
    (flow : FlowBalance site.net directions) (positive : directions root=true)
    (source : RootAccess site.net root)
    (finish : source.val.getLast?=some (site.net.wire oldLambda))
    {a b : Context} (sourceLabels : Labelling site.net source.val a b) :
    ∃ (principal : SiteActionPrincipal site) (pre : List (Endpoint site.net))
      (middle : Context) (copied : RootAccess site.reduce root),
      source.val=pre++principal.edges ∧
      pre.head?=some (Sum.inr (Sum.inl root)) ∧
      pre.getLast?=some (site.net.wire oldAux) ∧
      Labelling site.net pre a middle ∧
      accessWord site.reduce copied.val=accessWord site.net source.val ∧
      copied.val.getLast?=some (site.reduce.wire copiedLambda) ∧
      Labelling site.reduce copied.val a middle ∧
      Traversal i (.op .cro) (Sum.inr ()) (Sum.inl ()) middle b := by
  obtain ⟨principal⟩ := site.actionPrincipal_exists
  obtain ⟨pre,q,middle,split,preRoot,preLast,preLabels,writer⟩ :=
    site.rooted_control_writer_suffix principal sourceLabels root source.property.2.1 finish
  cases q
  let inside : List (Endpoint rhs) := [Sum.inr (Sum.inl (Sum.inl ()))]
  obtain ⟨actual,actualLabels,actualRoot,actualLast,word⟩ :=
    site.source_pending_expansion (.cro .lam i j lt) matching inputs flow positive
      preLabels preRoot (Sum.inl ()) preLast inside (.single _ middle) rfl
  have copiedFinish : actual.getLast?=some (site.reduce.wire copiedLambda) := by
    change actual.getLast?=some (AG.plugRight cut rhs (Sum.inr (Sum.inl (Sum.inl ()))))
    simpa only [inside,List.getLast?_singleton,Option.map_some] using actualLast
  have kindPreserved : accessKind site.reduce actual=accessKind site.net source.val := by
    simp only [accessKind,copiedFinish,finish,Option.bind_some,Pairing.involutive]
    rfl
  obtain ⟨newFlow⟩ := site.reduce_flowBalance flow
  have forward := actualLabels.root_forward_of_flow newFlow root actualRoot positive
  have typed : ∃ kind,accessKind site.reduce actual=some kind := by
    rw [kindPreserved]
    exact source.property.2.2
  have noTokens : accessTokens (schema).right.net inside=[] := by
    change accessTokens rhs inside=[]
    rfl
  rw [noTokens,List.append_nil] at word
  have routeTokens := principal.tokens_empty site (.cro .lam i j lt)
  change principal.edges.flatMap (arrivalWord site.net)=[] at routeTokens
  have sourceWord : accessWord site.net source.val=accessWord site.net pre := by
    rw [split,accessWord_append site.net pre principal.edges preLabels.nonempty,routeTokens,List.append_nil]
  let copied : RootAccess site.reduce root :=
    ⟨actual,⟨⟨⟨a,middle,actualLabels⟩,forward⟩,actualRoot,typed⟩⟩
  exact ⟨principal,pre,middle,copied,split,preRoot,preLast,preLabels,
    word.trans sourceWord.symm,copiedFinish,actualLabels,writer⟩

/-- Attach the constructed copied lambda to THIS actual current/redex child.
Its output middle and the writer back to the original b are both retained. -/
theorem ActualRedexAccess.cro_lam_terminal_writer_child
    {root : B} {current : LTerm} {redex : RedexOcc current.erase}
    (source : ActualRedexAccess site.net root redex)
    {directions : B → Bool} {depths : B → Int}
    (matching : Matches site.net root current.erase) (inputs : RootInputs site.net root)
    (flow : FlowBalance site.net directions) (positive : directions root=true)
    (balance : IndexedLevelBalance site.net depths) (rootDepth : depths root=0)
    (transparency : Transparency site.net root)
    (finish : source.child.val.getLast?=some (site.net.wire oldLambda))
    {a b : Context} (sourceLabels : Labelling site.net source.child.val a b) :
    ∃ (target : ActualRedexAccess site.reduce root redex) (principal : SiteActionPrincipal site)
      (pre : List (Endpoint site.net)) (middle : Context),
      source.child.val=pre++principal.edges ∧
      Labelling site.net pre a middle ∧
      Labelling site.reduce target.child.val a middle ∧
      target.child.val.getLast?=some (site.reduce.wire copiedLambda) ∧
      Traversal i (.op .cro) (Sum.inr ()) (Sum.inl ()) middle b := by
  obtain ⟨principal,pre,middle,copied,split,_preRoot,_preLast,preLabels,sameWord,
      copiedFinish,copiedLabels,writer⟩ :=
    site.cro_lam_terminal_writer_access matching inputs flow positive source.child finish sourceLabels
  have targetMatches := site.action_matches_rootInputs (.cro .lam i j lt)
    flow root positive balance rootDepth inputs transparency matching
  obtain ⟨target⟩ := targetMatches.actual_redex_access redex
  have sameChild : copied=target.child := targetMatches.accessWord_injective
    (sameWord.trans (source.childWord.trans target.childWord.symm))
  refine ⟨target,principal,pre,middle,split,preLabels,?_,?_,writer⟩
  · rw [←sameChild]
    exact copiedLabels
  · rw [←sameChild]
    exact copiedFinish
end
end Lamping.AG
