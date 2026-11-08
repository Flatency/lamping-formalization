import Lamping.Lamping.SourceActionLambdaAccess
import Lamping.Lamping.ActionMatching
import Lamping.Lamping.MatchingRedexEndpointUniqueness
import Lamping.Lambda.Labels

namespace Lamping.AG
open Graph Lambda Lambda.Labelled
section
variable {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K → Graph.Label signature} {i j : Nat} {lt : i<j}
variable (site : PathSite (.braAction .lam i j lt) kept (B:=B) (W:=W) (V:=V))
local notation "schema" => Schema.braAction Op.lam i j lt
local notation "cut" => cutFragment site.net (pathPartition schema V) site.closed
local notation "rhs" => unaryRightCore Op.bra Op.lam (Bij.refl Unit) i (j+1)
local notation "oldWriter" => (Sum.inl (Sigma.mk (Sum.inr (Sum.inl ())) (Sum.inr ())) : Endpoint site.net)
local notation "oldLambda" => (Sum.inl (Sigma.mk (Sum.inr (Sum.inr ())) (Sum.inl ())) : Endpoint site.net)
local notation "newLambda" => (Sum.inl (Sigma.mk (Sum.inr (Sum.inl ())) (Sum.inl ())) : Endpoint site.reduce)

/-- Retain the actual terminal writer and its middle context while constructing
the copied lambda. The original output b belongs to the removed writer. -/
theorem PathSite.bra_lam_terminal_writer_access
    {root : B} {term : Term} {directions : B → Bool}
    (matching : Matches site.net root term) (inputs : RootInputs site.net root)
    (flow : FlowBalance site.net directions) (positive : directions root=true)
    (source : RootAccess site.net root)
    (finish : source.val.getLast?=some (site.net.wire oldLambda))
    {a b : Context} (labels : Labelling site.net source.val a b) :
    ∃ (principal : SiteActionPrincipal site) (oldPre : List (Endpoint site.net))
      (middle : Context) (copied : RootAccess site.reduce root),
      source.val=oldPre++principal.edges ∧
      Labelling site.net oldPre a middle ∧
      accessWord site.reduce copied.val=accessWord site.net source.val ∧
      copied.val.getLast?=some (site.reduce.wire newLambda) ∧
      Labelling site.reduce copied.val a middle ∧
      Traversal i (.op .bra) (Sum.inr ()) (Sum.inl ()) middle b := by
  obtain ⟨principal⟩ := site.actionPrincipal_exists
  obtain ⟨oldPre,q,middle,split,head,last,oldLabels,writer⟩ :=
    site.rooted_control_writer_suffix principal labels root source.property.2.1 finish
  cases q
  let inside : List (Endpoint rhs) := [Sum.inr (Sum.inl (Sum.inl ()))]
  obtain ⟨actual,newLabels,newHead,newLast,word⟩ :=
    site.source_pending_expansion (.bra .lam i j lt) matching inputs flow positive
      oldLabels head (Sum.inl ()) last inside (.single _ middle) rfl
  have copiedFinish : actual.getLast?=some (site.reduce.wire newLambda) := by
    change actual.getLast?=some (AG.plugRight cut rhs (Sum.inr (Sum.inl (Sum.inl ()))))
    simpa only [inside,List.getLast?_singleton,Option.map_some] using newLast
  have kind : accessKind site.reduce actual=accessKind site.net source.val := by
    simp only [accessKind,copiedFinish,finish,Option.bind_some,Pairing.involutive]
    rfl
  obtain ⟨newFlow⟩ := site.reduce_flowBalance flow
  have forward := newLabels.root_forward_of_flow newFlow root newHead positive
  have typed : ∃ k,accessKind site.reduce actual=some k := by
    rw [kind]
    exact source.property.2.2
  have noTokens : accessTokens (schema).right.net inside=[] := by
    change accessTokens rhs inside=[]
    rfl
  rw [noTokens,List.append_nil] at word
  have principalTokens := principal.tokens_empty site (.bra .lam i j lt)
  change principal.edges.flatMap (arrivalWord site.net)=[] at principalTokens
  have originalWord : accessWord site.net source.val=accessWord site.net oldPre := by
    rw [split,accessWord_append site.net oldPre principal.edges oldLabels.nonempty,
      principalTokens,List.append_nil]
  let copied : RootAccess site.reduce root :=
    ⟨actual,⟨⟨⟨a,middle,newLabels⟩,forward⟩,newHead,typed⟩⟩
  exact ⟨principal,oldPre,middle,copied,split,oldLabels,
    word.trans originalWord.symm,copiedFinish,newLabels,writer⟩

/-- The copied lambda is the child of this same current syntax redex.
The result preserves a→middle and the actual old middle→b writer. -/
theorem ActualRedexAccess.bra_lam_terminal_writer_child
    {root : B} {current : LTerm} {redex : RedexOcc current.erase}
    (source : ActualRedexAccess site.net root redex)
    {directions : B → Bool} {depths : B → Int}
    (matching : Matches site.net root current.erase) (inputs : RootInputs site.net root)
    (flow : FlowBalance site.net directions) (positive : directions root=true)
    (balance : IndexedLevelBalance site.net depths) (rootDepth : depths root=0)
    (transparency : Transparency site.net root)
    (finish : source.child.val.getLast?=some (site.net.wire oldLambda))
    {a b : Context} (labels : Labelling site.net source.child.val a b) :
    ∃ (target : ActualRedexAccess site.reduce root redex) (principal : SiteActionPrincipal site)
      (oldPre : List (Endpoint site.net)) (middle : Context),
      source.child.val=oldPre++principal.edges ∧
      Labelling site.net oldPre a middle ∧
      Labelling site.reduce target.child.val a middle ∧
      target.child.val.getLast?=some (site.reduce.wire newLambda) ∧
      Traversal i (.op .bra) (Sum.inr ()) (Sum.inl ()) middle b := by
  obtain ⟨principal,oldPre,middle,copied,split,oldLabels,word,finishCopy,newLabels,writer⟩ :=
    site.bra_lam_terminal_writer_access matching inputs flow positive source.child finish labels
  have matchingTarget := site.action_matches_rootInputs (.bra .lam i j lt)
    flow root positive balance rootDepth inputs transparency matching
  obtain ⟨target⟩ := matchingTarget.actual_redex_access redex
  have child : copied=target.child := matchingTarget.accessWord_injective
    (word.trans (source.childWord.trans target.childWord.symm))
  refine ⟨target,principal,oldPre,middle,split,oldLabels,?_,?_,writer⟩
  · rw [←child]
    exact newLabels
  · rw [←child]
    exact finishCopy
end
end Lamping.AG
