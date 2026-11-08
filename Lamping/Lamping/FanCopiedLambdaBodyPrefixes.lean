import Lamping.Lamping.ActionCopiedLambdaBodyPrefixes
import Lamping.Lamping.FanCopiedLambdaContextCuts
import Lamping.Lamping.ActionPendingLambdaPadding
namespace Lamping.AG
open Graph Lambda Lambda.Labelled
section
variable {K B W : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W]
variable (c : Net signature K (B⊕(Bool⊕Bool)) W) (i j : Nat) (branch : Bool)
local notation "rhs" => fanRight Op.lam i j
local notation "bodySegment" => (Sum.inr (Sum.inl (Sigma.mk (Sum.inl branch) (Sum.inr true))) : PlugSegment c rhs)
local notation "writerSegment" => (Sum.inr (Sum.inl (Sigma.mk (Sum.inr true) (Sum.inl ()))) : PlugSegment c rhs)
local notation "exitSegment" => (Sum.inl (Sum.inr (Sum.inl (Sum.inr (Sum.inr true)))) : PlugSegment c rhs)
/-- Actual typed BODY departure forces these two indexed turns and outside
exit. The short untyped stops are excluded, without completing a partial path. -/
theorem fan_typed_body_prefix {es : List (PlugSegment c rhs)} {a b : Context}
    (labels : PlugLabelling c rhs es a b) (head : es.head?=some bodySegment)
    (typed : ∃k,accessKind (plug c rhs) (es.map (plugEnd c.label (rhs).label))=some k) :
    ∃tail middle,es=bodySegment::writerSegment::exitSegment::tail ∧
      Traversal i (.op .fan) (.inr branch) (.inl ()) a middle ∧
      PlugLabelling c rhs (exitSegment::tail) middle b := by
  cases es with
  | nil => cases head
  | cons e es =>
    have same := Option.some.inj head
    subst e
    cases labels with
    | single => obtain ⟨kind,typed⟩:=typed;cases typed
    | @cons e f es a middle b turn rest =>
      change PlugTurn c rhs (.inr (.inl ⟨.inr true,.inr branch⟩)) f a middle at turn
      cases turn with
      | right step =>
        obtain ⟨port,out,rule⟩ := step.from_node (.inr true) (.inr branch) rfl
        have principal : port=.inl () := rule.control_aux
        subst port
        cases out
        cases es with
        | nil => obtain ⟨kind,typed⟩:=typed;change none=some kind at typed;cases typed
        | cons f es =>
          cases rest with
          | cons next suffix =>
            change PlugTurn c rhs (.inr (.inr (.inl (.inr true)))) f middle _ at next
            cases next with
            | leave => exact ⟨es,middle,rfl,rule,suffix⟩
            | right impossible => cases impossible

/-- The true occurrence and actual copied-parent finish supply the BODYhead;
no fromEndpoint or writer-prefix certificate is supplied by the caller. -/
theorem fan_copied_lambda_body_fragment {current : LTerm} {root : B}
    (matching : Matches (plug c rhs) root current.erase)
    (fragment : SourceEdgeFragment current (plug c rhs) root edge position)
    (role : SourceDeparture parentTerm .body edge.fromPort)
    (parent : RootAccess (plug c rhs) root)
    (word : position=accessWord (plug c rhs) parent.val++[.body])
    (finish : parent.val.getLast?=some ((plug c rhs).wire (.inl ⟨.inr (.inl branch),.inl ()⟩)))
    {a b : Context} (labels : Labelling (plug c rhs) fragment.segments a b) :
    ∃tail middle,fragment.segments.map (plugEnd c.label (rhs).label).invFun=
      bodySegment::writerSegment::exitSegment::tail ∧
      Traversal i (.op .fan) (.inr branch) (.inl ()) a middle ∧
      PlugLabelling c rhs (exitSegment::tail) middle b := by
  have actualStart := actual_lambda_child_head matching fragment role parent word
    (.inr (.inl branch)) (.inl ()) (.inr true) HEq.rfl finish
  have head := fragment.start
  rw [actualStart] at head
  have rawHead : (fragment.segments.map (plugEnd c.label (rhs).label).invFun).head?=some bodySegment := by
    rw [List.head?_map,head];rfl
  apply fan_typed_body_prefix c i j branch (labels.plug_decomposition c rhs) rawHead
  simpa only [plug_decomposition_flatten] using fragment.fragment_typed
end
end Lamping.AG

namespace Lamping.AG
open Graph Lambda Lambda.Labelled
section
variable {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K → Label signature} {i j : Nat} {lt : i<j}
variable (site : PathSite (Schema.fanAction Op.lam i j lt) kept (B:=B) (W:=W) (V:=V))
local notation "cut" => cutFragment site.net (pathPartition (Schema.fanAction Op.lam i j lt) V) site.closed
private abbrev fanBodyRight (i j : Nat) (lt : i<j) := (Schema.fanAction Op.lam i j lt).right.net
local notation "rhs" => fanBodyRight i j lt

/-- The actual copied lambda context permits these specific lambda-body and
low-writer segments. This is not a path completion principle. -/
theorem PendingRhsBlock.fan_lambda_body_path
    {raw : List (PlugSegment cut rhs)} {a b : Context}
    (branch : Bool)
    (pending : PendingRhsBlock cut rhs raw a b)
    (finish : pending.inside.getLast?=some ((rhs).wire (.inl ⟨.inl branch,.inl ()⟩))) :
    ∃ path : LocalPath rhs (.inl branch) (.inr true) b (InitialOffsets.fanAt i branch b),
      pending.inside=[.inr (.inl (.inl branch))] ∧
      pending.enter=.inl branch ∧pending.middle=b ∧
      path.edges=pending.inside++[.inl ⟨.inl branch,.inr true⟩,.inl ⟨.inr true,.inl ()⟩] ∧
      PlugExcursions cut rhs
        (.inl pending.last::(path.edges.map Sum.inr++[.inl (.inr (.inl (.inr (.inr true))))]))
        b (InitialOffsets.fanAt i branch b) ∧
      raw++[.inr (.inl ⟨.inl branch,.inr true⟩),.inr (.inl ⟨.inr true,.inl ()⟩),
        .inl (.inr (.inl (.inr (.inr true))))]=
        pending.pre++(.inl pending.last::(path.edges.map Sum.inr++
          [.inl (.inr (.inl (.inr (.inr true))))])).tail := by
  obtain ⟨entry,shape,contexts⟩ := fanRight_lam_context_prefix i j branch
    pending.enter pending.inside pending.middle b pending.insideLabels pending.insideHead finish
  let path : LocalPath rhs (.inl branch) (.inr true) b (InitialOffsets.fanAt i branch b) := {
    edges := [.inr (.inl (.inl branch)),.inl ⟨.inl branch,.inr true⟩,.inl ⟨.inr true,.inl ()⟩]
    start := rfl
    finish := rfl
    labeling := .cons (LabelledTurn.node (g:=rhs) (.inl branch) _ _ (.direct (.lamBody b)))
      (.cons (LabelledTurn.node (g:=rhs) (.inr true) _ _
        (.direct (InitialOffsets.Event.apply_rel (.fan i branch) b))) (.single _ _)) }
  have arrival : (cut).wire pending.last=.inr (.inl (.inr (.inl branch))) := by
    rw [pending.arrival,entry]
  refine ⟨path,shape,entry,contexts,?_,?_,?_⟩
  · rw [shape]; rfl
  · exact .through path arrival (.single _ _)
  · have eqs := pending.equation
    rw [shape] at eqs
    exact (congrArg (fun xs => xs++[.inr (.inl ⟨.inl branch,.inr true⟩),
      .inr (.inl ⟨.inr true,.inl ()⟩),.inl (.inr (.inl (.inr (.inr true))))]) eqs).trans
      (by simp only [List.append_assoc];rfl)

/-- Join the real pending prefix to its finite padding and construct its
canonical source on the SAME supplied principal. -/
theorem PendingRhsBlock.fan_lambda_body_completion (principal : SiteActionPrincipal site)
    {raw : List (PlugSegment cut rhs)} {a b : Context}
    (branch : Bool)
    (pending : PendingRhsBlock cut rhs raw a b)
    (first : Endpoint cut) (head : raw.head?=some (.inl first))
    (finish : pending.inside.getLast?=some ((rhs).wire (.inl ⟨.inl branch,.inl ()⟩))) :
    ∃ old, ActionCanonicalBlocks site principal
        (raw++[.inr (.inl ⟨.inl branch,.inr true⟩),.inr (.inl ⟨.inr true,.inl ()⟩),
          .inl (.inr (.inl (.inr (.inr true))))]) old ∧
      Labelling site.net old a (InitialOffsets.fanAt i branch b) ∧
      old.head?=some (site.outsideEnd first) ∧
      old.getLast?=some (site.outsideEnd (.inr (.inl (.inr (.inr true))))) ∧
      PlugExcursions cut rhs
        (raw++[.inr (.inl ⟨.inl branch,.inr true⟩),.inr (.inl ⟨.inr true,.inl ()⟩),
          .inl (.inr (.inl (.inr (.inr true))))]) a (InitialOffsets.fanAt i branch b) := by
  obtain ⟨path,shape,entry,contexts,pathEq,rightPath,paddedEq⟩ := pending.fan_lambda_body_path site branch finish
  obtain ⟨before,preEq⟩ := List.getLast?_eq_some_iff.mp pending.prefixLast
  have prePath := pending.prefixPath
  rw [contexts] at prePath
  have joined := prePath.overlap_join cut rhs preEq rightPath
  have whole : PlugExcursions cut rhs
      (raw++[.inr (.inl ⟨.inl branch,.inr true⟩),.inr (.inl ⟨.inr true,.inl ()⟩),
        .inl (.inr (.inl (.inr (.inr true))))]) a (InitialOffsets.fanAt i branch b) := by
    rw [paddedEq]
    simpa only [preEq,List.append_assoc,List.cons_append,List.tail_cons] using joined
  have starts : (raw++[.inr (.inl ⟨.inl branch,.inr true⟩),.inr (.inl ⟨.inr true,.inl ()⟩),
      .inl (.inr (.inl (.inr (.inr true))))] : List (PlugSegment cut rhs)).head?=some (.inl first) := by
    rw [List.head?_append,head,Option.some_or]
  have ends : (raw++[.inr (.inl ⟨.inl branch,.inr true⟩),.inr (.inl ⟨.inr true,.inl ()⟩),
      .inl (.inr (.inl (.inr (.inr true))))] : List (PlugSegment cut rhs)).getLast?=
        some (.inl (.inr (.inl (.inr (.inr true))))) := by
    simp only [List.getLast?_append,List.getLast?_cons_cons,List.getLast?_singleton,Option.some_or]
  obtain ⟨old,relation,labels,start,last⟩ := whole.action_canonical_lift site (.fan .lam i j lt)
    principal first (.inr (.inl (.inr (.inr true)))) starts ends
  exact ⟨old,relation,labels,start,last,whole⟩
end
end Lamping.AG


namespace Lamping.AG
open Graph Lambda
section
variable {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K → Label signature} {i j : Nat} {lt : i<j}
variable (site : PathSite (Schema.fanAction .lam i j lt) kept (B:=B) (W:=W) (V:=V))
local notation "cut" => cutFragment site.net (pathPartition (Schema.fanAction Op.lam i j lt) V) site.closed
private abbrev fanParentRight (i j : Nat) (lt : i<j) := (Schema.fanAction .lam i j lt).right.net
local notation "rhs" => fanParentRight i j lt

/-- Identify the canonical old padding with THIS supplied source access.
The padding labels are constructed from the real writer and lambda-body turn. -/
theorem PathSite.fan_lambda_body_parent_canonical
    {directions : B → Bool} (flow : FlowBalance site.net directions)
    (root : B) (positive : directions root=true) {term : Term}
    (matching : Matches site.net root term) (principal : SiteActionPrincipal site)
    (source : RootAccess site.net root) (target : RootAccess site.reduce root)
    (word : accessWord site.net source.val=accessWord site.reduce target.val)
    (branch : Bool)
    (finish : target.val.getLast?=some (site.reduce.wire (.inl ⟨.inr (.inl branch),.inl ()⟩)))
    {a b : Context} (labels : Labelling site.reduce target.val a b) :
    ActionCanonicalBlocks site principal
      (target.val.map (plugEnd (cut).label (rhs).label).invFun++
        [.inr (.inl ⟨.inl branch,.inr true⟩),.inr (.inl ⟨.inr true,.inl ()⟩),
          .inl (.inr (.inl (.inr (.inr true))))])
      (source.val++[.inl ⟨.inr (.inr ()),.inr true⟩]) ∧
    PlugExcursions cut rhs
      (target.val.map (plugEnd (cut).label (rhs).label).invFun++
        [.inr (.inl ⟨.inl branch,.inr true⟩),.inr (.inl ⟨.inr true,.inl ()⟩),
          .inl (.inr (.inl (.inr (.inr true))))]) a (InitialOffsets.fanAt i branch b) := by
  let first : Endpoint cut := .inr (.inl (.inl root))
  have actualHead : target.val.head?=some (AG.plugLeft cut rhs first) := target.property.2.1
  obtain ⟨pending,insideFinish⟩ := labels.pending_new_node cut rhs first actualHead
    (.inl branch) (.inl ()) finish
  have rawHead : (target.val.map (plugEnd (cut).label (rhs).label).invFun).head?=some (.inl first) := by
    rw [List.head?_map,actualHead]
    exact congrArg some ((plugEnd (cut).label (rhs).label).left_inv (.inl first))
  obtain ⟨entry,shape,contexts⟩ := fanRight_lam_context_prefix i j branch
    pending.enter pending.inside pending.middle b pending.insideLabels pending.insideHead insideFinish
  have rule : Traversal i (.op .fan) (.inr branch) (.inl ()) pending.middle (InitialOffsets.fanAt i branch b) := by
    rw [contexts];exact .direct (InitialOffsets.Event.apply_rel (.fan i branch) b)
  obtain ⟨pre,oldLabels,oldHead,_preLast,oldLast,words⟩ := pending.fixed_principal_ancestor site
    (.fan .lam i j lt) principal first rawHead branch (by rw [entry];rfl)
    (by rw [shape];rfl) rule
  rw [plug_decomposition_flatten] at words
  have rooted : (pre++principal.edges).head?=some (.inr (.inl root)) := by
    rw [List.head?_append,oldHead,Option.some_or];rfl
  have typed : accessKind site.net (pre++principal.edges)=some AccessKind.lam := by
    simp only [accessKind,oldLast,Option.bind_some,Pairing.involutive]
    rfl
  have oldForward := oldLabels.root_forward_of_flow flow root rooted positive
  let oldAccess : RootAccess site.net root :=
    ⟨pre++principal.edges,⟨⟨⟨a,InitialOffsets.fanAt i branch b,oldLabels⟩,oldForward⟩,rooted,⟨_,typed⟩⟩⟩
  have sameAccess : oldAccess=source := matching.accessWord_injective (words.symm.trans word.symm)
  have literal : pre++principal.edges=source.val := congrArg Subtype.val sameAccess
  rw [literal] at oldLabels oldLast
  have padLabels : Labelling site.net (source.val++[.inl ⟨.inr (.inr ()),.inr true⟩]) a
      (InitialOffsets.fanAt i branch b) :=
    oldLabels.append_seam (.single _ _) (by
      intro e f atLast atHead
      have eEq := Option.some.inj (atLast.symm.trans oldLast)
      have fEq := Option.some.inj atHead
      subst e;subst f
      rw [Pairing.involutive]
      exact LabelledTurn.node (g:=site.net) (.inr (.inr ())) _ _ (.direct (.lamBody _)))
  obtain ⟨old,relation,canonLabels,canonHead,canonLast,whole⟩ :=
    pending.fan_lambda_body_completion site principal branch first rawHead insideFinish
  have padHead : (source.val++[.inl ⟨.inr (.inr ()),.inr true⟩] : List (Endpoint site.net)).head?=some (.inr (.inl root)) := by
    rw [List.head?_append,source.property.2.1,Option.some_or]
  have canonRoot : old.head?=some (.inr (.inl root)) := canonHead
  have padLast : (source.val++[.inl ⟨.inr (.inr ()),.inr true⟩] : List (Endpoint site.net)).getLast?=
      some (.inl ⟨.inr (.inr ()),.inr true⟩) := by
    simp only [List.getLast?_append,List.getLast?_singleton,Option.some_or]
  have canonEnd : old.getLast?=some (.inl ⟨.inr (.inr ()),.inr true⟩) := canonLast
  have canonicalForward := canonLabels.root_forward_of_flow flow root canonRoot positive
  have padForward := padLabels.root_forward_of_flow flow root padHead positive
  have same := canonLabels.rooted_terminal_unique site.net canonicalForward canonRoot padLabels padForward padHead
    (canonEnd.trans padLast.symm)
  rw [same.1] at relation
  exact ⟨relation,whole⟩
end
end Lamping.AG
