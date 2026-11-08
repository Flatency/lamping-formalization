import Lamping.Lamping.FanAppCopiedFunctionCuts
import Lamping.Lamping.ActionArgumentPadding
import Lamping.Lamping.ActualFragmentFanUniqueness
namespace Lamping.AG
open Graph Lambda Lambda.Labelled
section
variable {K B W : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W]
variable (c : Net signature K (B⊕(Bool⊕Bool)) W) (i j : Nat) (branch : Bool)
local notation "rhs" => fanRight Op.app i j
local notation "argumentSegment" => (Sum.inr (Sum.inl (Sigma.mk (Sum.inl branch) appArg)) : PlugSegment c rhs)
local notation "writerSegment" => (Sum.inr (Sum.inl (Sigma.mk (Sum.inr true) (Sum.inl ()))) : PlugSegment c rhs)
local notation "exitSegment" => (Sum.inl (Sum.inr (Sum.inl (Sum.inr (Sum.inr true)))) : PlugSegment c rhs)
theorem fan_app_typed_argument_prefix {es : List (PlugSegment c rhs)} {a b : Context}
    (labels : PlugLabelling c rhs es a b) (head : es.head?=some argumentSegment)
    (typed : ∃k,accessKind (plug c rhs) (es.map (plugEnd c.label (rhs).label))=some k) :
    ∃tail middle,es=argumentSegment::writerSegment::exitSegment::tail ∧
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

/-- The true occurrence and actual copied-parent finish supply the ARG head;
no fromEndpoint or writer-prefix certificate is supplied by the caller. -/
theorem fan_app_copied_argument_fragment {current : LTerm} {root : B}
    (matching : Matches (plug c rhs) root current.erase)
    (fragment : SourceEdgeFragment current (plug c rhs) root edge position)
    (role : SourceDeparture parentTerm .arg edge.fromPort)
    (parent : RootAccess (plug c rhs) root)
    (word : position=accessWord (plug c rhs) parent.val++[.arg])
    (finish : parent.val.getLast?=some ((plug c rhs).wire (.inl ⟨.inr (.inl branch),appCtx⟩)))
    {a b : Context} (labels : Labelling (plug c rhs) fragment.segments a b) :
    ∃tail middle,fragment.segments.map (plugEnd c.label (rhs).label).invFun=
      argumentSegment::writerSegment::exitSegment::tail ∧
      Traversal i (.op .fan) (.inr branch) (.inl ()) a middle ∧
      PlugLabelling c rhs (exitSegment::tail) middle b := by
  have actualStart := actual_argument_child_head matching fragment role parent word
    (.inr (.inl branch)) appCtx appArg HEq.rfl finish
  have head := fragment.start
  rw [actualStart] at head
  have rawHead : (fragment.segments.map (plugEnd c.label (rhs).label).invFun).head?=some argumentSegment := by
    rw [List.head?_map,head];rfl
  apply fan_app_typed_argument_prefix c i j branch (labels.plug_decomposition c rhs) rawHead
  simpa only [plug_decomposition_flatten] using fragment.fragment_typed
theorem PendingRhsBlock.fan_app_argument_padding
    {raw : List (PlugSegment c rhs)} {a b : Context}
    (pending : PendingRhsBlock c rhs raw a b)
    (finish : pending.inside.getLast?=some ((rhs).wire (.inl ⟨.inl branch,appCtx⟩))) :
    ∃ path : LocalPath rhs (.inr false) (.inr true) pending.middle pending.middle,
      pending.enter=.inr false ∧
      path.edges=pending.inside++[.inl ⟨.inl branch,appArg⟩,.inl ⟨.inr true,.inl ()⟩] ∧
      PlugExcursions c rhs
        (.inl pending.last::(path.edges.map Sum.inr++[.inl (.inr (.inl (.inr (.inr true))))]))
        pending.middle pending.middle ∧
      raw++[.inr (.inl ⟨.inl branch,appArg⟩),.inr (.inl ⟨.inr true,.inl ()⟩),
        .inl (.inr (.inl (.inr (.inr true))))]=
        pending.pre++((.inl pending.last::(path.edges.map (Sum.inr : Endpoint rhs → PlugSegment c rhs)++
          [.inl (.inr (.inl (.inr (.inr true))))])) : List (PlugSegment c rhs)).tail := by
  obtain ⟨entry,shape,rule⟩ := fanRight_app_context_prefix i j branch
    pending.enter pending.inside pending.middle b pending.insideLabels pending.insideHead finish
  let path : LocalPath rhs (.inr false) (.inr true) pending.middle pending.middle := {
    edges := [.inr (.inl (.inr false)),.inl ⟨.inr false,.inr branch⟩,
      .inl ⟨.inl branch,appArg⟩,.inl ⟨.inr true,.inl ()⟩]
    start := rfl
    finish := rfl
    labeling := .cons (LabelledTurn.node (g:=rhs) (.inr false) _ _ rule)
      (.cons (LabelledTurn.node (g:=rhs) (.inl branch) _ _ (.direct (.appArg b)))
        (.cons (LabelledTurn.node (g:=rhs) (.inr true) _ _ rule.reverse) (.single _ _))) }
  have arrival : c.wire pending.last=.inr (.inl (.inr (.inr false))) := by
    rw [pending.arrival,entry]
  refine ⟨path,entry,?_,?_,?_⟩
  · rw [shape];rfl
  · exact .through path arrival (.single _ _)
  · have eqs := pending.equation
    rw [shape] at eqs
    exact (congrArg (fun xs=>xs++[.inr (.inl ⟨.inl branch,appArg⟩),
      .inr (.inl ⟨.inr true,.inl ()⟩),.inl (.inr (.inl (.inr (.inr true))))]) eqs).trans
      (by simp only [List.append_assoc];rfl)
end
section
variable {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K→Label signature} {i j : Nat} {lt : i<j}
variable (site : PathSite (.fanAction .app i j lt) kept (B:=B) (W:=W) (V:=V))
local notation "cut" => cutFragment site.net (pathPartition (Schema.fanAction Op.app i j lt) V) site.closed
private abbrev argumentFanRight (i j : Nat) (lt : i<j) := (Schema.fanAction Op.app i j lt).right.net
local notation "rhs" => argumentFanRight i j lt
theorem PathSite.fan_app_argument_padding_access
    {directions : B → Bool} (flow : FlowBalance site.net directions)
    (root : B) (positive : directions root=true) {term : Term}
    (matching : Matches site.net root term) (principal : SiteActionPrincipal site)
    (source : RootAccess site.net root) (target : RootAccess site.reduce root)
    (word : accessWord site.net source.val=accessWord site.reduce target.val)
    (branch : Bool)
    (finish : target.val.getLast?=some (site.reduce.wire (.inl ⟨.inr (.inl branch),appCtx⟩)))
    {a b : Context} (labels : Labelling site.reduce target.val a b) :
    ActionCanonicalBlocks site principal
      (target.val.map (plugEnd (cut).label (rhs).label).invFun++
        [.inr (.inl ⟨.inl branch,appArg⟩),.inr (.inl ⟨.inr true,.inl ()⟩),
          .inl (.inr (.inl (.inr (.inr true))))])
      (source.val++[.inl ⟨.inr (.inr ()),appArg⟩]) := by
  obtain ⟨pending,_preRelation,oldLabels,oldFinish,_shape⟩ :=
    site.fan_aux_canonical_access flow root positive matching principal source target word branch false finish labels
  change PendingRhsBlock cut rhs (target.val.map (plugEnd (cut).label (rhs).label).invFun) a b at pending
  let first : Endpoint cut := .inr (.inl (.inl root))
  have actualHead : target.val.head?=some (AG.plugLeft cut rhs first) := target.property.2.1
  have rawHead : (target.val.map (plugEnd (cut).label (rhs).label).invFun).head?=some (.inl first) := by
    rw [List.head?_map,actualHead]
    exact congrArg some ((plugEnd (cut).label (rhs).label).left_inv (.inl first))
  have insideFinish : pending.inside.getLast?=some ((rhs).wire (.inl ⟨.inl branch,appCtx⟩)) := by
    apply pending.inside_finish cut rhs ((rhs).wire (.inl ⟨.inl branch,appCtx⟩))
    rw [List.getLast?_map,finish]
    change some ((plugEnd (cut).label (rhs).label).invFun
      ((plug cut rhs).wire (.inl ⟨.inr (.inl branch),appCtx⟩)))=_
    rw [plugSegmentWire_inverse];rfl
  obtain ⟨path,_entry,_pathEq,rightPath,paddedEq⟩ := pending.fan_app_argument_padding cut i j branch insideFinish
  obtain ⟨before,preEq⟩ := List.getLast?_eq_some_iff.mp pending.prefixLast
  have joined := pending.prefixPath.overlap_join cut rhs preEq rightPath
  have whole : PlugExcursions cut rhs
      (target.val.map (plugEnd (cut).label (rhs).label).invFun++
        [.inr (.inl ⟨.inl branch,appArg⟩),.inr (.inl ⟨.inr true,.inl ()⟩),
          .inl (.inr (.inl (.inr (.inr true))))]) a pending.middle := by
    rw [paddedEq]
    simpa only [preEq,List.append_assoc,List.cons_append,List.tail_cons] using joined
  have starts : (target.val.map (plugEnd (cut).label (rhs).label).invFun++
        [.inr (.inl ⟨.inl branch,appArg⟩),.inr (.inl ⟨.inr true,.inl ()⟩),
          .inl (.inr (.inl (.inr (.inr true))))] : List (PlugSegment cut rhs)).head?=some (.inl first) := by
    rw [List.head?_append,rawHead,Option.some_or]
  have ends : (target.val.map (plugEnd (cut).label (rhs).label).invFun++
        [.inr (.inl ⟨.inl branch,appArg⟩),.inr (.inl ⟨.inr true,.inl ()⟩),
          .inl (.inr (.inl (.inr (.inr true))))] : List (PlugSegment cut rhs)).getLast?=
        some (.inl (.inr (.inl (.inr (.inr true))))) := by
    simp only [List.getLast?_append,List.getLast?_cons_cons,List.getLast?_singleton,Option.some_or]
  obtain ⟨old,relation,canonLabels,canonHead,canonLast⟩ := whole.action_canonical_lift site
    (.fan .app i j lt) principal first (.inr (.inl (.inr (.inr true)))) starts ends
  let oldArg : Endpoint site.net := .inl ⟨.inr (.inr ()),appArg⟩
  have padLabels : Labelling site.net (source.val++[oldArg]) a pending.middle := by
    exact oldLabels.append_seam (.single oldArg pending.middle) (by
      intro e f last head
      have eEq:=Option.some.inj (last.symm.trans oldFinish)
      have fEq:=Option.some.inj head
      subst e;subst f
      rw [Pairing.involutive]
      exact LabelledTurn.node (g:=site.net) (.inr (.inr ())) appCtx appArg
        (.direct (.appArg pending.middle)))
  have padHead : (source.val++[oldArg]).head?=some (.inr (.inl root)) := by
    rw [List.head?_append,source.property.2.1,Option.some_or]
  have padLast : (source.val++[oldArg]).getLast?=some oldArg := by
    simp only [List.getLast?_append,List.getLast?_singleton,Option.some_or]
  have canonRoot : old.head?=some (.inr (.inl root)) := canonHead
  have canonEnd : old.getLast?=some oldArg := canonLast
  have same := canonLabels.rooted_terminal_unique site.net
    (canonLabels.root_forward_of_flow flow root canonRoot positive) canonRoot padLabels
    (padLabels.root_forward_of_flow flow root padHead positive) padHead (canonEnd.trans padLast.symm)
  rw [same.1] at relation
  exact relation
local notation "argumentSegment" branch => (Sum.inr (Sum.inl (Sigma.mk (Sum.inl branch) appArg)) : PlugSegment cut rhs)
local notation "writerSegment" => (Sum.inr (Sum.inl (Sigma.mk (Sum.inr true) (Sum.inl ()))) : PlugSegment cut rhs)
local notation "exitPivot" => (Sum.inr (Sum.inl (Sum.inr (Sum.inr true))) : Endpoint cut)
local notation "oldArgument" => (Sum.inl (Sigma.mk (Sum.inr (Sum.inr ())) appArg) : Endpoint site.net)
theorem SourceEdgeFragment.fan_app_copied_argument_kept_cut
    {directions : B → Bool} (flow : FlowBalance site.net directions)
    (root : B) (positive : directions root=true) {current : LTerm}
    (sourceMatches : Matches site.net root current.erase) (targetMatches : Matches site.reduce root current.erase)
    (principal : SiteActionPrincipal site) {edge : SourceEdge} {position : Path}
    (source : SourceEdgeFragment current site.net root edge position)
    (target : SourceEdgeFragment current site.reduce root edge position)
    (role : SourceDeparture parentTerm .arg edge.fromPort)
    (sourceParent : RootAccess site.net root) (targetParent : RootAccess site.reduce root)
    (sourceWord : position=accessWord site.net sourceParent.val++[.arg])
    (targetWord : position=accessWord site.reduce targetParent.val++[.arg])
    (branch : Bool)
    (parentFinish : targetParent.val.getLast?=some (site.reduce.wire (.inl ⟨.inr (.inl branch),appCtx⟩)))
    (endNode : K) (endPort : Port (kept endNode).sort)
    (endAt : target.access.val.getLast?=some (site.reduce.wire (.inl ⟨.inl endNode,endPort⟩)))
    {a b : Context} (wholeLabels : Labelling site.reduce target.access.val a b) :
    ∃ rawTail oldTail seam,
      target.segments.map (plugEnd (cut).label (rhs).label).invFun=
        (argumentSegment branch)::writerSegment::Sum.inl exitPivot::rawTail ∧
      source.segments=oldArgument::oldTail ∧
      ActionCanonicalBlocks site principal (Sum.inl exitPivot::rawTail)
        (site.outsideEnd exitPivot::oldTail) ∧
      PlugLabelling cut rhs (Sum.inl exitPivot::rawTail) seam b := by
  have targetCut := target.child_prefix targetMatches role targetParent targetWord
  obtain ⟨pieceInput,_prefixLabels,pieceLabels⟩ := target.assignments a b wholeLabels
  obtain ⟨rawTail,_writerOutput,targetShape,_writerRule,_tailLabels⟩ := fan_app_copied_argument_fragment cut i j branch targetMatches target role targetParent targetWord parentFinish pieceLabels
  change List (PlugSegment cut rhs) at rawTail
  change target.segments.map (plugEnd (cut).label (rhs).label).invFun=
    (argumentSegment branch)::writerSegment::Sum.inl exitPivot::rawTail at targetShape
  obtain ⟨whole,_sourceWholeLabels,_sourceEnd⟩ := site.action_kept_canonical_access (.fan .app i j lt)
    flow root positive sourceMatches principal source.access target.access
    (source.word.trans target.word.symm) endNode endPort endAt wholeLabels
  obtain ⟨c,d,parentLabels⟩ := targetParent.property.1.1
  have parentWord : accessWord site.net sourceParent.val=accessWord site.reduce targetParent.val :=
    List.append_cancel_right (sourceWord.symm.trans targetWord)
  have parent := site.fan_app_argument_padding_access flow root positive sourceMatches principal
    sourceParent targetParent parentWord branch parentFinish parentLabels
  have rawSplit : target.access.val.map (plugEnd (cut).label (rhs).label).invFun=
      (targetParent.val.map (plugEnd (cut).label (rhs).label).invFun++
        [(argumentSegment branch),writerSegment,Sum.inl exitPivot])++rawTail := by
    rw [targetCut.2,List.map_append,targetShape]
    simp only [List.append_assoc,List.cons_append,List.nil_append]
  have parentLast : (targetParent.val.map (plugEnd (cut).label (rhs).label).invFun++
      [(argumentSegment branch),writerSegment,Sum.inl exitPivot]).getLast?=some (Sum.inl exitPivot) := by
    simp only [List.getLast?_append,List.getLast?_cons_cons,List.getLast?_singleton,Option.some_or]
  obtain ⟨oldTail,seam,oldSplit,relation,_actualParentLabels,actualPieceLabels⟩ :=
    whole.cut_at_raw_parent site parent (wholeLabels.plug_decomposition cut rhs) rawSplit exitPivot parentLast
  have sourceCut := source.child_prefix sourceMatches role sourceParent sourceWord
  have sourceShape : source.segments=oldArgument::oldTail := by
    apply List.append_cancel_left (as:=sourceParent.val)
    rw [←sourceCut.2,oldSplit]
    simp only [List.append_assoc,List.singleton_append]
  exact ⟨rawTail,oldTail,seam,targetShape,sourceShape,relation,actualPieceLabels⟩


end
end Lamping.AG

#print axioms Lamping.AG.fan_app_typed_argument_prefix

#print axioms Lamping.AG.fan_app_copied_argument_fragment

#print axioms Lamping.AG.PendingRhsBlock.fan_app_argument_padding

#print axioms Lamping.AG.PathSite.fan_app_argument_padding_access

#print axioms Lamping.AG.SourceEdgeFragment.fan_app_copied_argument_kept_cut
