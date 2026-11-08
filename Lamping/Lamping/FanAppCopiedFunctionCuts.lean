import Lamping.Lamping.FanCopiedBindingCuts
import Lamping.Lamping.ActionRawOutsideCut
import Lamping.Lamping.ActionFunctionPadding
import Lamping.Lamping.ActionCopiedFunctionPrefixes
namespace Lamping.AG
open Graph Lambda Lambda.Labelled
section
variable {K B W : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W]
variable (c : Net signature K (B⊕(Bool⊕Bool)) W) (i j : Nat)
local notation "rhs" => fanRight Op.app i j
theorem PendingRhsBlock.fan_app_function_padding (branch : Bool)
    {raw : List (PlugSegment c rhs)} {a b : Context}
    (pending : PendingRhsBlock c rhs raw a b)
    (finish : pending.inside.getLast?=some ((rhs).wire (.inl ⟨.inl branch,appCtx⟩))) :
    ∃ path : LocalPath rhs (.inr false) (.inl branch) pending.middle b,
      pending.enter=.inr false ∧
      path.edges=pending.inside++[.inl ⟨.inl branch,(Sum.inl ())⟩] ∧
      PlugExcursions c rhs
        (.inl pending.last::(path.edges.map Sum.inr++[.inl (.inr (.inl (.inr (.inl branch))))]))
        pending.middle b ∧
      raw++[.inr (.inl ⟨.inl branch,(Sum.inl ())⟩),.inl (.inr (.inl (.inr (.inl branch))))] =
        pending.pre++((.inl pending.last::(path.edges.map (Sum.inr : Endpoint rhs → PlugSegment c rhs)++
          [.inl (.inr (.inl (.inr (.inl branch))))] )) : List (PlugSegment c rhs)).tail := by
  obtain ⟨entry,shape,rule⟩ := fanRight_app_context_prefix i j branch
    pending.enter pending.inside pending.middle b pending.insideLabels pending.insideHead finish
  let path : LocalPath rhs (.inr false) (.inl branch) pending.middle b := {
    edges := [.inr (.inl (.inr false)),.inl ⟨.inr false,.inr branch⟩,
      .inl ⟨.inl branch,(Sum.inl ())⟩]
    start := rfl
    finish := rfl
    labeling := .cons (LabelledTurn.node (g:=rhs) (.inr false) _ _ rule)
      (.cons (LabelledTurn.node (g:=rhs) (.inl branch) _ _ (show Traversal j (.op .app) appCtx (Sum.inl ()) b b from .direct (.appFun b))) (.single _ _)) }
  have arrival : c.wire pending.last=.inr (.inl (.inr (.inr false))) := by
    rw [pending.arrival,entry]
  refine ⟨path,entry,?_,?_,?_⟩
  · rw [shape];rfl
  · exact .through path arrival (.single _ _)
  · have eqs := pending.equation
    rw [shape] at eqs
    exact (congrArg (fun xs => xs++[.inr (.inl ⟨.inl branch,(Sum.inl ())⟩),
      .inl (.inr (.inl (.inr (.inl branch))))] ) eqs).trans
      (by simp only [List.append_assoc];rfl)
end
section
variable {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K → Label signature} {i j : Nat} {lt : i<j}
variable (site : PathSite (Schema.fanAction Op.app i j lt) kept (B:=B) (W:=W) (V:=V))
local notation "cut" => cutFragment site.net (pathPartition (Schema.fanAction Op.app i j lt) V) site.closed
local notation "rhs" => fanRight Op.app i j
theorem PendingRhsBlock.fan_app_function_canonical_completion (principal : SiteActionPrincipal site) (branch : Bool)
    {raw : List (PlugSegment cut rhs)} {a b : Context}
    (pending : PendingRhsBlock cut rhs raw a b)
    (first : Endpoint cut) (head : raw.head?=some (.inl first))
    (finish : pending.inside.getLast?=some ((rhs).wire (.inl ⟨.inl branch,appCtx⟩))) :
    ∃ old, ActionCanonicalBlocks site principal
        (raw++[.inr (.inl ⟨.inl branch,.inl ()⟩),.inl (.inr (.inl (.inr (.inl branch))))] ) old ∧
      Labelling site.net old a b ∧old.head?=some (site.outsideEnd first) ∧
      old.getLast?=some (site.outsideEnd (.inr (.inl (.inr (.inl branch))))) ∧
      PlugExcursions cut rhs
        (raw++[.inr (.inl ⟨.inl branch,.inl ()⟩),.inl (.inr (.inl (.inr (.inl branch))))] ) a b := by
  obtain ⟨path,_,pathEq,rightPath,paddedEq⟩ := pending.fan_app_function_padding cut i j branch finish
  obtain ⟨before,preEq⟩ := List.getLast?_eq_some_iff.mp pending.prefixLast
  have joined := pending.prefixPath.overlap_join cut rhs preEq rightPath
  have whole : PlugExcursions cut rhs
      (raw++[.inr (.inl ⟨.inl branch,.inl ()⟩),.inl (.inr (.inl (.inr (.inl branch))))] ) a b := by
    rw [paddedEq]
    simpa only [preEq,List.append_assoc,List.cons_append,List.tail_cons] using joined
  have starts : (raw++[.inr (.inl ⟨.inl branch,.inl ()⟩),
      .inl (.inr (.inl (.inr (.inl branch))))] : List (PlugSegment cut rhs)).head?=some (.inl first) := by
    rw [List.head?_append,head,Option.some_or]
  have ends : (raw++[.inr (.inl ⟨.inl branch,.inl ()⟩),
      .inl (.inr (.inl (.inr (.inl branch))))] : List (PlugSegment cut rhs)).getLast?=
      some (.inl (.inr (.inl (.inr (.inl branch))))) := by
    simp only [List.getLast?_append,List.getLast?_cons_cons,List.getLast?_singleton,Option.some_or]
  obtain ⟨old,relation,labels,start,last⟩ := whole.action_canonical_lift site (.fan .app i j lt)
    principal first (.inr (.inl (.inr (.inl branch)))) starts ends
  exact ⟨old,relation,labels,start,last,whole⟩
theorem PathSite.fan_app_function_padding_access
    {directions : B → Bool} (flow : FlowBalance site.net directions)
    (root : B) (positive : directions root=true) {term : Lambda.Term}
    (matching : Matches site.net root term) (principal : SiteActionPrincipal site)
    (source : RootAccess site.net root) (target : RootAccess site.reduce root)
    (word : accessWord site.net source.val=accessWord site.reduce target.val)
    (branch : Bool)
    (finish : target.val.getLast?=some (site.reduce.wire (.inl ⟨.inr (.inl branch),appCtx⟩)))
    {a b : Context} (labels : Labelling site.reduce target.val a b) :
    ActionCanonicalBlocks site principal
      (target.val.map (plugEnd (cut).label (rhs).label).invFun++
        [.inr (.inl ⟨.inl branch,.inl ()⟩),.inl (.inr (.inl (.inr (.inl branch))))] )
      (source.val++reverseEdges principal.edges++[.inl ⟨.inr (.inl ()),.inr branch⟩]) := by
  obtain ⟨pending,_preRelation,oldLabels,oldFinish,_shape⟩ :=
    site.fan_aux_canonical_access flow root positive matching principal source target word branch false finish labels
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
    rw [plugSegmentWire_inverse]
    rfl
  obtain ⟨entry,_shape2,rule⟩ := fanRight_app_context_prefix i j branch pending.enter pending.inside pending.middle b pending.insideLabels pending.insideHead insideFinish
  have routeHead : (reverseEdges principal.edges).head?=some (.inl ⟨.inr (.inr ()),.inl ()⟩) := by
    simp only [reverseEdges,List.head?_map,List.head?_reverse,principal.last,Option.map_some,Pairing.involutive]
  have routeLast : (reverseEdges principal.edges).getLast?=
      some (site.net.wire (.inl ⟨.inr (.inl ()),.inl ()⟩)) := by
    simp only [reverseEdges,List.getLast?_map,List.getLast?_reverse,principal.first,Option.map_some]
  have crossing := principal_crossing_labels site.net (.inr (.inr ())) (.inr (.inl ()))
    appCtx (.inl ()) (.inl ()) (.inr branch) (reverseEdges principal.edges) routeHead routeLast
    (transparent_reverse_turns principal.edges principal.transparent) (Traversal.direct (.appFun pending.middle)) rule
  obtain ⟨before,sourceSplit⟩ := List.getLast?_eq_some_iff.mp oldFinish
  have padLabels : Labelling site.net
      (source.val++reverseEdges principal.edges++[.inl ⟨.inr (.inl ()),.inr branch⟩]) a b := by
    rw [sourceSplit] at oldLabels ⊢
    have joined := oldLabels.join crossing
    simpa only [List.append_assoc,List.singleton_append] using joined
  obtain ⟨old,relation,canonLabels,canonHead,canonLast,_whole⟩ :=
    pending.fan_app_function_canonical_completion site principal branch first rawHead insideFinish
  have padHead : (source.val++reverseEdges principal.edges++[.inl ⟨.inr (.inl ()),.inr branch⟩] :
      List (Endpoint site.net)).head?=some (.inr (.inl root)) := by
    rw [List.head?_append,List.head?_append,source.property.2.1,Option.some_or,Option.some_or]
  have canonRoot : old.head?=some (.inr (.inl root)) := canonHead
  have padLast : (source.val++reverseEdges principal.edges++[.inl ⟨.inr (.inl ()),.inr branch⟩] :
      List (Endpoint site.net)).getLast?=some (.inl ⟨.inr (.inl ()),.inr branch⟩) := by
    simp only [List.getLast?_append,List.getLast?_singleton,Option.some_or]
  have canonEnd : old.getLast?=some (.inl ⟨.inr (.inl ()),.inr branch⟩) := canonLast
  have same := canonLabels.rooted_terminal_unique site.net
    (canonLabels.root_forward_of_flow flow root canonRoot positive) canonRoot padLabels
    (padLabels.root_forward_of_flow flow root padHead positive) padHead (canonEnd.trans padLast.symm)
  rw [same.1] at relation
  exact relation
end
section
variable {K B W : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W]
variable (c : Net signature K (B⊕(Bool⊕Bool)) W) (i j : Nat)
local notation "rhs" => fanRight Op.app i j
local notation "functionSegment" branch => (Sum.inr (Sum.inl (Sigma.mk (Sum.inl branch) (Sum.inl ()))) : PlugSegment c rhs)
local notation "exitSegment" branch => (Sum.inl (Sum.inr (Sum.inl (Sum.inr (Sum.inl branch)))) : PlugSegment c rhs)
 theorem fan_app_typed_function_prefix (branch : Bool) {es : List (PlugSegment c rhs)} {a b : Context}
    (labels : PlugLabelling c rhs es a b) (head : es.head?=some (functionSegment branch))
    (typed : ∃k,accessKind (plug c rhs) (es.map (plugEnd c.label (rhs).label))=some k) :
    ∃tail,es=(functionSegment branch)::(exitSegment branch)::tail ∧PlugLabelling c rhs ((exitSegment branch)::tail) a b := by
  cases es with
  | nil => cases head
  | cons e es =>
    have same := Option.some.inj head
    subst e
    cases labels with
    | single =>
      obtain ⟨kind,typed⟩ := typed
      change none=some kind at typed
      cases typed
    | @cons e f es a middle b turn rest =>
      change PlugTurn c rhs (.inr (.inr (.inl (.inl branch)))) f a middle at turn
      cases turn with
      | leave => exact ⟨es,rfl,rest⟩
      | right impossible => cases impossible
 theorem fan_app_copied_function_fragment {current : LTerm} {root : B}
    (matching : Matches (plug c rhs) root current.erase)
    (fragment : SourceEdgeFragment current (plug c rhs) root edge position)
    (role : SourceDeparture parentTerm .fn edge.fromPort)
    (parent : RootAccess (plug c rhs) root)
    (word : position=accessWord (plug c rhs) parent.val++[.fn])
    (branch : Bool)
    (finish : parent.val.getLast?=some ((plug c rhs).wire (.inl ⟨.inr (.inl branch),.inr false⟩)))
    {a b : Context} (labels : Labelling (plug c rhs) fragment.segments a b) :
    ∃tail,fragment.segments.map (plugEnd c.label (rhs).label).invFun=
      (functionSegment branch)::(exitSegment branch)::tail ∧PlugLabelling c rhs ((exitSegment branch)::tail) a b := by
  have actualStart := actual_function_child_head matching fragment role parent word
    (.inr (.inl branch)) (.inr false) (.inl ()) HEq.rfl finish
  have head := fragment.start
  rw [actualStart] at head
  have rawHead : (fragment.segments.map (plugEnd c.label (rhs).label).invFun).head?=some (functionSegment branch) := by
    rw [List.head?_map,head]
    rfl
  apply fan_app_typed_function_prefix c i j branch (labels.plug_decomposition c rhs) rawHead
  simpa only [plug_decomposition_flatten] using fragment.fragment_typed
end
section
variable {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K → Label signature} {i j : Nat} {lt : i<j}
variable (site : PathSite (Schema.fanAction Op.app i j lt) kept (B:=B) (W:=W) (V:=V))
local notation "cut" => cutFragment site.net (pathPartition (Schema.fanAction Op.app i j lt) V) site.closed
private abbrev appFanRight (i j : Nat) (lt : i<j) := (Schema.fanAction Op.app i j lt).right.net
local notation "rhs" => appFanRight i j lt
local notation "functionSegment" branch => (Sum.inr (Sum.inl (Sigma.mk (Sum.inl branch) (Sum.inl ()))) : PlugSegment cut rhs)
local notation "exitPivot" branch => (Sum.inr (Sum.inl (Sum.inr (Sum.inl branch))) : Endpoint cut)
local notation "activeAux" branch => (Sum.inl (Sigma.mk (Sum.inr (Sum.inl ())) (Sum.inr branch)) : Endpoint site.net)

/-- The actual copied APP parent and kept child terminal determine both
normalizations. The old split is a conclusion, not an oracle supplied by
the caller. The seam is cut from this same whole target labelling. -/
theorem SourceEdgeFragment.fan_app_copied_function_kept_cut
    {directions : B → Bool} (flow : FlowBalance site.net directions)
    (root : B) (positive : directions root=true) {current : LTerm}
    (sourceMatches : Matches site.net root current.erase) (targetMatches : Matches site.reduce root current.erase)
    (principal : SiteActionPrincipal site) {edge : SourceEdge} {position : Path}
    (source : SourceEdgeFragment current site.net root edge position)
    (target : SourceEdgeFragment current site.reduce root edge position)
    (role : SourceDeparture parentTerm .fn edge.fromPort)
    (sourceParent : RootAccess site.net root) (targetParent : RootAccess site.reduce root)
    (sourceWord : position=accessWord site.net sourceParent.val++[.fn])
    (targetWord : position=accessWord site.reduce targetParent.val++[.fn])
    (branch : Bool)
    (parentFinish : targetParent.val.getLast?=some (site.reduce.wire (.inl ⟨.inr (.inl branch),appCtx⟩)))
    (endNode : K) (endPort : Port (kept endNode).sort)
    (endAt : target.access.val.getLast?=some (site.reduce.wire (.inl ⟨.inl endNode,endPort⟩)))
    {a b : Context} (wholeLabels : Labelling site.reduce target.access.val a b) :
    ∃ rawTail oldTail seam,
      target.segments.map (plugEnd (cut).label (rhs).label).invFun=
        (functionSegment branch)::Sum.inl (exitPivot branch)::rawTail ∧
      source.segments=reverseEdges principal.edges++(activeAux branch)::oldTail ∧
      ActionCanonicalBlocks site principal (Sum.inl (exitPivot branch)::rawTail)
        (site.outsideEnd (exitPivot branch)::oldTail) ∧
      PlugLabelling cut rhs (Sum.inl (exitPivot branch)::rawTail) seam b := by
  have targetCut := target.child_prefix targetMatches role targetParent targetWord
  obtain ⟨pieceInput,prefixLabels,pieceLabels⟩ := target.assignments a b wholeLabels
  obtain ⟨rawTail,targetShape,_tailLabels⟩ := fan_app_copied_function_fragment cut i j targetMatches target role targetParent targetWord branch parentFinish pieceLabels
  change List (PlugSegment cut rhs) at rawTail
  change target.segments.map (plugEnd (cut).label (rhs).label).invFun=
    (functionSegment branch)::Sum.inl (exitPivot branch)::rawTail at targetShape
  obtain ⟨whole,_sourceWholeLabels,_sourceEnd⟩ := site.action_kept_canonical_access (.fan .app i j lt)
    flow root positive sourceMatches principal source.access target.access
    (source.word.trans target.word.symm) endNode endPort endAt wholeLabels
  obtain ⟨c,d,parentLabels⟩ := targetParent.property.1.1
  have parentWord : accessWord site.net sourceParent.val=accessWord site.reduce targetParent.val :=
    List.append_cancel_right (sourceWord.symm.trans targetWord)
  have parent := site.fan_app_function_padding_access flow root positive sourceMatches principal
    sourceParent targetParent parentWord branch parentFinish parentLabels
  have rawSplit : target.access.val.map (plugEnd (cut).label (rhs).label).invFun=
      (targetParent.val.map (plugEnd (cut).label (rhs).label).invFun++
        [functionSegment branch,Sum.inl (exitPivot branch)])++rawTail := by
    rw [targetCut.2,List.map_append,targetShape]
    simp only [List.append_assoc,List.cons_append,List.nil_append]
  have parentLast : (targetParent.val.map (plugEnd (cut).label (rhs).label).invFun++
      [functionSegment branch,Sum.inl (exitPivot branch)]).getLast?=some (Sum.inl (exitPivot branch)) := by
    simp only [List.getLast?_append,List.getLast?_cons_cons,List.getLast?_singleton,Option.some_or]
  obtain ⟨oldTail,seam,oldSplit,relation,_actualParentLabels,actualPieceLabels⟩ :=
    whole.cut_at_raw_parent site parent (wholeLabels.plug_decomposition cut rhs) rawSplit (exitPivot branch) parentLast
  have sourceCut := source.child_prefix sourceMatches role sourceParent sourceWord
  have sourceShape : source.segments=reverseEdges principal.edges++(activeAux branch)::oldTail := by
    apply List.append_cancel_left (as:=sourceParent.val)
    rw [←sourceCut.2,oldSplit]
    simp only [List.append_assoc,List.singleton_append]
  exact ⟨rawTail,oldTail,seam,targetShape,sourceShape,relation,actualPieceLabels⟩

end
end Lamping.AG

#print axioms Lamping.AG.PendingRhsBlock.fan_app_function_padding

#print axioms Lamping.AG.PendingRhsBlock.fan_app_function_canonical_completion

#print axioms Lamping.AG.PathSite.fan_app_function_padding_access

#print axioms Lamping.AG.fan_app_typed_function_prefix

#print axioms Lamping.AG.fan_app_copied_function_fragment

#print axioms Lamping.AG.SourceEdgeFragment.fan_app_copied_function_kept_cut
