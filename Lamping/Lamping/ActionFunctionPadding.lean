import Lamping.Lamping.ActionPendingLambdaPadding
import Lamping.Lamping.ActionCopiedBindingComparison
namespace Lamping.AG
open Graph
section
variable {K B W : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W]
variable (c : Net signature K (B⊕(Unit⊕Bool)) W) (op : Op) (single : Bij Unit (Aux op))
    (control : op=.fan ∨op=.cro ∨op=.bra) (i k : Nat)
local notation "rhs" => unaryRightCore op Op.app single i k
/-- Extend an actual app-context pending block only by its real app-function
turn and frontier exit, retaining the low reader's supplied assignment. -/
theorem PendingRhsBlock.unary_function_padding (control : op=.fan ∨op=.cro ∨op=.bra)
    {raw : List (PlugSegment c rhs)} {a b : Context}
    (pending : PendingRhsBlock c rhs raw a b)
    (finish : pending.inside.getLast?=some ((rhs).wire (.inl ⟨.inl (),appCtx⟩))) :
    ∃ path : LocalPath rhs (.inr false) (.inl ()) pending.middle b,
      pending.enter=.inr false ∧
      path.edges=pending.inside++[.inl ⟨.inl (),(Sum.inl ())⟩] ∧
      PlugExcursions c rhs
        (.inl pending.last::(path.edges.map Sum.inr++[.inl (.inr (.inl (.inr (.inl ()))))]))
        pending.middle b ∧
      raw++[.inr (.inl ⟨.inl (),(Sum.inl ())⟩),.inl (.inr (.inl (.inr (.inl ()))))] =
        pending.pre++((.inl pending.last::(path.edges.map (Sum.inr : Endpoint rhs → PlugSegment c rhs)++
          [.inl (.inr (.inl (.inr (.inl ()))))] )) : List (PlugSegment c rhs)).tail := by
  obtain ⟨entry,shape,rule⟩ := unaryRight_app_context_prefix op single control i k
    pending.enter pending.inside pending.middle b pending.insideLabels pending.insideHead finish
  let path : LocalPath rhs (.inr false) (.inl ()) pending.middle b := {
    edges := [.inr (.inl (.inr false)),.inl ⟨.inr false,.inr (single ())⟩,
      .inl ⟨.inl (),(Sum.inl ())⟩]
    start := rfl
    finish := rfl
    labeling := .cons (LabelledTurn.node (g:=rhs) (.inr false) _ _ rule)
      (.cons (LabelledTurn.node (g:=rhs) (.inl ()) _ _ (show Traversal k (.op .app) appCtx (Sum.inl ()) b b from .direct (.appFun b))) (.single _ _)) }
  have arrival : c.wire pending.last=.inr (.inl (.inr (.inr false))) := by
    rw [pending.arrival,entry]
  refine ⟨path,entry,?_,?_,?_⟩
  · rw [shape];rfl
  · exact .through path arrival (.single _ _)
  · have eqs := pending.equation
    rw [shape] at eqs
    exact (congrArg (fun xs => xs++[.inr (.inl ⟨.inl (),(Sum.inl ())⟩),
      .inl (.inr (.inl (.inr (.inl ()))))] ) eqs).trans
      (by simp only [List.append_assoc];rfl)
end
section
variable {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K → Label signature} {i j : Nat} {lt : i<j}
variable (site : PathSite (Schema.croAction Op.app i j lt) kept (B:=B) (W:=W) (V:=V))
local notation "cut" => cutFragment site.net (pathPartition (Schema.croAction Op.app i j lt) V) site.closed
local notation "rhs" => unaryRightCore Op.cro Op.app (Bij.refl _) i (j-1)
theorem PendingRhsBlock.cro_function_canonical_completion (principal : SiteActionPrincipal site)
    {raw : List (PlugSegment cut rhs)} {a b : Context}
    (pending : PendingRhsBlock cut rhs raw a b)
    (first : Endpoint cut) (head : raw.head?=some (.inl first))
    (finish : pending.inside.getLast?=some ((rhs).wire (.inl ⟨.inl (),appCtx⟩))) :
    ∃ old, ActionCanonicalBlocks site principal
        (raw++[.inr (.inl ⟨.inl (),.inl ()⟩),.inl (.inr (.inl (.inr (.inl ()))))] ) old ∧
      Labelling site.net old a b ∧old.head?=some (site.outsideEnd first) ∧
      old.getLast?=some (site.outsideEnd (.inr (.inl (.inr (.inl ()))))) ∧
      PlugExcursions cut rhs
        (raw++[.inr (.inl ⟨.inl (),.inl ()⟩),.inl (.inr (.inl (.inr (.inl ()))))] ) a b := by
  obtain ⟨path,_,pathEq,rightPath,paddedEq⟩ := pending.unary_function_padding
    cut .cro (Bij.refl _) i (j-1) (Or.inr (Or.inl rfl)) finish
  obtain ⟨before,preEq⟩ := List.getLast?_eq_some_iff.mp pending.prefixLast
  have joined := pending.prefixPath.overlap_join cut rhs preEq rightPath
  have whole : PlugExcursions cut rhs
      (raw++[.inr (.inl ⟨.inl (),.inl ()⟩),.inl (.inr (.inl (.inr (.inl ()))))] ) a b := by
    rw [paddedEq]
    simpa only [preEq,List.append_assoc,List.cons_append,List.tail_cons] using joined
  have starts : (raw++[.inr (.inl ⟨.inl (),.inl ()⟩),
      .inl (.inr (.inl (.inr (.inl ()))))] : List (PlugSegment cut rhs)).head?=some (.inl first) := by
    rw [List.head?_append,head,Option.some_or]
  have ends : (raw++[.inr (.inl ⟨.inl (),.inl ()⟩),
      .inl (.inr (.inl (.inr (.inl ()))))] : List (PlugSegment cut rhs)).getLast?=
      some (.inl (.inr (.inl (.inr (.inl ()))))) := by
    simp only [List.getLast?_append,List.getLast?_cons_cons,List.getLast?_singleton,Option.some_or]
  obtain ⟨old,relation,labels,start,last⟩ := whole.action_canonical_lift site (.cro .app i j lt)
    principal first (.inr (.inl (.inr (.inl ())))) starts ends
  exact ⟨old,relation,labels,start,last,whole⟩
end
section
variable {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K → Label signature} {i j : Nat} {lt : i<j}
variable (site : PathSite (Schema.braAction Op.app i j lt) kept (B:=B) (W:=W) (V:=V))
local notation "cut" => cutFragment site.net (pathPartition (Schema.braAction Op.app i j lt) V) site.closed
local notation "rhs" => unaryRightCore Op.bra Op.app (Bij.refl _) i (j+1)
theorem PendingRhsBlock.bra_function_canonical_completion (principal : SiteActionPrincipal site)
    {raw : List (PlugSegment cut rhs)} {a b : Context}
    (pending : PendingRhsBlock cut rhs raw a b)
    (first : Endpoint cut) (head : raw.head?=some (.inl first))
    (finish : pending.inside.getLast?=some ((rhs).wire (.inl ⟨.inl (),appCtx⟩))) :
    ∃ old, ActionCanonicalBlocks site principal
        (raw++[.inr (.inl ⟨.inl (),.inl ()⟩),.inl (.inr (.inl (.inr (.inl ()))))] ) old ∧
      Labelling site.net old a b ∧old.head?=some (site.outsideEnd first) ∧
      old.getLast?=some (site.outsideEnd (.inr (.inl (.inr (.inl ()))))) ∧
      PlugExcursions cut rhs
        (raw++[.inr (.inl ⟨.inl (),.inl ()⟩),.inl (.inr (.inl (.inr (.inl ()))))] ) a b := by
  obtain ⟨path,_,pathEq,rightPath,paddedEq⟩ := pending.unary_function_padding
    cut .bra (Bij.refl _) i (j+1) (Or.inr (Or.inr rfl)) finish
  obtain ⟨before,preEq⟩ := List.getLast?_eq_some_iff.mp pending.prefixLast
  have joined := pending.prefixPath.overlap_join cut rhs preEq rightPath
  have whole : PlugExcursions cut rhs
      (raw++[.inr (.inl ⟨.inl (),.inl ()⟩),.inl (.inr (.inl (.inr (.inl ()))))] ) a b := by
    rw [paddedEq]
    simpa only [preEq,List.append_assoc,List.cons_append,List.tail_cons] using joined
  have starts : (raw++[.inr (.inl ⟨.inl (),.inl ()⟩),
      .inl (.inr (.inl (.inr (.inl ()))))] : List (PlugSegment cut rhs)).head?=some (.inl first) := by
    rw [List.head?_append,head,Option.some_or]
  have ends : (raw++[.inr (.inl ⟨.inl (),.inl ()⟩),
      .inl (.inr (.inl (.inr (.inl ()))))] : List (PlugSegment cut rhs)).getLast?=
      some (.inl (.inr (.inl (.inr (.inl ()))))) := by
    simp only [List.getLast?_append,List.getLast?_cons_cons,List.getLast?_singleton,Option.some_or]
  obtain ⟨old,relation,labels,start,last⟩ := whole.action_canonical_lift site (.bra .app i j lt)
    principal first (.inr (.inl (.inr (.inl ())))) starts ends
  exact ⟨old,relation,labels,start,last,whole⟩
end

section
variable {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K → Label signature} {i j : Nat} {lt : i<j}
variable (site : PathSite (Schema.croAction Op.app i j lt) kept (B:=B) (W:=W) (V:=V))
local notation "cut" => cutFragment site.net (pathPartition (Schema.croAction Op.app i j lt) V) site.closed
local notation "rhs" => unaryRightCore Op.cro Op.app (Bij.refl _) i (j-1)
theorem PathSite.cro_function_padding_access
    {directions : B → Bool} (flow : FlowBalance site.net directions)
    (root : B) (positive : directions root=true) {term : Lambda.Term}
    (matching : Matches site.net root term) (principal : SiteActionPrincipal site)
    (source : RootAccess site.net root) (target : RootAccess site.reduce root)
    (word : accessWord site.net source.val=accessWord site.reduce target.val)
    (finish : target.val.getLast?=some (site.reduce.wire (.inl ⟨.inr (.inl ()),appCtx⟩)))
    {a b : Context} (labels : Labelling site.reduce target.val a b) :
    ActionCanonicalBlocks site principal
      (target.val.map (plugEnd (cut).label (rhs).label).invFun++
        [.inr (.inl ⟨.inl (),.inl ()⟩),.inl (.inr (.inl (.inr (.inl ()))))] )
      (source.val++reverseEdges principal.edges++[.inl ⟨.inr (.inl ()),.inr ()⟩]) := by
  obtain ⟨pending,_preRelation,oldLabels,oldFinish,_shape⟩ :=
    site.cro_aux_canonical_access flow root positive matching principal source target word false finish labels
  let first : Endpoint cut := .inr (.inl (.inl root))
  have actualHead : target.val.head?=some (AG.plugLeft cut rhs first) := target.property.2.1
  have rawHead : (target.val.map (plugEnd (cut).label (rhs).label).invFun).head?=some (.inl first) := by
    rw [List.head?_map,actualHead]
    exact congrArg some ((plugEnd (cut).label (rhs).label).left_inv (.inl first))
  have insideFinish : pending.inside.getLast?=some ((rhs).wire (.inl ⟨.inl (),appCtx⟩)) := by
    apply pending.inside_finish cut rhs ((rhs).wire (.inl ⟨.inl (),appCtx⟩))
    rw [List.getLast?_map,finish]
    change some ((plugEnd (cut).label (rhs).label).invFun
      ((plug cut rhs).wire (.inl ⟨.inr (.inl ()),appCtx⟩)))=_
    rw [plugSegmentWire_inverse]
    rfl
  obtain ⟨entry,_shape2,rule⟩ := unaryRight_app_context_prefix .cro (Bij.refl _) (Or.inr (Or.inl rfl))
    i (j-1) pending.enter pending.inside pending.middle b pending.insideLabels pending.insideHead insideFinish
  have routeHead : (reverseEdges principal.edges).head?=some (.inl ⟨.inr (.inr ()),.inl ()⟩) := by
    simp only [reverseEdges,List.head?_map,List.head?_reverse,principal.last,Option.map_some,Pairing.involutive]
  have routeLast : (reverseEdges principal.edges).getLast?=
      some (site.net.wire (.inl ⟨.inr (.inl ()),.inl ()⟩)) := by
    simp only [reverseEdges,List.getLast?_map,List.getLast?_reverse,principal.first,Option.map_some]
  have crossing := principal_crossing_labels site.net (.inr (.inr ())) (.inr (.inl ()))
    appCtx (.inl ()) (.inl ()) (.inr ()) (reverseEdges principal.edges) routeHead routeLast
    (transparent_reverse_turns principal.edges principal.transparent) (Traversal.direct (.appFun pending.middle)) rule
  obtain ⟨before,sourceSplit⟩ := List.getLast?_eq_some_iff.mp oldFinish
  have padLabels : Labelling site.net
      (source.val++reverseEdges principal.edges++[.inl ⟨.inr (.inl ()),.inr ()⟩]) a b := by
    rw [sourceSplit] at oldLabels ⊢
    have joined := oldLabels.join crossing
    simpa only [List.append_assoc,List.singleton_append] using joined
  obtain ⟨old,relation,canonLabels,canonHead,canonLast,_whole⟩ :=
    pending.cro_function_canonical_completion site principal first rawHead insideFinish
  have padHead : (source.val++reverseEdges principal.edges++[.inl ⟨.inr (.inl ()),.inr ()⟩] :
      List (Endpoint site.net)).head?=some (.inr (.inl root)) := by
    rw [List.head?_append,List.head?_append,source.property.2.1,Option.some_or,Option.some_or]
  have canonRoot : old.head?=some (.inr (.inl root)) := canonHead
  have padLast : (source.val++reverseEdges principal.edges++[.inl ⟨.inr (.inl ()),.inr ()⟩] :
      List (Endpoint site.net)).getLast?=some (.inl ⟨.inr (.inl ()),.inr ()⟩) := by
    simp only [List.getLast?_append,List.getLast?_singleton,Option.some_or]
  have canonEnd : old.getLast?=some (.inl ⟨.inr (.inl ()),.inr ()⟩) := canonLast
  have same := canonLabels.rooted_terminal_unique site.net
    (canonLabels.root_forward_of_flow flow root canonRoot positive) canonRoot padLabels
    (padLabels.root_forward_of_flow flow root padHead positive) padHead (canonEnd.trans padLast.symm)
  rw [same.1] at relation
  exact relation
end
section
variable {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K → Label signature} {i j : Nat} {lt : i<j}
variable (site : PathSite (Schema.braAction Op.app i j lt) kept (B:=B) (W:=W) (V:=V))
local notation "cut" => cutFragment site.net (pathPartition (Schema.braAction Op.app i j lt) V) site.closed
local notation "rhs" => unaryRightCore Op.bra Op.app (Bij.refl _) i (j+1)
theorem PathSite.bra_function_padding_access
    {directions : B → Bool} (flow : FlowBalance site.net directions)
    (root : B) (positive : directions root=true) {term : Lambda.Term}
    (matching : Matches site.net root term) (principal : SiteActionPrincipal site)
    (source : RootAccess site.net root) (target : RootAccess site.reduce root)
    (word : accessWord site.net source.val=accessWord site.reduce target.val)
    (finish : target.val.getLast?=some (site.reduce.wire (.inl ⟨.inr (.inl ()),appCtx⟩)))
    {a b : Context} (labels : Labelling site.reduce target.val a b) :
    ActionCanonicalBlocks site principal
      (target.val.map (plugEnd (cut).label (rhs).label).invFun++
        [.inr (.inl ⟨.inl (),.inl ()⟩),.inl (.inr (.inl (.inr (.inl ()))))] )
      (source.val++reverseEdges principal.edges++[.inl ⟨.inr (.inl ()),.inr ()⟩]) := by
  obtain ⟨pending,_preRelation,oldLabels,oldFinish,_shape⟩ :=
    site.bra_aux_canonical_access flow root positive matching principal source target word false finish labels
  let first : Endpoint cut := .inr (.inl (.inl root))
  have actualHead : target.val.head?=some (AG.plugLeft cut rhs first) := target.property.2.1
  have rawHead : (target.val.map (plugEnd (cut).label (rhs).label).invFun).head?=some (.inl first) := by
    rw [List.head?_map,actualHead]
    exact congrArg some ((plugEnd (cut).label (rhs).label).left_inv (.inl first))
  have insideFinish : pending.inside.getLast?=some ((rhs).wire (.inl ⟨.inl (),appCtx⟩)) := by
    apply pending.inside_finish cut rhs ((rhs).wire (.inl ⟨.inl (),appCtx⟩))
    rw [List.getLast?_map,finish]
    change some ((plugEnd (cut).label (rhs).label).invFun
      ((plug cut rhs).wire (.inl ⟨.inr (.inl ()),appCtx⟩)))=_
    rw [plugSegmentWire_inverse]
    rfl
  obtain ⟨entry,_shape2,rule⟩ := unaryRight_app_context_prefix .bra (Bij.refl _) (Or.inr (Or.inr rfl))
    i (j+1) pending.enter pending.inside pending.middle b pending.insideLabels pending.insideHead insideFinish
  have routeHead : (reverseEdges principal.edges).head?=some (.inl ⟨.inr (.inr ()),.inl ()⟩) := by
    simp only [reverseEdges,List.head?_map,List.head?_reverse,principal.last,Option.map_some,Pairing.involutive]
  have routeLast : (reverseEdges principal.edges).getLast?=
      some (site.net.wire (.inl ⟨.inr (.inl ()),.inl ()⟩)) := by
    simp only [reverseEdges,List.getLast?_map,List.getLast?_reverse,principal.first,Option.map_some]
  have crossing := principal_crossing_labels site.net (.inr (.inr ())) (.inr (.inl ()))
    appCtx (.inl ()) (.inl ()) (.inr ()) (reverseEdges principal.edges) routeHead routeLast
    (transparent_reverse_turns principal.edges principal.transparent) (Traversal.direct (.appFun pending.middle)) rule
  obtain ⟨before,sourceSplit⟩ := List.getLast?_eq_some_iff.mp oldFinish
  have padLabels : Labelling site.net
      (source.val++reverseEdges principal.edges++[.inl ⟨.inr (.inl ()),.inr ()⟩]) a b := by
    rw [sourceSplit] at oldLabels ⊢
    have joined := oldLabels.join crossing
    simpa only [List.append_assoc,List.singleton_append] using joined
  obtain ⟨old,relation,canonLabels,canonHead,canonLast,_whole⟩ :=
    pending.bra_function_canonical_completion site principal first rawHead insideFinish
  have padHead : (source.val++reverseEdges principal.edges++[.inl ⟨.inr (.inl ()),.inr ()⟩] :
      List (Endpoint site.net)).head?=some (.inr (.inl root)) := by
    rw [List.head?_append,List.head?_append,source.property.2.1,Option.some_or,Option.some_or]
  have canonRoot : old.head?=some (.inr (.inl root)) := canonHead
  have padLast : (source.val++reverseEdges principal.edges++[.inl ⟨.inr (.inl ()),.inr ()⟩] :
      List (Endpoint site.net)).getLast?=some (.inl ⟨.inr (.inl ()),.inr ()⟩) := by
    simp only [List.getLast?_append,List.getLast?_singleton,Option.some_or]
  have canonEnd : old.getLast?=some (.inl ⟨.inr (.inl ()),.inr ()⟩) := canonLast
  have same := canonLabels.rooted_terminal_unique site.net
    (canonLabels.root_forward_of_flow flow root canonRoot positive) canonRoot padLabels
    (padLabels.root_forward_of_flow flow root padHead positive) padHead (canonEnd.trans padLast.symm)
  rw [same.1] at relation
  exact relation
end
end Lamping.AG
