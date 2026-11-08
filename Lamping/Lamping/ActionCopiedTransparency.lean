import Lamping.Lamping.CopiedLambdaTransparency
namespace Lamping.AG
open Graph
section
variable {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K → Label signature} {i j : Nat} {lt : i<j}

/-- Every copied fan-lambda binding endpoint has the original target
assignment's literal binding decomposition. All pending metadata is derived
from its real two-segment RHS prefix. -/
theorem PathSite.fan_copied_lambda_transparency
    (site : PathSite (.fanAction .lam i j lt) kept (B:=B) (W:=W) (V:=V))
    {boundary : B → Bool} (flow : FlowBalance site.net boundary) (root : B) (positive : boundary root=true)
    (oldT : Transparency site.net root) {es : List (Endpoint site.reduce)} {a b : Context}
    (labels : Labelling site.reduce es a b) (rooted : es.head?=some (.inr (.inl root)))
    (branch : Bool) (finish : es.getLast?=some (site.reduce.wire (.inl ⟨.inr (.inl branch),lamBind⟩))) :
    ∃ (pre loop : List (Endpoint site.reduce)) (middle : Context) (binding : BindingLoop site.reduce loop middle b),
      es=pre++loop ∧binding.binder=.inr (.inl branch) ∧
      pre.getLast?=some (site.reduce.wire (.inl ⟨.inr (.inl branch),(.inl ())⟩)) ∧Labelling site.reduce pre a middle := by
  let c := cutFragment site.net (pathPartition (Schema.fanAction .lam i j lt) V) site.closed
  let r := fanRight .lam i j
  let first : Endpoint c := .inr (.inl (.inl root))
  obtain ⟨pending,insideLast⟩ := labels.pending_new_node c r first rooted (.inl branch) lamBind finish
  obtain ⟨entry,_shape,inverse⟩ := fanRight_copied_aux_prefix .lam i j branch false pending.enter
    pending.inside pending.middle b pending.insideLabels pending.insideHead insideLast
  have rawHead : (es.map (plugEnd (c).label (r).label).invFun).head?=some (.inl first) := by
    rw [List.head?_map,rooted]
    rfl
  obtain ⟨pre,loop,middle,binding,split,binderEq,ctx,ctxRole,preEnd,preLabels⟩ :=
    site.pending_copied_lambda_transparency (.fan .lam i j lt) rfl flow positive oldT true false HEq.rfl HEq.rfl
      pending rawHead entry branch (.inl branch) (.fan site branch) lamBind HEq.rfl inverse
      (by change ((es.map (plugEnd (c).label (r).label).invFun).map (plugEnd (c).label (r).label)).getLast?=_; rw [plug_decomposition_flatten]; exact finish)
  have ctxEq : ctx=.inl () := eq_of_heq ctxRole
  rw [ctxEq] at preEnd
  change (es.map (plugEnd (c).label (r).label).invFun).map (plugEnd (c).label (r).label)=pre++loop at split
  rw [plug_decomposition_flatten] at split
  exact ⟨pre,loop,middle,binding,split,binderEq,preEnd,preLabels⟩

theorem PathSite.cro_copied_lambda_transparency
    (site : PathSite (.croAction .lam i j lt) kept (B:=B) (W:=W) (V:=V))
    {boundary : B → Bool} (flow : FlowBalance site.net boundary) (root : B) (positive : boundary root=true)
    (oldT : Transparency site.net root) {es : List (Endpoint site.reduce)} {a b : Context}
    (labels : Labelling site.reduce es a b) (rooted : es.head?=some (.inr (.inl root)))
    (finish : es.getLast?=some (site.reduce.wire (.inl ⟨.inr (.inl ()),lamBind⟩))) :
    ∃ (pre loop : List (Endpoint site.reduce)) (middle : Context) (binding : BindingLoop site.reduce loop middle b),
      es=pre++loop ∧binding.binder=.inr (.inl ()) ∧
      pre.getLast?=some (site.reduce.wire (.inl ⟨.inr (.inl ()),(.inl ())⟩)) ∧Labelling site.reduce pre a middle := by
  let c := cutFragment site.net (pathPartition (Schema.croAction .lam i j lt) V) site.closed
  let r := unaryRightCore .cro .lam (Bij.refl _) i (j-1)
  let first : Endpoint c := .inr (.inl (.inl root))
  obtain ⟨pending,insideLast⟩ := labels.pending_new_node c r first rooted (.inl ()) lamBind finish
  obtain ⟨entry,_shape,inverse⟩ := unaryRight_copied_aux_prefix .cro .lam (Bij.refl _) (Or.inr (Or.inl rfl))
    i (j-1) false pending.enter pending.inside pending.middle b pending.insideLabels pending.insideHead insideLast
  have rawHead : (es.map (plugEnd (c).label (r).label).invFun).head?=some (.inl first) := by
    rw [List.head?_map,rooted]
    rfl
  obtain ⟨pre,loop,middle,binding,split,binderEq,ctx,ctxRole,preEnd,preLabels⟩ :=
    site.pending_copied_lambda_transparency (.cro .lam i j lt) rfl flow positive oldT true false HEq.rfl HEq.rfl
      pending rawHead entry () (.inl ()) (.cro site) lamBind HEq.rfl inverse
      (by change ((es.map (plugEnd (c).label (r).label).invFun).map (plugEnd (c).label (r).label)).getLast?=_; rw [plug_decomposition_flatten]; exact finish)
  have ctxEq : ctx=.inl () := eq_of_heq ctxRole
  rw [ctxEq] at preEnd
  change (es.map (plugEnd (c).label (r).label).invFun).map (plugEnd (c).label (r).label)=pre++loop at split
  rw [plug_decomposition_flatten] at split
  exact ⟨pre,loop,middle,binding,split,binderEq,preEnd,preLabels⟩

theorem PathSite.bra_copied_lambda_transparency
    (site : PathSite (.braAction .lam i j lt) kept (B:=B) (W:=W) (V:=V))
    {boundary : B → Bool} (flow : FlowBalance site.net boundary) (root : B) (positive : boundary root=true)
    (oldT : Transparency site.net root) {es : List (Endpoint site.reduce)} {a b : Context}
    (labels : Labelling site.reduce es a b) (rooted : es.head?=some (.inr (.inl root)))
    (finish : es.getLast?=some (site.reduce.wire (.inl ⟨.inr (.inl ()),lamBind⟩))) :
    ∃ (pre loop : List (Endpoint site.reduce)) (middle : Context) (binding : BindingLoop site.reduce loop middle b),
      es=pre++loop ∧binding.binder=.inr (.inl ()) ∧
      pre.getLast?=some (site.reduce.wire (.inl ⟨.inr (.inl ()),(.inl ())⟩)) ∧Labelling site.reduce pre a middle := by
  let c := cutFragment site.net (pathPartition (Schema.braAction .lam i j lt) V) site.closed
  let r := unaryRightCore .bra .lam (Bij.refl _) i (j+1)
  let first : Endpoint c := .inr (.inl (.inl root))
  obtain ⟨pending,insideLast⟩ := labels.pending_new_node c r first rooted (.inl ()) lamBind finish
  obtain ⟨entry,_shape,inverse⟩ := unaryRight_copied_aux_prefix .bra .lam (Bij.refl _) (Or.inr (Or.inr rfl))
    i (j+1) false pending.enter pending.inside pending.middle b pending.insideLabels pending.insideHead insideLast
  have rawHead : (es.map (plugEnd (c).label (r).label).invFun).head?=some (.inl first) := by
    rw [List.head?_map,rooted]
    rfl
  obtain ⟨pre,loop,middle,binding,split,binderEq,ctx,ctxRole,preEnd,preLabels⟩ :=
    site.pending_copied_lambda_transparency (.bra .lam i j lt) rfl flow positive oldT true false HEq.rfl HEq.rfl
      pending rawHead entry () (.inl ()) (.bra site) lamBind HEq.rfl inverse
      (by change ((es.map (plugEnd (c).label (r).label).invFun).map (plugEnd (c).label (r).label)).getLast?=_; rw [plug_decomposition_flatten]; exact finish)
  have ctxEq : ctx=.inl () := eq_of_heq ctxRole
  rw [ctxEq] at preEnd
  change (es.map (plugEnd (c).label (r).label).invFun).map (plugEnd (c).label (r).label)=pre++loop at split
  rw [plug_decomposition_flatten] at split
  exact ⟨pre,loop,middle,binding,split,binderEq,preEnd,preLabels⟩
end
end Lamping.AG
