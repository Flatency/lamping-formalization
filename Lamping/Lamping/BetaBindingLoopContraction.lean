import Lamping.Lamping.BetaResidualOccurrences
namespace Lamping.AG
open Graph
section
variable {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K → Label signature} {i : Nat}
variable (site : PathSite (.beta i) kept (B:=B) (W:=W) (V:=V))
local notation "cut" => cutFragment site.net (pathPartition (Schema.beta i) V) site.closed
local notation "rhs" => wires Bool Bool boolFlip

private theorem raw_last {edge : BetaEdge site.net} {raw old}
    (relation : BetaPathResidual site edge raw old) : ∃ last : Endpoint cut,raw.getLast?=some (.inl last) := by
  induction relation with
  | single e => exact ⟨e,rfl⟩
  | outside rest ih => obtain ⟨last,finish⟩ := ih; exact ⟨last,by simpa only [List.getLast?_cons_cons] using finish⟩
  | context arrival rest ih => obtain ⟨last,finish⟩ := ih; exact ⟨last,by simpa only [List.getLast?_cons_cons] using finish⟩
  | binding arrival rest ih => obtain ⟨last,finish⟩ := ih; exact ⟨last,by simpa only [List.getLast?_cons_cons] using finish⟩

/-- Contract a given actual expanded binding loop whose binder is retained.
The same original loop contexts and shell survive; ordinary direction comes
from the supplied actual reduced path, not from a new generation certificate. -/
theorem BetaPathResidual.contract_kept_binding_loop {edge : BetaEdge site.net} {raw old}
    (relation : BetaPathResidual site edge raw old) (geometry : SiteBetaGeometry site edge)
    {originalA originalB a b : Context} (shape : PlugLabelling cut rhs raw originalA originalB)
    (forward : Forward site.reduce (raw.map (plugEnd (cut).label (rhs).label)))
    (binding : ExpandedBindingLoop site.net old a b) (node : K) (binderEq : binding.binder=.inl node) :
    ∃ loop : BindingLoop site.reduce (raw.map (plugEnd (cut).label (rhs).label)) a b,
      loop.binder=.inl node := by
  rcases binding with ⟨binder,isLam,body,bind,bodyRole,bindRole,start,finish,labels,expandedForward,shell⟩
  dsimp only at binderEq
  subst binder
  have head : ∃ first : Endpoint cut,raw.head?=some (.inl first) := by
    cases relation <;> exact ⟨_,rfl⟩
  obtain ⟨first,rawHead⟩ := head
  have oldHead := relation.head site rawHead
  have sameHead : first=(.inl ⟨node,body⟩ : Endpoint cut) :=
    site.outsideEnd_injective (Option.some.inj (oldHead.symm.trans start))
  subst first
  obtain ⟨last,rawLast⟩ := raw_last site relation
  have oldLast := relation.finish site rawLast
  have sameLast : last=(cut).wire (.inl ⟨node,bind⟩) :=
    site.outsideEnd_injective ((Option.some.inj (oldLast.symm.trans finish)).trans
      (site.outsideEnd_wire (.inl ⟨node,bind⟩)))
  subst last
  have actual := (relation.contract site geometry shape labels).actual cut rhs
  refine ⟨{ binder := .inl node
            isLam := isLam
            body := body
            bind := bind
            body_role := bodyRole
            bind_role := bindRole
            start := ?_
            finish := ?_
            proper := actual
            forward := forward
            shell := shell },rfl⟩
  · rw [List.head?_map,rawHead]
    rfl
  · rw [List.getLast?_map,rawLast]
    exact congrArg some (plugLeft_wire cut rhs (.inl ⟨node,bind⟩)).symm

private theorem split_raw {pre post : List (PlugSegment cut rhs)} {e : PlugSegment cut rhs} {a b : Context}
    (labels : PlugLabelling cut rhs (pre++e::post) a b) :
    ∃ middle,PlugLabelling cut rhs (pre++[e]) a middle ∧PlugLabelling cut rhs (e::post) middle b := by
  induction pre generalizing a with
  | nil => exact ⟨a,.single _ _,labels⟩
  | cons x pre ih =>
    cases pre with
    | nil => cases labels with | cons turn tail => exact ⟨_,.cons turn (.single _ _),tail⟩
    | cons y pre => cases labels with
      | cons turn tail =>
        obtain ⟨middle,before,after⟩ := ih tail
        exact ⟨middle,.cons turn before,after⟩

private theorem lambda_body_predecessor {kind : Kind} {index : Nat} {ctx body p : Port kind} {a b : Context}
    (sort : kind=.op .lam) (ctxRole : HEq ctx (Sum.inl () : Port (.op .lam))) (bodyRole : HEq body lamBody)
    (rule : Traversal index kind p body a b) : p=ctx ∧a=b := by
  subst kind
  have ctxEq : ctx=.inl () := eq_of_heq ctxRole
  have bodyEq : body=lamBody := eq_of_heq bodyRole
  subst ctx
  subst body
  refine ⟨?_,rule.proper_context⟩
  cases p with
  | inl u => cases u; rfl
  | inr branch =>
    cases branch
    · exact False.elim (rule.no_binding.1 rfl)
    · exact False.elim (rule.distinct rfl)

private theorem last_turn {N D U : Type} [FiniteNames N] [FiniteNames D] [FiniteNames U]
    {g : Net signature N D U} {pre : List (Endpoint g)} {last : Endpoint g} {a b : Context}
    (labels : Labelling g (pre++[last]) a b) (nonempty : pre≠[]) :
    ∃ previous middle,pre.getLast?=some previous ∧Labelling g pre a middle ∧
      LabelledTurn g (g.wire previous) last middle b := by
  induction pre generalizing a with
  | nil => exact False.elim (nonempty rfl)
  | cons x pre ih =>
    cases pre with
    | nil => cases labels with
      | cons turn tail => cases tail; exact ⟨x,_,rfl,.single _ _,turn⟩
    | cons y pre => cases labels with
      | cons turn tail =>
        obtain ⟨previous,middle,finish,before,lastTurn⟩ := ih tail (by simp)
        exact ⟨previous,middle,by simpa only [List.getLast?_cons_cons] using finish,.cons turn before,lastTurn⟩

private theorem drop_lambda_body {N D U : Type} [FiniteNames N] [FiniteNames D] [FiniteNames U]
    {g : Net signature N D U} {pre : List (Endpoint g)} (node : N) (ctx body : Port (g.label node).sort)
    (sort : (g.label node).sort=.op .lam) (ctxRole : HEq ctx (Sum.inl () : Port (.op .lam))) (bodyRole : HEq body lamBody)
    {a b : Context} (labels : Labelling g (pre++[.inl ⟨node,body⟩]) a b) (nonempty : pre≠[]) :
    Labelling g pre a b ∧pre.getLast?=some (g.wire (.inl ⟨node,ctx⟩)) := by
  obtain ⟨previous,middle,finish,before,turn⟩ := last_turn labels nonempty
  obtain ⟨port,arrives,rule⟩ := turn.reverse.from_node node body rfl
  obtain ⟨portEq,contexts⟩ := lambda_body_predecessor sort ctxRole bodyRole rule.reverse
  subst port
  subst middle
  have wired := congrArg g.wire.mate arrives
  rw [Pairing.involutive] at wired
  exact ⟨before,finish.trans (congrArg some wired)⟩

/-- Transport the selected binding occurrence and its literal prefix. The
old prefix includes the body segment with the SAME seam context as the old
expanded loop, ruling out an unrelated shell witness. -/
theorem BetaPathResidual.contract_binding_decomposition {edge : BetaEdge site.net} {raw old}
    (relation : BetaPathResidual site edge raw old) (geometry : SiteBetaGeometry site edge)
    {a middle b : Context} (shape : PlugLabelling cut rhs raw a b)
    (root : B) (rooted : (raw.map (plugEnd (cut).label (rhs).label)).head?=some (.inr (.inl root)))
    (forward : Forward site.reduce (raw.map (plugEnd (cut).label (rhs).label)))
    (pre loop : List (Endpoint site.net)) (split : old=pre++loop)
    (binding : ExpandedBindingLoop site.net loop middle b) (node : K) (binderEq : binding.binder=.inl node)
    (ctx : Port (kept node).sort) (ctxRole : HEq ctx (Sum.inl () : Port (.op .lam)))
    (prefixLabels : ExpandedLabelling site.net (pre++[.inl ⟨binding.binder,binding.body⟩]) a middle) :
    ∃ targetPre targetLoop : List (Endpoint site.reduce),
      raw.map (plugEnd (cut).label (rhs).label)=targetPre++targetLoop ∧
      Labelling site.reduce targetPre a middle ∧
      targetPre.getLast?=some (site.reduce.wire (.inl ⟨.inl node,ctx⟩)) ∧
      ∃ targetBinding : BindingLoop site.reduce targetLoop middle b,targetBinding.binder=.inl node := by
  rcases binding with ⟨binder,isLam,body,bind,bodyRole,bindRole,start,finish,loopLabels,loopForward,shell⟩
  dsimp only at binderEq prefixLabels
  subst binder
  obtain ⟨tail,loopSplit⟩ := List.head?_eq_some_iff.mp start
  have split' : old=pre++(.inl ⟨.inl node,body⟩)::tail := by rw [split,loopSplit]
  obtain ⟨cutAt,beforeEq,afterEq⟩ := relation.split_kept_departure site geometry node body pre tail split'
  have sourcePrefix := cutAt.prefixResidual
  have sourceSuffix := cutAt.suffixResidual
  rw [beforeEq] at sourcePrefix
  rw [afterEq] at sourceSuffix
  have shape' := shape
  rw [cutAt.raw_eq] at shape'
  obtain ⟨originalMiddle,shapePrefix,shapeSuffix⟩ := split_raw site shape'
  have newPrefix := (sourcePrefix.contract site geometry shapePrefix prefixLabels).actual cut rhs
  let newLoopLabels : ExpandedBindingLoop site.net ((site.outsideEnd (.inl ⟨node,body⟩))::tail) middle b := {
    binder := .inl node
    isLam := isLam
    body := body
    bind := bind
    body_role := bodyRole
    bind_role := bindRole
    start := rfl
    finish := by change ((.inl ⟨.inl node,body⟩)::tail).getLast?=_; rw [←loopSplit]; exact finish
    proper := by change ExpandedLabelling site.net ((.inl ⟨.inl node,body⟩)::tail) middle b; rw [←loopSplit]; exact loopLabels
    forward := by change ExpandedForward site.net ((.inl ⟨.inl node,body⟩)::tail); rw [←loopSplit]; exact loopForward
    shell := shell }
  have fullSplit : raw.map (plugEnd (cut).label (rhs).label)=
      cutAt.before.map (plugEnd (cut).label (rhs).label)++
        ((Sum.inl (.inl ⟨node,body⟩))::cutAt.after).map (plugEnd (cut).label (rhs).label) := by
    exact (congrArg (List.map (plugEnd (cut).label (rhs).label)) cutAt.raw_eq).trans (List.map_append)
  have bodyAt : (raw.map (plugEnd (cut).label (rhs).label))[cutAt.before.length]?=
      some (.inl ⟨.inl node,body⟩) := by
    rw [fullSplit,List.getElem?_append_right (by simp),List.length_map,Nat.sub_self]
    rfl
  have suffixForward := forward.suffix_at cutAt.before.length _ bodyAt
  rw [fullSplit,List.drop_append,List.length_map] at suffixForward
  have dropped : (cutAt.before.map (plugEnd (cut).label (rhs).label)).drop cutAt.before.length=[] := by
    have proof : (cutAt.before.map (plugEnd (cut).label (rhs).label)).drop
        (cutAt.before.map (plugEnd (cut).label (rhs).label)).length=[] := List.drop_length
    simpa only [List.length_map] using proof
  simp only [dropped,Nat.sub_self,List.drop_zero,List.nil_append] at suffixForward
  obtain ⟨newBinding,newBinder⟩ := sourceSuffix.contract_kept_binding_loop site geometry shapeSuffix suffixForward
    newLoopLabels node rfl
  have nonempty : cutAt.before.map (plugEnd (cut).label (rhs).label)≠[] := by
    intro empty
    rw [fullSplit,empty,List.nil_append] at rooted
    cases rooted
  simp only [List.map_append,List.map_cons,List.map_nil] at newPrefix
  obtain ⟨targetPrefix,prefixEnd⟩ := drop_lambda_body (g:=site.reduce) (.inl node) ctx body isLam ctxRole bodyRole newPrefix nonempty
  exact ⟨_,_,fullSplit,targetPrefix,prefixEnd,newBinding,newBinder⟩

private theorem lambda_body_identity {kind : Kind} {index : Nat} {ctx body : Port kind}
    (sort : kind=.op .lam) (ctxRole : HEq ctx (Sum.inl () : Port (.op .lam))) (bodyRole : HEq body lamBody)
    (context : Context) : Traversal index kind ctx body context context := by
  subst kind
  have ctxEq : ctx=.inl () := eq_of_heq ctxRole
  have bodyEq : body=lamBody := eq_of_heq bodyRole
  subst ctx
  subst body
  exact .direct (.lamBody context)

/-- The usual old expanded transparency decomposition supplies the precise
prefix seam. The actual beta residual transports that decomposition, with
the original a/middle/b assignment and retained physical lambda. -/
theorem BetaPathResidual.contract_binding_prefix {edge : BetaEdge site.net} {raw old}
    (relation : BetaPathResidual site edge raw old) (geometry : SiteBetaGeometry site edge)
    {a middle b : Context} (shape : PlugLabelling cut rhs raw a b)
    (root : B) (rooted : (raw.map (plugEnd (cut).label (rhs).label)).head?=some (.inr (.inl root)))
    (forward : Forward site.reduce (raw.map (plugEnd (cut).label (rhs).label)))
    (pre loop : List (Endpoint site.net)) (split : old=pre++loop)
    (binding : ExpandedBindingLoop site.net loop middle b) (node : K) (binderEq : binding.binder=.inl node)
    (ctx : Port (kept node).sort) (ctxRole : HEq ctx (Sum.inl () : Port (.op .lam)))
    (prefixEnd : pre.getLast?=some (site.net.wire (.inl ⟨.inl node,ctx⟩)))
    (prefixLabels : ExpandedLabelling site.net pre a middle) :
    ∃ targetPre targetLoop : List (Endpoint site.reduce),
      raw.map (plugEnd (cut).label (rhs).label)=targetPre++targetLoop ∧
      Labelling site.reduce targetPre a middle ∧
      targetPre.getLast?=some (site.reduce.wire (.inl ⟨.inl node,ctx⟩)) ∧
      ∃ targetBinding : BindingLoop site.reduce targetLoop middle b,targetBinding.binder=.inl node := by
  rcases binding with ⟨binder,isLam,body,bind,bodyRole,bindRole,start,finish,loopLabels,loopForward,shell⟩
  dsimp only at binderEq
  subst binder
  have rule := lambda_body_identity (index:=(kept node).index) isLam ctxRole bodyRole middle
  have extended := prefixLabels.splice prefixEnd (ExpandedLabelling.single (g:=site.net) (.inl ⟨.inl node,body⟩) middle) rfl
    (by
      rw [Pairing.involutive]
      exact ExpandedTurn.ordinary (LabelledTurn.node (g:=site.net) (.inl node) ctx body rule))
  let binding : ExpandedBindingLoop site.net loop middle b :=
    ⟨.inl node,isLam,body,bind,bodyRole,bindRole,start,finish,loopLabels,loopForward,shell⟩
  exact relation.contract_binding_decomposition site geometry shape root rooted forward pre loop split
    binding node rfl ctx ctxRole extended

theorem BetaPathResidual.contract_binding_prefix_actual {edge : BetaEdge site.net}
    {es : List (Endpoint site.reduce)} {old : List (Endpoint site.net)}
    (relation : BetaPathResidual site edge (es.map (plugEnd (cut).label (rhs).label).invFun) old)
    (geometry : SiteBetaGeometry site edge) {a middle b : Context}
    (labels : Labelling site.reduce es a b) (root : B)
    (rooted : es.head?=some (.inr (.inl root))) (forward : Forward site.reduce es)
    (pre loop : List (Endpoint site.net)) (split : old=pre++loop)
    (binding : ExpandedBindingLoop site.net loop middle b) (node : K) (binderEq : binding.binder=.inl node)
    (ctx : Port (kept node).sort) (ctxRole : HEq ctx (Sum.inl () : Port (.op .lam)))
    (prefixEnd : pre.getLast?=some (site.net.wire (.inl ⟨.inl node,ctx⟩)))
    (prefixLabels : ExpandedLabelling site.net pre a middle) :
    ∃ targetPre targetLoop : List (Endpoint site.reduce),es=targetPre++targetLoop ∧
      Labelling site.reduce targetPre a middle ∧
      targetPre.getLast?=some (site.reduce.wire (.inl ⟨.inl node,ctx⟩)) ∧
      ∃ targetBinding : BindingLoop site.reduce targetLoop middle b,targetBinding.binder=.inl node := by
  have actual := relation.contract_binding_prefix site geometry (labels.plug_decomposition cut rhs) root
    (by simpa only [plug_decomposition_flatten] using rooted)
    (by simpa only [plug_decomposition_flatten] using forward)
    pre loop split binding node binderEq ctx ctxRole prefixEnd prefixLabels
  simpa only [plug_decomposition_flatten] using actual
end
end Lamping.AG







