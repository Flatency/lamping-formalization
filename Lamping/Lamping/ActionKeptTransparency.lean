import Lamping.Lamping.ActionOccurrenceLabelling
import Lamping.Lamping.FlowRootPaths
import Lamping.Lamping.InitialPathConstruction
namespace Lamping.AG
open Graph
section
variable {s : Schema} {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K → Label signature} (site : PathSite s kept (B:=B) (W:=W) (V:=V))
local notation "cut" => cutFragment site.net (pathPartition s V) site.closed
local notation "rhs" => s.right.net

private theorem body_identity {kind : Kind} {index : Nat} {ctx body : Port kind}
    (sort : kind=.op .lam) (ctxRole : HEq ctx (Sum.inl () : Port (.op .lam))) (bodyRole : HEq body lamBody)
    (a : Context) : Traversal index kind ctx body a a := by
  subst kind
  have hc : ctx=.inl () := eq_of_heq ctxRole
  have hb : body=lamBody := eq_of_heq bodyRole
  subst ctx
  subst body
  exact .direct (.lamBody a)

/-- A retained binder's selected source occurrence reflects to an actual
target occurrence. Reflect the original target prefix's labels back through
the SAME canonical residual, and output uniqueness locks its seam to the
old T decomposition's middle. No arbitrary-input replay is needed. -/
theorem ActionCanonicalBlocks.kept_binding_prefix {principal : SiteActionPrincipal site} {raw old}
    (relation : ActionCanonicalBlocks site principal raw old)
    (root : B) {a middle b : Context}
    (labels : Labelling site.reduce (raw.map (plugEnd (cut).label (rhs).label)) a b)
    (rooted : (raw.map (plugEnd (cut).label (rhs).label)).head?=some (.inr (.inl root)))
    (forward : Forward site.reduce (raw.map (plugEnd (cut).label (rhs).label)))
    (pre loop : List (Endpoint site.net)) (split : old=pre++loop)
    (binding : BindingLoop site.net loop middle b) (node : K) (binderEq : binding.binder=.inl node)
    (ctx : Port (kept node).sort) (ctxRole : HEq ctx (Sum.inl () : Port (.op .lam)))
    (prefixEnd : pre.getLast?=some (site.net.wire (.inl ⟨.inl node,ctx⟩)))
    (prefixLabels : Labelling site.net pre a middle)
    (targetBind : Port (kept node).sort) (targetBindRole : HEq targetBind lamBind)
    (finish : (raw.map (plugEnd (cut).label (rhs).label)).getLast?=
      some (site.reduce.wire (.inl ⟨.inl node,targetBind⟩))) :
    ∃ targetPre targetLoop : List (Endpoint site.reduce),
      raw.map (plugEnd (cut).label (rhs).label)=targetPre++targetLoop ∧
      Labelling site.reduce targetPre a middle ∧
      targetPre.getLast?=some (site.reduce.wire (.inl ⟨.inl node,ctx⟩)) ∧
      ∃ targetBinding : BindingLoop site.reduce targetLoop middle b,targetBinding.binder=.inl node := by
  rcases binding with ⟨binder,isLam,body,bind,bodyRole,bindRole,start,loopEnd,loopLabels,loopForward,shell⟩
  dsimp at binderEq finish
  subst binder
  have bindEq : bind=targetBind := eq_of_heq (bindRole.trans targetBindRole.symm)
  subst targetBind
  obtain ⟨tail,loopSplit⟩ := List.head?_eq_some_iff.mp start
  have split' : old=pre++(.inl ⟨.inl node,body⟩)::tail := by rw [split,loopSplit]
  obtain ⟨cutAt,beforeEq,afterEq⟩ := relation.split_kept_decomposition site node body pre tail split'
  have fullSplit : raw.map (plugEnd (cut).label (rhs).label)=
      cutAt.before.map (plugEnd (cut).label (rhs).label)++
      (.inl ⟨.inl node,body⟩)::cutAt.after.map (plugEnd (cut).label (rhs).label) := by
    have mapped := congrArg (List.map (plugEnd (cut).label (rhs).label)) cutAt.raw_eq
    simpa only [List.map_append,List.map_cons] using mapped
  have fullLabels := labels
  rw [fullSplit] at fullLabels
  obtain ⟨actualMiddle,targetPrefix,targetSuffix⟩ := fullLabels.split_segment
  let physicalPrefix : List (Endpoint site.reduce) :=
    cutAt.before.map (plugEnd (cut).label (rhs).label)++[.inl ⟨.inl node,body⟩]
  have nonempty : cutAt.before.map (plugEnd (cut).label (rhs).label)≠[] := by
    intro empty
    rw [fullSplit,empty,List.nil_append] at rooted
    cases rooted
  have prefixRoot : physicalPrefix.head?=some (.inr (.inl root)) := by
    rw [fullSplit] at rooted
    cases before : cutAt.before with
    | nil => simp only [before,List.map_nil,List.nil_append,List.head?_cons] at rooted; cases rooted
    | cons e es => simpa only [physicalPrefix,before,List.map_cons,List.cons_append,List.head?_cons] using rooted
  have prefixLast : physicalPrefix.getLast?=some (AG.plugLeft cut rhs (.inl ⟨node,body⟩)) := by
    simp only [physicalPrefix,List.getLast?_append,List.getLast?_cons,List.getLast?_nil,Option.some_or]
    rfl
  have prefixShape := targetPrefix.local_excursions cut rhs (.inr (.inl (.inl root))) (.inl ⟨node,body⟩)
    prefixRoot prefixLast
  have prefixRaw : physicalPrefix.map (plugEnd (cut).label (rhs).label).invFun=
      cutAt.before++[.inl (.inl ⟨node,body⟩ : Endpoint cut)] := by
    have represented : physicalPrefix=
        (cutAt.before++[(Sum.inl (.inl ⟨node,body⟩ : Endpoint cut) : PlugSegment cut rhs)]).map
          (plugEnd (cut).label (rhs).label) := by
      simp only [physicalPrefix,List.map_append,List.map_cons,List.map_nil]
      rfl
    rw [represented]
    simp only [List.map_map,Function.comp_def,(plugEnd (cut).label (rhs).label).left_inv]
    simp
  change PlugExcursions cut rhs (physicalPrefix.map (plugEnd (cut).label (rhs).label).invFun) a actualMiddle at prefixShape
  rw [prefixRaw] at prefixShape
  have reflected := cutAt.prefixResidual.source_labels site prefixShape
  rw [beforeEq] at reflected
  have extended := prefixLabels.append_seam (Labelling.single (g:=site.net) (.inl ⟨.inl node,body⟩) middle) (by
    intro e f atE atF
    have sameE := Option.some.inj (atE.symm.trans prefixEnd)
    have sameF := (Option.some.inj atF).symm
    rw [sameE,sameF,Pairing.involutive]
    exact LabelledTurn.node (g:=site.net) (.inl node) ctx body (body_identity isLam ctxRole bodyRole middle))
  have same := reflected.output_unique extended
  rw [same] at targetPrefix targetSuffix
  obtain ⟨newPrefix,newPrefixEnd⟩ := Labelling.before_lambda_body (g:=site.reduce)
    (.inl node) ctx body isLam ctxRole bodyRole targetPrefix nonempty
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
  have suffixEnd : ((.inl ⟨.inl node,body⟩)::cutAt.after.map (plugEnd (cut).label (rhs).label)).getLast?=
      some (site.reduce.wire (.inl ⟨.inl node,bind⟩)) := by
    rw [fullSplit,List.getLast?_append] at finish
    cases atLast : ((.inl ⟨.inl node,body⟩)::cutAt.after.map (plugEnd (cut).label (rhs).label)).getLast? with
    | none => have empty := List.getLast?_eq_none_iff.mp atLast; cases empty
    | some e => simpa only [atLast,Option.some_or] using finish
  let newBinding : BindingLoop site.reduce ((.inl ⟨.inl node,body⟩)::cutAt.after.map (plugEnd (cut).label (rhs).label)) middle b :=
    ⟨.inl node,isLam,body,bind,bodyRole,bindRole,rfl,suffixEnd,targetSuffix,suffixForward,shell⟩
  exact ⟨_,_,fullSplit,newPrefix,newPrefixEnd,newBinding,rfl⟩

/-- Ordinary action Transparency at every retained lambda, for the original
target assignment and literal binder occurrence. Newly copied RHS lambdas
are deliberately outside this theorem's node type. -/
theorem PathSite.action_kept_transparency (action : IsAction s)
    {boundary : B → Bool} (flow : FlowBalance site.net boundary) (root : B) (positive : boundary root=true)
    (oldT : Transparency site.net root)
    (es : List (Endpoint site.reduce)) (a b : Context) (node : K)
    (ctx body bind : Port (kept node).sort) (isLam : (kept node).sort=.op .lam)
    (ctxRole : HEq ctx (Sum.inl () : Port (.op .lam))) (bodyRole : HEq body lamBody) (bindRole : HEq bind lamBind)
    (rooted : es.head?=some (.inr (.inl root)))
    (finish : es.getLast?=some (site.reduce.wire (.inl ⟨.inl node,bind⟩)))
    (forward : Forward site.reduce es) (labels : Labelling site.reduce es a b) :
    ∃ (pre loop : List (Endpoint site.reduce)) (middle : Context) (binding : BindingLoop site.reduce loop middle b),
      es=pre++loop ∧ binding.binder=.inl node ∧
      pre.getLast?=some (site.reduce.wire (.inl ⟨.inl node,ctx⟩)) ∧ Labelling site.reduce pre a middle := by
  let first : Endpoint cut := .inr (.inl (.inl root))
  let last : Endpoint cut := (cut).wire (.inl ⟨node,bind⟩)
  have targetEnd : es.getLast?=some (AG.plugLeft cut rhs last) := by
    rw [finish]
    exact congrArg some (plugLeft_wire cut rhs (.inl ⟨node,bind⟩))
  obtain ⟨principal,old,relation,oldLabels,oldRoot,oldLast⟩ :=
    site.action_canonical_ancestor action labels first last rooted targetEnd
  have oldFinish : old.getLast?=some (site.net.wire (.inl ⟨.inl node,bind⟩)) := by
    rw [←site.outsideEnd_wire] at oldLast
    exact oldLast
  have oldForward := oldLabels.root_forward_of_flow flow root oldRoot positive
  obtain ⟨pre,loop,middle,binding,split,binderEq,prefixEnd,prefixLabels⟩ :=
    oldT old a b (.inl node) ctx body bind isLam ctxRole bodyRole bindRole oldRoot oldFinish oldForward oldLabels
  obtain ⟨newPre,newLoop,newSplit,newLabels,newEnd,newBinding,newBinder⟩ :=
    relation.kept_binding_prefix site root
      (by simpa only [plug_decomposition_flatten] using labels)
      (by simpa only [plug_decomposition_flatten] using rooted)
      (by simpa only [plug_decomposition_flatten] using forward)
      pre loop split binding node binderEq ctx ctxRole prefixEnd prefixLabels bind bindRole
      (by simpa only [plug_decomposition_flatten] using finish)
  refine ⟨newPre,newLoop,middle,newBinding,?_,newBinder,newEnd,newLabels⟩
  simpa only [plug_decomposition_flatten] using newSplit
end
end Lamping.AG
