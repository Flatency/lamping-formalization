import Lamping.Lamping.ActionOccurrenceWords
import Lamping.Lamping.ActionKeptTransparency
namespace Lamping.AG
open Graph Lambda
private theorem suffix_of_binder_eq
    {N D U : Type} [FiniteNames N] [FiniteNames D] [FiniteNames U]
    {g : Net signature N D U} {es pre loop : List (Endpoint g)} {a middle b : Context}
    (binding : BindingLoop g loop middle b) (node : N) (binderEq : binding.binder=node)
    (ctx : Port (g.label node).sort) (role : HEq ctx (Sum.inl () : Port (.op .lam)))
    (split : es=pre++loop) (last : pre.getLast?=some (g.wire (.inl ⟨node,ctx⟩)))
    (labels : Labelling g pre a middle) : BindingSuffix g es (binderDepth (accessWord g loop)) := by
  rcases binding with ⟨binder,isLam,body,bind,bodyRole,bindRole,start,finish,proper,forward,shell⟩
  dsimp at binderEq
  subst binder
  exact ⟨pre,loop,a,middle,b,
    ⟨node,isLam,body,bind,bodyRole,bindRole,start,finish,proper,forward,shell⟩,
    ctx,split,role,last,labels,rfl⟩
section
variable {s : Schema} {K B W V : Type} [FiniteNames K] [FiniteNames B]
  [FiniteNames W] [FiniteNames V] {kept : K → Label signature}
variable (site : PathSite s kept (B:=B) (W:=W) (V:=V))
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

/-- Retained-binder transparency with the exact suffix word. The proof
uses the original selected source binder occurrence and the actual canonical
whole/prefix word equations; it never chooses a binder by its kind. -/
theorem ActionCanonicalBlocks.kept_binding_prefix_word {principal : SiteActionPrincipal site} {raw old}
    (relation : ActionCanonicalBlocks site principal raw old)
    (root : B) {a middle b : Context}
    (labels : Labelling site.reduce (raw.map (plugEnd (cut).label (rhs).label)) a b)
    (rooted : (raw.map (plugEnd (cut).label (rhs).label)).head?=some (.inr (.inl root)))
    (forward : Forward site.reduce (raw.map (plugEnd (cut).label (rhs).label)))
    (shape : PlugExcursions cut rhs raw a b)
    (rawHead : raw.head?=some (.inl (.inr (.inl (.inl root)))))
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
      ∃ targetBinding : BindingLoop site.reduce targetLoop middle b,targetBinding.binder=.inl node ∧
        accessWord site.reduce targetLoop=accessWord site.net loop := by
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
  have words := cutAt.suffix_word site relation shape (.inr (.inl (.inl root))) rawHead
  rw [afterEq] at words
  exact ⟨_,_,fullSplit,newPrefix,newPrefixEnd,newBinding,rfl,by simpa only [loopSplit] using words⟩

/-- Actual retained binding endpoints have source and target binding suffixes
with the same index, selected from the original source T decomposition. -/
theorem PathSite.action_kept_binding_suffix_word (action : IsAction s)
    {boundary : B → Bool} (flow : FlowBalance site.net boundary)
    (root : B) (positive : boundary root=true) (oldT : Transparency site.net root)
    (target : RootAccess site.reduce root) (node : K)
    (ctx body bind : Port (kept node).sort) (isLam : (kept node).sort=.op .lam)
    (ctxRole : HEq ctx (Sum.inl () : Port (.op .lam)))
    (bodyRole : HEq body lamBody) (bindRole : HEq bind lamBind)
    (finish : target.val.getLast?=some (site.reduce.wire (.inl ⟨.inl node,bind⟩))) :
    ∃ source : RootAccess site.net root,
      accessWord site.net source.val=accessWord site.reduce target.val ∧
      accessKind site.net source.val=accessKind site.reduce target.val ∧
      ∃ index,BindingSuffix site.net source.val index ∧BindingSuffix site.reduce target.val index := by
  let first : Endpoint cut := .inr (.inl (.inl root))
  let last : Endpoint cut := (cut).wire (.inl ⟨node,bind⟩)
  obtain ⟨a,b,labels⟩ := target.property.1.1
  have rooted : target.val.head?=some (AG.plugLeft cut rhs first) := target.property.2.1
  have targetEnd : target.val.getLast?=some (AG.plugLeft cut rhs last) := by
    rw [finish]
    exact congrArg some (plugLeft_wire cut rhs (.inl ⟨node,bind⟩))
  obtain ⟨principal,old,relation,oldLabels,oldRoot,oldLast⟩ :=
    site.action_canonical_ancestor action labels first last rooted targetEnd
  have shape := labels.local_excursions cut rhs first last rooted targetEnd
  have rawHead : (target.val.map (plugEnd (cut).label (rhs).label).invFun).head?=some (.inl first) := by
    rw [List.head?_map,rooted]
    exact congrArg some ((plugEnd (cut).label (rhs).label).left_inv (.inl first))
  have oldFinish : old.getLast?=some (site.net.wire (.inl ⟨.inl node,bind⟩)) := by
    rw [←site.outsideEnd_wire] at oldLast
    exact oldLast
  have sourceRoot : old.head?=some (.inr (.inl root)) := oldRoot
  have oldForward := oldLabels.root_forward_of_flow flow root sourceRoot positive
  obtain ⟨pre,loop,middle,binding,split,binderEq,prefixEnd,prefixLabels⟩ :=
    oldT old a b (.inl node) ctx body bind isLam ctxRole bodyRole bindRole
      sourceRoot oldFinish oldForward oldLabels
  obtain ⟨newPre,newLoop,newSplit,newLabels,newEnd,newBinding,newBinder,loopWord⟩ :=
    relation.kept_binding_prefix_word site root
      (by simpa only [plug_decomposition_flatten] using labels)
      (by simpa only [plug_decomposition_flatten] using target.property.2.1)
      (by simpa only [plug_decomposition_flatten] using target.property.1.2)
      shape rawHead pre loop split binding node binderEq ctx ctxRole prefixEnd prefixLabels bind bindRole
      (by simpa only [plug_decomposition_flatten] using finish)
  have word := relation.word site shape
  rw [plug_decomposition_flatten] at word newSplit
  have kind : accessKind site.net old=accessKind site.reduce target.val := by
    simp only [accessKind,oldFinish,finish,Option.bind_some,Pairing.involutive]
    rfl
  have typed : ∃ observation,accessKind site.net old=some observation := by
    rw [kind]; exact target.property.2.2
  let source : RootAccess site.net root :=
    ⟨old,⟨⟨⟨a,b,oldLabels⟩,oldForward⟩,sourceRoot,typed⟩⟩
  refine ⟨source,word.symm,kind,binderDepth (accessWord site.net loop),?_,?_⟩
  · exact suffix_of_binder_eq binding (.inl node) binderEq ctx ctxRole split prefixEnd prefixLabels
  · have suffix := suffix_of_binder_eq newBinding (.inl node) newBinder ctx ctxRole newSplit newEnd newLabels
    simpa only [loopWord] using suffix
end
end Lamping.AG
