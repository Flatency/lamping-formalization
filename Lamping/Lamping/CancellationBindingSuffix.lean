import Lamping.Lamping.CancellationRootWords
import Lamping.Lamping.BindingSuffixUniqueness
namespace Lamping.AG
open Graph Lambda
private theorem lambda_ctx_kind (k : Kind) (ctx : Port k) (isLam : k=.op .lam)
    (role : HEq ctx (Sum.inl () : Port (.op .lam))) : portKind k ctx=some .lam := by
  subst k
  have same : ctx=.inl () := eq_of_heq role
  subst ctx
  rfl

private theorem lambda_bind_kind (k : Kind) (bind : Port k) (isLam : k=.op .lam)
    (role : HEq bind lamBind) : portKind k bind=some .var := by
  subst k
  have same : bind=lamBind := eq_of_heq role
  subst bind
  rfl

private theorem lambda_body_turn (k : Kind) (i : Nat) (ctx body : Port k)
    (isLam : k=.op .lam) (ctxRole : HEq ctx (Sum.inl () : Port (.op .lam)))
    (bodyRole : HEq body lamBody) (a : Context) : Traversal i k ctx body a a := by
  subst k
  have hc : ctx=.inl () := eq_of_heq ctxRole
  have hb : body=lamBody := eq_of_heq bodyRole
  subst ctx
  subst body
  exact .direct (.lamBody a)

section
variable {s : Schema} {K B W V : Type} [FiniteNames K] [FiniteNames B]
  [FiniteNames W] [FiniteNames V] {kept : K → Label signature}
variable (site : PathSite s kept (B:=B) (W:=W) (V:=V))

/-- Preserve a genuine old binding suffix, its original seam assignment,
its literal loop word and hence its variable index under actual cancellation. -/
theorem PathSite.cancellation_binding_suffix (cancel : IsCancellation s)
    {boundary : B → Bool} (flow : FlowBalance site.net boundary)
    (root : B) (positive : boundary root=true) (source : RootAccess site.net root)
    {index : Nat} (suffix : BindingSuffix site.net source.val index) :
    ∃ reduced : RootAccess site.reduce root,
      accessWord site.reduce reduced.val=accessWord site.net source.val ∧
      accessKind site.reduce reduced.val=accessKind site.net source.val ∧
      BindingSuffix site.reduce reduced.val index := by
  obtain ⟨pre,loop,a,middle,b,binding,ctx,oldSplit,ctxRole,preEnd,preLabels,indexEq⟩ := suffix
  rcases binding with ⟨binder,isLam,body,bind,bodyRole,bindRole,loopHead,loopEnd,loopLabels,loopForward,shell⟩
  have keptBinder : ∃ node : K,binder=.inl node := by
    cases binder with
    | inl node => exact ⟨node,rfl⟩
    | inr node => cases node <;> rename_i tag <;> cases tag <;> cases cancel <;> cases isLam
  obtain ⟨node,sameBinder⟩ := keptBinder
  subst binder
  let c := cutFragment site.net (pathPartition s V) site.closed
  let r := s.right.net
  let first : Endpoint c := .inr (.inl (.inl root))
  obtain ⟨newFlow⟩ := site.reduce_flowBalance flow
  have preRoot : pre.head?=some (.inr (.inl root)) := by
    cases pre with
    | nil => cases preEnd
    | cons e rest => simpa only [oldSplit,List.cons_append,List.head?_cons] using source.property.2.1
  have preTyped : ∃ k,accessKind site.net pre=some k := by
    refine ⟨.lam,?_⟩
    simp only [accessKind,preEnd,Option.bind_some,Pairing.involutive]
    exact lambda_ctx_kind _ ctx isLam ctxRole
  have loopTyped : ∃ k,accessKind site.net loop=some k := by
    refine ⟨.var,?_⟩
    simp only [accessKind,loopEnd,Option.bind_some,Pairing.involutive]
    exact lambda_bind_kind _ bind isLam bindRole
  obtain ⟨newPre,newPreLabels,_preResidual,newPreRoot,newPreEnd,_preWord⟩ :=
    site.cancellation_source_word_contraction cancel preLabels
      (preLabels.root_forward_of_flow flow root preRoot positive) preTyped first
      (c.wire (.inl ⟨node,ctx⟩)) preRoot (by
        rw [←site.outsideEnd_wire]; exact preEnd)
  obtain ⟨newLoop,newLoopLabels,_loopResidual,newLoopHead,newLoopEnd,loopWord⟩ :=
    site.cancellation_source_word_contraction cancel loopLabels loopForward loopTyped (.inl ⟨node,body⟩)
      (c.wire (.inl ⟨node,bind⟩)) loopHead (by
        rw [←site.outsideEnd_wire]; exact loopEnd)
  change newPre.head?=some (.inr (.inl root)) at newPreRoot
  change newLoop.head?=some (.inl ⟨.inl node,body⟩) at newLoopHead
  have newCtxEnd : newPre.getLast?=some (site.reduce.wire (.inl ⟨.inl node,ctx⟩)) := by
    simpa only [←plugLeft_wire c r (.inl ⟨node,ctx⟩)] using newPreEnd
  have newBindEnd : newLoop.getLast?=some (site.reduce.wire (.inl ⟨.inl node,bind⟩)) := by
    simpa only [←plugLeft_wire c r (.inl ⟨node,bind⟩)] using newLoopEnd
  have whole : Labelling site.reduce (newPre++newLoop) a b := by
    obtain ⟨xs,preSplit⟩ := List.getLast?_eq_some_iff.mp newCtxEnd
    obtain ⟨ys,loopSplit⟩ := List.head?_eq_some_iff.mp newLoopHead
    have left : Labelling site.reduce (xs++[site.reduce.wire (.inl ⟨.inl node,ctx⟩)]) a middle :=
      by rw [←preSplit]; exact newPreLabels
    have right : Labelling site.reduce ((.inl ⟨.inl node,body⟩)::ys) middle b :=
      by rw [←loopSplit]; exact newLoopLabels
    have seam : LabelledTurn site.reduce
        (site.reduce.wire (site.reduce.wire (.inl ⟨.inl node,ctx⟩))) (.inl ⟨.inl node,body⟩) middle middle := by
      rw [Pairing.involutive]
      exact LabelledTurn.node (g:=site.reduce) (.inl node) ctx body (lambda_body_turn _ _ ctx body isLam ctxRole bodyRole middle)
    simpa only [preSplit,loopSplit,List.append_assoc,List.singleton_append] using left.splice right seam
  have wholeRoot : (newPre++newLoop).head?=some (.inr (.inl root)) := by
    cases newPre with
    | nil => cases newPreRoot
    | cons e rest => exact newPreRoot
  have wholeForward := whole.root_forward_of_flow newFlow root wholeRoot positive
  have bodyAt : (newPre++newLoop)[newPre.length]?=some (.inl ⟨.inl node,body⟩) := by
    rw [List.getElem?_append_right (Nat.le_refl _),Nat.sub_self]
    simpa only [List.head?_eq_getElem?] using newLoopHead
  have newLoopForward := wholeForward.suffix_at newPre.length _ bodyAt
  simp only [List.drop_append,List.drop_length,Nat.sub_self,List.drop_zero,List.nil_append] at newLoopForward
  let newBinding : BindingLoop site.reduce newLoop middle b := {
    binder := .inl node, isLam := isLam, body := body, bind := bind,
    body_role := bodyRole, bind_role := bindRole, start := newLoopHead,
    finish := newBindEnd, proper := newLoopLabels, forward := newLoopForward, shell := shell }
  have oldWhole : Labelling site.net source.val a b := by
    rw [oldSplit]
    exact BindingLoop.prefix_labelling
      (BindingLoop.mk (.inl node) isLam body bind bodyRole bindRole loopHead loopEnd loopLabels loopForward shell)
      ctx ctxRole preEnd preLabels
  have oldFinish : source.val.getLast?=some (site.net.wire (.inl ⟨.inl node,bind⟩)) := by
    rw [oldSplit,List.getLast?_append,loopEnd,Option.some_or]
  obtain ⟨again,againLabels,_residual,againRoot,againLast,word⟩ :=
    site.cancellation_source_word_contraction cancel oldWhole source.property.1.2 source.property.2.2
      first (c.wire (.inl ⟨node,bind⟩)) source.property.2.1 (by
        rw [←site.outsideEnd_wire]; exact oldFinish)
  change again.head?=some (.inr (.inl root)) at againRoot
  have againEnd : again.getLast?=some (site.reduce.wire (.inl ⟨.inl node,bind⟩)) := by
    simpa only [←plugLeft_wire c r (.inl ⟨node,bind⟩)] using againLast
  have wholeEnd : (newPre++newLoop).getLast?=some (site.reduce.wire (.inl ⟨.inl node,bind⟩)) := by
    rw [List.getLast?_append,newBindEnd,Option.some_or]
  have againForward := againLabels.root_forward_of_flow newFlow root againRoot positive
  obtain ⟨same,_⟩ := Labelling.rooted_terminal_unique site.reduce whole wholeForward wholeRoot
    againLabels againForward againRoot (wholeEnd.trans againEnd.symm)
  rw [←same] at word
  have kind : accessKind site.reduce (newPre++newLoop)=accessKind site.net source.val := by
    simp only [accessKind,wholeEnd,oldFinish,Option.bind_some,Pairing.involutive]
    rfl
  have typed : ∃ k,accessKind site.reduce (newPre++newLoop)=some k := by
    rw [kind]; exact source.property.2.2
  refine ⟨⟨newPre++newLoop,⟨⟨⟨a,b,whole⟩,wholeForward⟩,wholeRoot,typed⟩⟩,word,kind,?_⟩
  refine ⟨newPre,newLoop,a,middle,b,newBinding,ctx,rfl,ctxRole,newCtxEnd,newPreLabels,?_⟩
  exact indexEq.trans (congrArg binderDepth loopWord).symm
end
end Lamping.AG
