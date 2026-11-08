import Lamping.Lamping.CancellationSourceContraction
import Lamping.Lamping.CancellationResidualReplay
import Lamping.Lamping.BackwardPathDeterminism
import Lamping.Lamping.TraceSeams
namespace Lamping.AG
open Graph

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

/-- Actual cancellation preserves Transparency with the original root
assignment and binder occurrence. Contract the old prefix and binding loop
separately; rooted terminal uniqueness identifies their spliced target path
with the very target path supplied by the caller. -/
theorem PathSite.cancellation_transparency (cancel : IsCancellation s)
    {boundary : B → Bool} (flow : FlowBalance site.net boundary)
    (root : B) (positive : boundary root=true) (oldT : Transparency site.net root) :
    Transparency site.reduce root := by
  have empty : s.right.N → False := by cases cancel <;> exact Empty.elim
  obtain ⟨newFlow⟩ := site.reduce_flowBalance flow
  intro es a b node ctx body bind isLam ctxRole bodyRole bindRole rooted finish forward labels
  cases node with
  | inr node => exact False.elim (empty node)
  | inl node =>
    let c := cutFragment site.net (pathPartition s V) site.closed
    let r := s.right.net
    let first : Endpoint c := .inr (.inl (.inl root))
    let last : Endpoint c := c.wire (.inl ⟨node,bind⟩)
    have newFinish : es.getLast?=some (AG.plugLeft c r last) := by
      rw [finish]
      exact congrArg some (plugLeft_wire c r (.inl ⟨node,bind⟩))
    obtain ⟨ancestor,_residual,ancestorLabels,ancestorHead,ancestorLast,_replay⟩ :=
      site.cancellation_relabelling_ancestor cancel labels first last rooted newFinish
    have ancestorRoot : ancestor.head?=some (.inr (.inl root)) := ancestorHead
    have ancestorFinish : ancestor.getLast?=some (site.net.wire (.inl ⟨.inl node,bind⟩)) := by
      rw [←site.outsideEnd_wire] at ancestorLast
      exact ancestorLast
    have ancestorForward := ancestorLabels.root_forward_of_flow flow root ancestorRoot positive
    obtain ⟨pre,loop,middle,binding,oldSplit,binderEq,preEnd,preLabels⟩ := oldT
      ancestor a b (.inl node) ctx body bind isLam ctxRole bodyRole bindRole
      ancestorRoot ancestorFinish ancestorForward ancestorLabels
    rcases binding with ⟨binder,loopLam,loopBody,loopBind,loopBodyRole,loopBindRole,
      loopHead,loopEnd,loopLabels,_loopForward,shell⟩
    dsimp at binderEq
    cases binderEq
    have bodyEq : loopBody=body := eq_of_heq (loopBodyRole.trans bodyRole.symm)
    have bindEq : loopBind=bind := eq_of_heq (loopBindRole.trans bindRole.symm)
    subst loopBody
    subst loopBind
    have preRoot : pre.head?=some (.inr (.inl root)) := by
      cases pre with
      | nil => cases preEnd
      | cons e rest => simpa only [oldSplit,List.cons_append,List.head?_cons] using ancestorRoot
    have preTyped : ∃ k,accessKind site.net pre=some k := by
      refine ⟨.lam,?_⟩
      simp only [accessKind,preEnd,Option.bind_some,Pairing.involutive]
      exact lambda_ctx_kind _ ctx isLam ctxRole
    have loopTyped : ∃ k,accessKind site.net loop=some k := by
      refine ⟨.var,?_⟩
      simp only [accessKind,loopEnd,Option.bind_some,Pairing.involutive]
      exact lambda_bind_kind _ bind isLam bindRole
    obtain ⟨newPre,newPreLabels,_preResidual,newPreRoot,newPreEnd⟩ :=
      site.cancellation_source_contraction cancel preLabels preTyped first
        (c.wire (.inl ⟨node,ctx⟩)) preRoot (by
          rw [←site.outsideEnd_wire]; exact preEnd)
    obtain ⟨newLoop,newLoopLabels,_loopResidual,newLoopHead,newLoopEnd⟩ :=
      site.cancellation_source_contraction cancel loopLabels loopTyped (.inl ⟨node,body⟩)
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
    have wholeEnd : (newPre++newLoop).getLast?=es.getLast? := by
      rw [List.getLast?_append,newBindEnd,Option.some_or,finish]
    have wholeForward := whole.root_forward_of_flow newFlow root wholeRoot positive
    obtain ⟨same,_⟩ := Labelling.rooted_terminal_unique site.reduce whole wholeForward wholeRoot
      labels forward rooted wholeEnd
    have bodyAt : (newPre++newLoop)[newPre.length]?=some (.inl ⟨.inl node,body⟩) := by
      rw [List.getElem?_append_right (Nat.le_refl _),Nat.sub_self]
      simpa only [List.head?_eq_getElem?] using newLoopHead
    have loopForward := wholeForward.suffix_at newPre.length _ bodyAt
    simp only [List.drop_append,List.drop_length,Nat.sub_self,List.drop_zero,List.nil_append] at loopForward
    let newBinding : BindingLoop site.reduce newLoop middle b := {
      binder := .inl node
      isLam := isLam
      body := body
      bind := bind
      body_role := bodyRole
      bind_role := bindRole
      start := newLoopHead
      finish := newBindEnd
      proper := newLoopLabels
      forward := loopForward
      shell := shell }
    exact ⟨newPre,newLoop,middle,newBinding,same.symm,rfl,newCtxEnd,newPreLabels⟩
end
end Lamping.AG

