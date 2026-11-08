import Lamping.Lamping.InitialMatching
import Lamping.Lamping.GlobalPathInvariants
namespace Lamping.AG
open Graph Lambda
section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable {g : Net signature N B W}
/-- Split a supplied labelling across one specified concatenation seam,
retaining both actual seam contexts and the actual joining turn. -/
theorem Labelling.split_seam (pre loop : List (Endpoint g)) (e f : Endpoint g)
    (last : pre.getLast?=some e) (head : loop.head?=some f)
    (labels : Labelling g (pre++loop) a b) :
    ∃ c d,Labelling g pre a c ∧Labelling g loop d b ∧LabelledTurn g (g.wire e) f c d := by
  induction pre generalizing a with
  | nil => cases last
  | cons x rest ih =>
    cases rest with
    | nil =>
      have same : x=e := Option.some.inj last
      subst x
      cases loop with
      | nil => cases head
      | cons y tail =>
        have same : y=f := Option.some.inj head
        subst y
        cases labels with
        | cons turn after => exact ⟨_,_,.single _ _,after,turn⟩
    | cons y rest =>
      cases labels with
      | cons turn after =>
        obtain ⟨c,d,first,second,seam⟩ := ih
          (by simpa only [List.getLast?_cons_cons] using last) after
        exact ⟨c,d,.cons turn first,second,seam⟩
end
private theorem binding_kind (kind : Kind) (p : Port kind) (isLam : kind=.op .lam)
    (role : HEq p lamBind) : portKind kind p=some .var := by
  subst kind
  have same : p=lamBind := eq_of_heq role
  subst p
  rfl
private theorem last_append_nonempty {T : Type} (xs ys : List T) (nonempty : ys≠[]) :
    (xs++ys).getLast?=ys.getLast? := by
  rw [List.getLast?_append]
  cases h : ys.getLast? with
  | none => exact False.elim (nonempty (List.getLast?_eq_none_iff.mp h))
  | some => rfl

/-- Closed initial transparency preserves the originally supplied labelling,
including its exact input, final context and selected lambda-body seam. -/
theorem encode_closed_transparency (t : Term) (closed : Closed t) (level : Nat) :
    Transparency (encode level t).net (.inl ()) := by
  let g := (encode level t).net
  intro es a b n ctx body bind isLam ctxRole bodyRole bindRole rooted finish forward labels
  have kind : accessKind g es=some .var := by
    unfold accessKind
    rw [finish]
    simp only [g,Option.bind_some,Pairing.involutive]
    exact binding_kind _ bind isLam bindRole
  let access : RootAccess g (.inl ()) := ⟨es,⟨⟨⟨a,b,labels⟩,forward⟩,rooted,.var,kind⟩⟩
  obtain ⟨u,lookup,observes⟩ := encode_closed_access_observes t closed level access
  have suffix : ∃ k,BindingSuffix g es k := by
    cases u with
    | var k => exact ⟨k,observes.2.1⟩
    | app f arg =>
      have impossible := observes.1.symm.trans kind
      cases impossible
    | lam body =>
      have impossible := observes.1.symm.trans kind
      cases impossible
  obtain ⟨k,pre,loop,a0,c0,d0,binding,oldCtx,same,oldCtxRole,preLast,preLabels,index⟩ := suffix
  rcases binding with ⟨binder,binderLam,oldBody,oldBind,oldBodyRole,oldBindRole,
    loopHead,loopLast,loopLabels,loopForward,shell⟩
  have wholeLast := finish
  rw [same,last_append_nonempty _ _ loopLabels.nonempty,loopLast] at wholeLast
  have ends := Option.some.inj wholeLast
  have nodes : binder=n := by
    have physical := congrArg g.wire.mate ends
    simp only [g,Pairing.involutive] at physical
    exact congrArg Sigma.fst (Sum.inl.inj physical)
  subst binder
  have ctxSame : oldCtx=ctx := eq_of_heq (oldCtxRole.trans ctxRole.symm)
  subst oldCtx
  have actualLabels : Labelling g (pre++loop) a b := same ▸ labels
  obtain ⟨middle,after,first,last,seam⟩ := actualLabels.split_seam pre loop
    (g.wire (.inl ⟨n,ctx⟩)) (.inl ⟨n,oldBody⟩) preLast loopHead
  rw [Pairing.involutive] at seam
  have contexts : middle=after := by
    cases seam with
    | node node p q rule =>
      have equal := rule.proper_context
      simpa only [binderLam,ProperContextInvariant] using equal
  subst after
  let raw : InitialOffsets.RawLoop g loop middle b := {
    binder := n
    isLam := binderLam
    body := oldBody
    bind := oldBind
    body_role := oldBodyRole
    bind_role := oldBindRole
    start := loopHead
    finish := loopLast
    proper := last }
  exact ⟨pre,loop,middle,InitialOffsets.encode_rawLoop_binding t level loop middle b raw,
    same,rfl,preLast,first⟩
end Lamping.AG
