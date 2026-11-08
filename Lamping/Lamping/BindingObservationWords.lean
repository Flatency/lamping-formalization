import Lamping.Lamping.BackwardPathDeterminism
import Lamping.Lamping.MatchingVariableAccess

namespace Lamping.AG
open Graph Lambda

private theorem body_arrival (kind : Kind) (body : Port kind)
    (sort : kind=.op .lam) (role : HEq body lamBody) :
    (match kind,body with
      | .op .app,.inl () => [Step.fn]
      | .op .app,.inr true => [Step.arg]
      | .op .lam,.inr true => [Step.body]
      | _,_ => [])=[.body] := by
  subst kind
  cases eq_of_heq role
  rfl

section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable {g : Net signature N B W} {root : B}

/-- The same actual final context and kept lambda context identify the
literal binder prefix by backwards path determinism. Its syntax word then
determines the loop word and the exact de Bruijn index. This uses existing
whole/prefix paths and their actual labellings, with no target Matches. -/
theorem RootAccess.binding_suffix_of_same_seam
    (whole parent : RootAccess g root) (pre loop : List (Endpoint g))
    {input parentInput seam output : Context} (binding : BindingLoop g loop seam output)
    (ctx : Port (g.label binding.binder).sort) (ctxRole : HEq ctx (Sum.inl () : Port (.op .lam)))
    (split : whole.val=pre++loop) (preLabels : Labelling g pre input seam)
    (preEnd : pre.getLast?=some (g.wire (.inl ⟨binding.binder,ctx⟩)))
    (parentLabels : Labelling g parent.val parentInput seam)
    (parentEnd : parent.val.getLast?=some (g.wire (.inl ⟨binding.binder,ctx⟩)))
    (q : Path) (words : accessWord g whole.val=accessWord g parent.val++(.body::q)) :
    BindingSuffix g whole.val (binderDepth q) := by
  have nonempty : pre≠[] := by intro empty; rw [empty] at preEnd; cases preEnd
  have rooted : pre.head?=some (.inr (.inl root)) := by
    cases pre with
    | nil => exact False.elim (nonempty rfl)
    | cons first rest => simpa only [split,List.cons_append,List.head?_cons] using whole.property.2.1
  have forward := whole.property.1.2
  rw [split] at forward
  have prefixForward := forward.prefix_of_append nonempty
  have prefixSame : pre=parent.val :=
    (preLabels.rooted_terminal_unique g prefixForward rooted parentLabels parent.property.1.2
      parent.property.2.1 (preEnd.trans parentEnd.symm)).1
  have token : arrivalWord g (.inl ⟨binding.binder,binding.body⟩)=[.body] := by
    exact body_arrival _ _ binding.isLam binding.body_role
  obtain ⟨tail,loopSplit⟩ := List.head?_eq_some_iff.mp binding.start
  have loopWord : accessWord g loop=q := by
    rw [split,accessWord_append g pre loop nonempty,prefixSame,loopSplit] at words
    simp only [List.flatMap_cons,token,List.singleton_append] at words
    have suffixSame := List.append_cancel_left words
    simpa only [loopSplit,accessWord] using (List.cons.inj suffixSame).2
  exact ⟨pre,loop,input,seam,output,binding,ctx,split,ctxRole,preEnd,preLabels,by rw [loopWord]⟩

end
end Lamping.AG
