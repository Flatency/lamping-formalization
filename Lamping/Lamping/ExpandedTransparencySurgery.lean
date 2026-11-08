import Lamping.Lamping.PathShellReflection
import Lamping.Lamping.CoherentExpandedPaths
namespace Lamping.AG
open Graph
section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable {g : Net signature N B W}

theorem ExpandedForward.suffix_at {es : List (Endpoint g)} (forward : ExpandedForward g es)
    (index : Nat) (e : Endpoint g) (atE : es[index]?=some e) : ExpandedForward g (es.drop index) := by
  induction forward generalizing index with
  | single x =>
    cases index with
    | zero => exact .single x
    | succ n => cases atE
  | cons turn tail ih =>
    cases index with
    | zero => exact .cons turn tail
    | succ n => exact ih n atE

private theorem body_identity {kind : Kind} {index : Nat} {ctx body : Port kind}
    (sort : kind=.op .lam) (ctxRole : HEq ctx (Sum.inl () : Port (.op .lam))) (bodyRole : HEq body lamBody)
    (context : Context) : Traversal index kind ctx body context context := by
  subst kind
  have ctxEq : ctx=.inl () := eq_of_heq ctxRole
  have bodyEq : body=lamBody := eq_of_heq bodyRole
  subst ctx
  subst body
  exact .direct (.lamBody context)

/-- The body occurrence inherits exactly the context on the given preceding
lambda context prefix, including when that prefix itself is expanded. -/
theorem ExpandedLabelling.after_lambda_context
    (node : N) (ctx body : Port (g.label node).sort) (sort : (g.label node).sort=.op .lam)
    (ctxRole : HEq ctx (Sum.inl () : Port (.op .lam))) (bodyRole : HEq body lamBody)
    (pre tail : List (Endpoint g)) (a middle b : Context)
    (prefixLabels : ExpandedLabelling g pre a middle)
    (prefixEnd : pre.getLast?=some (g.wire (.inl ⟨node,ctx⟩)))
    (labels : ExpandedLabelling g (pre++(.inl ⟨node,body⟩)::tail) a b) :
    ExpandedLabelling g ((.inl ⟨node,body⟩)::tail) middle b := by
  have rule := body_identity (index:=(g.label node).index) sort ctxRole bodyRole middle
  have extended := prefixLabels.splice prefixEnd (ExpandedLabelling.single (g:=g) (.inl ⟨node,body⟩) middle) rfl (by
    rw [Pairing.involutive]
    exact .ordinary (LabelledTurn.node node ctx body rule))
  obtain ⟨actual,first,after⟩ := labels.split_segment
  have same := first.output_unique extended
  rw [same] at after
  exact after

/-- A real whole expanded assignment and a selected original binder prefix
supply all loop labels/direction; only the actual same-assignment shell is
requested. No semantic loop or generation certificate is inserted. -/
theorem expanded_binding_suffix (node : N) (ctx body bind : Port (g.label node).sort)
    (sort : (g.label node).sort=.op .lam)
    (ctxRole : HEq ctx (Sum.inl () : Port (.op .lam))) (bodyRole : HEq body lamBody) (bindRole : HEq bind lamBind)
    (pre tail : List (Endpoint g)) (a middle b : Context)
    (labels : ExpandedLabelling g (pre++(.inl ⟨node,body⟩)::tail) a b)
    (forward : ExpandedForward g (pre++(.inl ⟨node,body⟩)::tail))
    (prefixLabels : ExpandedLabelling g pre a middle)
    (prefixEnd : pre.getLast?=some (g.wire (.inl ⟨node,ctx⟩)))
    (finish : (pre++(.inl ⟨node,body⟩)::tail).getLast?=some (g.wire (.inl ⟨node,bind⟩)))
    (shell : Context.SameShell (g.label node).index middle b) :
    ∃ binding : ExpandedBindingLoop g ((.inl ⟨node,body⟩)::tail) middle b,binding.binder=node := by
  have after := ExpandedLabelling.after_lambda_context node ctx body sort ctxRole bodyRole pre tail a middle b
    prefixLabels prefixEnd labels
  have point : (pre++(.inl ⟨node,body⟩)::tail)[pre.length]?=some (.inl ⟨node,body⟩) := by
    rw [List.getElem?_append_right (Nat.le_refl _),Nat.sub_self]
    rfl
  have suffixForward := forward.suffix_at pre.length _ point
  simp only [List.drop_append,List.drop_length,Nat.sub_self,List.drop_zero,List.nil_append] at suffixForward
  have suffixEnd : ((.inl ⟨node,body⟩)::tail).getLast?=some (g.wire (.inl ⟨node,bind⟩)) := by
    rw [List.getLast?_append] at finish
    cases last : ((.inl ⟨node,body⟩)::tail).getLast? with
    | none => have empty := List.getLast?_eq_none_iff.mp last; cases empty
    | some e => simpa only [last,Option.some_or] using finish
  exact ⟨⟨node,sort,body,bind,bodyRole,bindRole,rfl,suffixEnd,after,suffixForward,shell⟩,rfl⟩

/-- Two specified prefixes of one ordered list are comparable by actual
list extension, without identifying repeated endpoint occurrences. -/
theorem compare_path_prefixes {T : Type} (left right leftTail rightTail : List T)
    (same : left++leftTail=right++rightTail) :
    (∃ middle,right=left++middle ∧leftTail=middle++rightTail) ∨
      (∃ middle,left=right++middle ∧rightTail=middle++leftTail) := by
  induction left generalizing right with
  | nil => exact Or.inl ⟨right,rfl,same⟩
  | cons x left ih =>
    cases right with
    | nil => exact Or.inr ⟨x::left,rfl,same.symm⟩
    | cons y right =>
      obtain ⟨head,tail⟩ := List.cons.inj same
      subst y
      rcases ih right tail with ⟨middle,rightEq,tailEq⟩ |⟨middle,leftEq,tailEq⟩
      · exact Or.inl ⟨middle,congrArg (x::·) rightEq,tailEq⟩
      · exact Or.inr ⟨middle,congrArg (x::·) leftEq,tailEq⟩
end
end Lamping.AG
