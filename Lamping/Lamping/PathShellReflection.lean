import Lamping.Lamping.InitialPathConstruction
import Lamping.Lamping.TraceSeams
import Lamping.Lamping.ExpandedLabelSurgery
import Lamping.Lamping.HighTailTransport
namespace Lamping.AG
open Graph
section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable {g : Net signature N B W} {root : B}

/-- The synchronization clause reflects a low terminal shell backwards along
this SAME actual forward proper path. The two inputs may differ, and the
source and target indices need not be ordered. -/
theorem Independence.reflect_shell (independence : Independence g root)
    (es : List (Endpoint g)) (start finish : Endpoint g) (sourceRole targetRole : ProperRole)
    (sourceIndex targetIndex : Nat) (a b changedA changedB : Context)
    (head : es.head?=some start) (last : es.getLast?=some (g.wire finish))
    (atStart : AtProperRole g root start sourceRole sourceIndex) (outgoing : sourceRole.outgoing)
    (atFinish : AtProperRole g root finish targetRole targetIndex) (incoming : targetRole.incoming)
    (forward : Forward g es) (labels : Labelling g es a b) (changed : Labelling g es changedA changedB)
    (shell : Context.SameShell (targetRole.terminalWidth targetIndex) b changedB) : Context.SameShell sourceIndex a changedA := by
  obtain ⟨_,width,bound,strict,fixed,sync⟩ := independence es start finish sourceRole targetRole
    sourceIndex targetIndex a b head last atStart outgoing atFinish incoming forward labels
  have moved := sync (changedB.tail (targetRole.terminalWidth targetIndex))
  change Labelling g es (a.replace width (changedB.tail (targetRole.terminalWidth targetIndex)))
    (b.replace (targetRole.terminalWidth targetIndex) (changedB.tail (targetRole.terminalWidth targetIndex))) at moved
  rw [Context.replace_of_sameShell b changedB (targetRole.terminalWidth targetIndex) shell] at moved
  have inputEq := moved.reverse.output_unique changed.reverse
  intro k low
  rw [←inputEq,Context.replace_low _ _ (by omega : k<width)]

/-- The same reflection already follows from actual indexed graph balance:
no arbitrary-input existence or rooted access assumption is used. -/
theorem IndexedLevelBalance.reflect_shell {boundary : B → Int} (balance : IndexedLevelBalance g boundary) (root : B)
    (rootDepth : boundary root=0)
    (es : List (Endpoint g)) (start finish : Endpoint g) (sourceRole targetRole : ProperRole)
    (sourceIndex targetIndex : Nat) (a b changedA changedB : Context)
    (head : es.head?=some start) (last : es.getLast?=some (g.wire finish))
    (atStart : AtProperRole g root start sourceRole sourceIndex) (outgoing : sourceRole.outgoing)
    (atFinish : AtProperRole g root finish targetRole targetIndex) (incoming : targetRole.incoming)
    (forward : Forward g es) (labels : Labelling g es a b) (changed : Labelling g es changedA changedB)
    (shell : Context.SameShell (targetRole.terminalWidth targetIndex) b changedB) : Context.SameShell sourceIndex a changedA := by
  obtain ⟨width,bound,strict,fixed,sync⟩ := balance.independence_tail root rootDepth es start finish sourceRole targetRole
    sourceIndex targetIndex a b head last atStart outgoing atFinish incoming forward labels
  have moved := sync (changedB.tail (targetRole.terminalWidth targetIndex))
  rw [Context.replace_of_sameShell b changedB (targetRole.terminalWidth targetIndex) shell] at moved
  have inputEq := moved.reverse.output_unique changed.reverse
  intro k low
  rw [←inputEq,Context.replace_low _ _ (by omega : k<width)]

private theorem lambda_body_identity {kind : Kind} {index : Nat} {ctx body : Port kind}
    (sort : kind=.op .lam) (ctxRole : HEq ctx (Sum.inl () : Port (.op .lam))) (bodyRole : HEq body lamBody)
    (context : Context) : Traversal index kind ctx body context context := by
  subst kind
  have ctxEq : ctx=.inl () := eq_of_heq ctxRole
  have bodyEq : body=lamBody := eq_of_heq bodyRole
  subst ctx
  subst body
  exact .direct (.lamBody context)

/-- The specified lambda occurrence's unchanged body turn identifies the
seam of the actual suffix. No prefix/completion witness is chosen anew. -/
theorem Labelling.after_lambda_context
    (node : N) (ctx body : Port (g.label node).sort) (sort : (g.label node).sort=.op .lam)
    (ctxRole : HEq ctx (Sum.inl () : Port (.op .lam))) (bodyRole : HEq body lamBody)
    (pre tail : List (Endpoint g)) (a middle b : Context)
    (prefixLabels : Labelling g pre a middle)
    (prefixEnd : pre.getLast?=some (g.wire (.inl ⟨node,ctx⟩)))
    (labels : Labelling g (pre++(.inl ⟨node,body⟩)::tail) a b) :
    Labelling g ((.inl ⟨node,body⟩)::tail) middle b := by
  have rule := lambda_body_identity (index:=(g.label node).index) sort ctxRole bodyRole middle
  have extended := prefixLabels.append_seam (Labelling.single (g:=g) (.inl ⟨node,body⟩) middle) (by
    intro e f atE atF
    have eEq : e=g.wire (.inl ⟨node,ctx⟩) := Option.some.inj (atE.symm.trans prefixEnd)
    have fEq : f=(.inl ⟨node,body⟩ : Endpoint g) := (Option.some.inj atF).symm
    rw [eEq,fEq,Pairing.involutive]
    exact LabelledTurn.node node ctx body rule)
  obtain ⟨actual,first,after⟩ := labels.split_segment
  have same := first.output_unique extended
  rw [same] at after
  exact after

/-- The difficult pre-detour binder case reduces to an ordinary suffix:
the active app shell reflects to the SAME earlier lambda occurrence, even
when the root assignments differ and the lambda index exceeds the app's. -/
theorem Independence.reflect_lambda_prefix (independence : Independence g root) (edge : BetaEdge g)
    (node : N) (ctx body : Port (g.label node).sort) (level : Nat) (lab : g.label node=label .lam level)
    (ctxRole : HEq ctx (Sum.inl () : Port (.op .lam))) (bodyRole : HEq body lamBody)
    (pre tail : List (Endpoint g)) (a middle output changedA changedMiddle changedOutput : Context)
    (prefixLabels : Labelling g pre a middle) (changedPrefix : Labelling g pre changedA changedMiddle)
    (prefixEnd : pre.getLast?=some (g.wire (.inl ⟨node,ctx⟩)))
    (labels : Labelling g (pre++(.inl ⟨node,body⟩)::tail) a output)
    (changed : Labelling g (pre++(.inl ⟨node,body⟩)::tail) changedA changedOutput)
    (forward : Forward g (pre++(.inl ⟨node,body⟩)::tail))
    (finish : (pre++(.inl ⟨node,body⟩)::tail).getLast?=some (g.wire (.inl ⟨edge.app,edge.appCtx⟩)))
    (shell : Context.SameShell edge.index output changedOutput) : Context.SameShell level middle changedMiddle := by
  have suffix := Labelling.after_lambda_context node ctx body (congrArg Label.sort lab) ctxRole bodyRole pre tail
    a middle output prefixLabels prefixEnd labels
  have changedSuffix := Labelling.after_lambda_context node ctx body (congrArg Label.sort lab) ctxRole bodyRole pre tail
    changedA changedMiddle changedOutput changedPrefix prefixEnd changed
  have point : (pre++(.inl ⟨node,body⟩)::tail)[pre.length]?=some (.inl ⟨node,body⟩) := by
    rw [List.getElem?_append_right (Nat.le_refl _),Nat.sub_self]
    rfl
  have suffixForward := forward.suffix_at pre.length _ point
  simp only [List.drop_append,List.drop_length,Nat.sub_self,List.drop_zero,List.nil_append] at suffixForward
  have suffixEnd : ((.inl ⟨node,body⟩)::tail).getLast?=some (g.wire (.inl ⟨edge.app,edge.appCtx⟩)) := by
    rw [List.getLast?_append] at finish
    cases atLast : ((.inl ⟨node,body⟩)::tail).getLast? with
    | none => have empty := List.getLast?_eq_none_iff.mp atLast; cases empty
    | some last => simpa only [atLast,Option.some_or] using finish
  exact independence.reflect_shell _ (.inl ⟨node,body⟩) (.inl ⟨edge.app,edge.appCtx⟩) .lamBody .appCtx level edge.index
    middle output changedMiddle changedOutput rfl suffixEnd
    (.lamBody node body level lab bodyRole) trivial
    (.appCtx edge.app edge.appCtx edge.index edge.appLabel edge.appCtx_role) trivial
    suffixForward suffix changedSuffix shell
end
end Lamping.AG




