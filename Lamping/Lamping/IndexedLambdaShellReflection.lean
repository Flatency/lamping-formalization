import Lamping.Lamping.PathShellReflection
namespace Lamping.AG
open Graph
section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable {g : Net signature N B W} {root : B}

/-- Reflect the active application shell to the selected earlier lambda
occurrence using structural tail synchronization. The actual suffix starts
at its body turn in both assignments; no full Independence is used. -/theorem IndexedLevelBalance.reflect_lambda_prefix {heights : B → Int}
    (balance : IndexedLevelBalance g heights) (rootDepth : heights root=0) (edge : BetaEdge g)
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
  exact balance.reflect_shell root rootDepth _ (.inl ⟨node,body⟩) (.inl ⟨edge.app,edge.appCtx⟩) .lamBody .appCtx level edge.index
    middle output changedMiddle changedOutput rfl suffixEnd
    (.lamBody node body level lab bodyRole) trivial
    (.appCtx edge.app edge.appCtx edge.index edge.appLabel edge.appCtx_role) trivial
    suffixForward suffix changedSuffix shell
end
end Lamping.AG





