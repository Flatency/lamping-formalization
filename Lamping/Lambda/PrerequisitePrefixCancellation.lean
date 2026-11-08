import Lamping.Lambda.PrerequisitePrefixes
namespace Lamping.Lambda.Labelled

private theorem path_last_unique {p q : Path} {s u : Step}
    (same : p++[s]=q++[u]) : p=q ∧s=u := by
  have back := congrArg List.reverse same
  simp only [List.reverse_append,List.reverse_cons,List.reverse_nil,List.nil_append,
    List.singleton_append] at back
  exact ⟨List.reverse_inj.mp (List.cons.inj back).2,(List.cons.inj back).1⟩

theorem PrerequisitePrefix.cancel_successful_chain
    {t : LTerm} {start reader : Path} {before tail : List Path}
    (segment : PrerequisitePrefix t start before reader)
    (chain : PrerequisiteChain t start (before++tail)) :
    PrerequisiteChain t reader tail := by
  suffices ∀(cp : Path) (es : List Path),PrerequisiteChain t cp es →
      cp=start →es=before++tail →PrerequisiteChain t reader tail by
    exact this start (before++tail) chain rfl rfl
  clear chain
  induction segment generalizing tail with
  | refl =>
    intro cp es actual position words
    subst cp;subst es
    exact actual
  | @app p stamp fn arg edges finish lookup notLambda rest ih =>
    intro cp es actual position words
    cases actual with
    | redex_app atRedex =>
      have atSame := position ▸ atRedex
      have terms := Option.some.inj (lookup.symm.trans atSame)
      exact False.elim (notLambda _ _ (LTerm.app.inj terms).2.1)
    | @redex_lam q beta alpha redBody redArg atRedex =>
      have atFunction : t.subterm (q++[.fn])=some (.lam alpha redBody) := by
        rw [LTerm.subterm_append,atRedex];rfl
      have atSame := position ▸ atFunction
      rw [lookup] at atSame
      cases atSame
    | app atApp _ next =>
      have atSame := position ▸ atApp
      have terms := Option.some.inj (lookup.symm.trans atSame)
      have functions := (LTerm.app.inj terms).2.1
      have remaining := (List.cons.inj (by simpa only [List.cons_append] using words)).2
      exact ih _ _ next (congrArg (fun path=>path++[.fn]) position) remaining
    | lam atLambda _ _ =>
      have atSame := position ▸ atLambda
      rw [lookup] at atSame;cases atSame
    | var atVariable _ _ _ _ =>
      have atSame := position ▸ atVariable
      rw [lookup] at atSame;cases atSame
  | @lam parent step stamp body edges finish lookup notFunction rest ih =>
    intro cp es actual position words
    cases actual with
    | redex_app atRedex =>
      have atSame := position ▸ atRedex
      rw [lookup] at atSame;cases atSame
    | redex_lam atRedex =>
      have last := (path_last_unique position).2
      exact False.elim (notFunction last.symm)
    | app atApp _ _ =>
      have atSame := position ▸ atApp
      rw [lookup] at atSame;cases atSame
    | lam atLambda _ next =>
      have parents := (path_last_unique position).1
      have remaining := (List.cons.inj (by simpa only [List.cons_append] using words)).2
      exact ih _ _ next parents remaining
    | var atVariable _ _ _ _ =>
      have atSame := position ▸ atVariable
      rw [lookup] at atSame;cases atSame
  | @var leaf stamp index parent origin body suffix edges finish lookup binder split depth rest ih =>
    intro cp es actual position words
    cases actual with
    | redex_app atRedex =>
      have atSame := position ▸ atRedex
      rw [lookup] at atSame;cases atSame
    | @redex_lam q beta alpha redBody redArg atRedex =>
      have atFunction : t.subterm (q++[.fn])=some (.lam alpha redBody) := by
        rw [LTerm.subterm_append,atRedex];rfl
      have atSame := position ▸ atFunction
      rw [lookup] at atSame;cases atSame
    | app atApp _ _ =>
      have atSame := position ▸ atApp
      rw [lookup] at atSame;cases atSame
    | lam atLambda _ _ =>
      have atSame := position ▸ atLambda
      rw [lookup] at atSame;cases atSame
    | var atVariable _ otherSplit otherDepth next =>
      have atSame := position ▸ atVariable
      have terms := Option.some.inj (lookup.symm.trans atSame)
      obtain ⟨sameParent,_sameRest⟩ := binding_prefix_depth_unique
        (split.symm.trans (position.symm.trans otherSplit))
        (depth.symm.trans ((LTerm.var.inj terms).2.trans otherDepth))
      exact ih _ _ next sameParent.symm words

#print axioms PrerequisitePrefix.cancel_successful_chain
end Lamping.Lambda.Labelled
