import Lamping.Lambda.SourceBinderOccurrences
namespace Lamping.Lambda.Labelled

/-- The environment records exactly the lambda-body turns on this actual
syntax descent, in addition to the supplied outside environment. -/
theorem SourceSubterm.environment_length
    (atSite : SourceSubterm outerEnv outerCtx t p env ctx sub) :
    env.length=outerEnv.length+binderDepth p := by
  exact atSite.env_length

/-- Every variable in a closed currently labelled term names an actual
lexical lambda on the same literal path. Labels may repeat or be compound. -/
theorem LTerm.closed_variable_binder {t : LTerm}
    (closed : Closed t.erase) (lookup : t.subterm leaf=some (.var stamp index)) :
    ∃ parent tail origin body,
      leaf=parent++(.body::tail) ∧
      t.subterm parent=some (.lam origin body) ∧
      body.subterm tail=some (.var stamp index) ∧
      subtermAt body.erase tail=some (.var (binderDepth tail)) ∧
      index=binderDepth tail := by
  obtain ⟨env,ctx,atSite⟩ := SourceSubterm.of_lookup t lookup [] .external
  have erased : subtermAt t.erase leaf=some (.var index) := by
    rw [←LTerm.erase_subterm,lookup]; rfl
  have scopedLeaf := scoped_subterm closed erased
  have bound : index<env.length := by
    have lengths := atSite.env_length
    change index<0+binderDepth leaf at scopedLeaf
    simp only [List.length_nil,Nat.zero_add] at lengths
    omega
  cases entry : env[index]? with
  | none =>
    have outside : env.length≤index := List.getElem?_eq_none_iff.mp entry
    omega
  | some origin =>
    obtain ⟨parent,tail,body,split,atParent,depth⟩ := atSite.bound_binder_occurrence entry
    have inside : body.subterm tail=some (.var stamp index) := by
      rw [split,LTerm.subterm_append,atParent,Option.bind_some] at lookup
      exact lookup
    refine ⟨parent,tail,origin,body,split,atParent,inside,?_,depth⟩
    rw [←LTerm.erase_subterm,inside]
    simp only [Option.map_some,LTerm.erase,depth]

/-- Scope is transported by the actual labelled history, with no relabelling
or INIT assumption on any reduct. -/
theorem History.closed (history : History ps t u) (closed : Closed t.erase) : Closed u.erase := by
  induction history with
  | nil => exact closed
  | cons step _ ih => exact ih (step.betaAt.beta.scoped closed)

end Lamping.Lambda.Labelled





