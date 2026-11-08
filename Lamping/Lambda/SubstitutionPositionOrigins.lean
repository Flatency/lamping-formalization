import Lamping.Lambda.ArgumentCopies
import Lamping.Lambda.ArgumentResidualScope
namespace Lamping.Lambda
/-- An actual substituted node comes either from the same nonvariable source
node, or from a real source variable leaf followed by a path in its correctly
lifted replacement. This is only syntax lookup, not a graph ancestor assertion. -/
theorem subtermAt_subst_origins {t u : Term} {p : Path} {sigma : Nat → Term}
    (lookup : subtermAt (subst sigma t) p=some u) :
    (∃ old,subtermAt t p=some old ∧ (∀ k,old≠.var k) ∧
      u=subst (liftSubN (binderDepth p) sigma) old) ∨
    (∃ q r k,p=q++r ∧ subtermAt t q=some (.var k) ∧
      subtermAt (liftSubN (binderDepth q) sigma k) r=some u) := by
  induction t generalizing p sigma with
  | var k => exact Or.inr ⟨[],p,k,rfl,rfl,lookup⟩
  | app f a hf ha =>
    cases p with
    | nil =>
      refine Or.inl ⟨.app f a,rfl,?_,?_⟩
      · intro k eq; cases eq
      · exact (Option.some.inj lookup).symm
    | cons step rest =>
      cases step with
      | body => simp [subst,subtermAt] at lookup
      | fn =>
        rcases hf lookup with ⟨old,atOld,nonvar,eq⟩ | ⟨q,r,k,split,atVar,atReplacement⟩
        · exact Or.inl ⟨old,atOld,nonvar,eq⟩
        · exact Or.inr ⟨.fn::q,r,k,congrArg (Step.fn::·) split,atVar,atReplacement⟩
      | arg =>
        rcases ha lookup with ⟨old,atOld,nonvar,eq⟩ | ⟨q,r,k,split,atVar,atReplacement⟩
        · exact Or.inl ⟨old,atOld,nonvar,eq⟩
        · exact Or.inr ⟨.arg::q,r,k,congrArg (Step.arg::·) split,atVar,atReplacement⟩
  | lam body ih =>
    cases p with
    | nil =>
      refine Or.inl ⟨.lam body,rfl,?_,?_⟩
      · intro k eq; cases eq
      · exact (Option.some.inj lookup).symm
    | cons step rest =>
      cases step with
      | fn => simp [subst,subtermAt] at lookup
      | arg => simp [subst,subtermAt] at lookup
      | body =>
        rcases ih lookup with ⟨old,atOld,nonvar,eq⟩ | ⟨q,r,k,split,atVar,atReplacement⟩
        · exact Or.inl ⟨old,atOld,nonvar,by simpa only [binderDepth,liftSubN_shift] using eq⟩
        · refine Or.inr ⟨.body::q,r,k,congrArg (Step.body::·) split,atVar,?_⟩
          simpa only [binderDepth,liftSubN_shift] using atReplacement
/-- A variable is a leaf: a genuine source lookup below it has no suffix. -/
theorem variable_descendant_lookup {t u : Term} {q r : Path} {k : Nat}
    (atVariable : subtermAt t q=some (.var k))
    (lookup : subtermAt t (q++r)=some u) : r=[] ∧ u=.var k := by
  rw [subtermAt_append,atVariable,Option.bind_some] at lookup
  cases r with
  | nil => exact ⟨rfl,(Option.some.inj lookup).symm⟩
  | cons step rest => cases step <;> simp [subtermAt] at lookup
/-- Two source variable prefixes of one target path are the very same source
occurrence and index, with exactly the same replacement-relative path. -/
theorem variable_origin_prefix_unique {t : Term} {q r other suffix : Path} {k j : Nat}
    (first : subtermAt t q=some (.var k)) (second : subtermAt t other=some (.var j))
    (split : q++r=other++suffix) : q=other ∧ r=suffix ∧ k=j := by
  have same : q=other := by
    rcases List.append_eq_append_iff.mp split with ⟨tail,eq,_⟩ | ⟨tail,eq,_⟩
    · exact variable_prefix_eq first second ⟨tail,eq⟩
    · exact (variable_prefix_eq second first ⟨tail,eq⟩).symm
  subst other
  have sameIndex : k=j := Term.var.inj (Option.some.inj (first.symm.trans second))
  exact ⟨rfl,List.append_cancel_left split,sameIndex⟩
/-- The preserved nonvariable case cannot also lie in a replacement. -/
theorem nonvariable_origin_not_variable_prefix {t old : Term} {p q r : Path} {k : Nat}
    (atOld : subtermAt t p=some old) (nonvariable : ∀ j,old≠.var j)
    (atVariable : subtermAt t q=some (.var k)) (split : p=q++r) : False := by
  rw [split] at atOld
  exact nonvariable k (variable_descendant_lookup atVariable atOld).2
/-- Conversely, a real variable occurrence and actual lifted replacement
lookup give the exact target lookup, retaining both source and relative paths. -/
theorem subtermAt_subst_from_variable {t u : Term} {q r : Path} {k : Nat} {sigma : Nat → Term}
    (atVariable : subtermAt t q=some (.var k))
    (replacement : subtermAt (liftSubN (binderDepth q) sigma k) r=some u) :
    subtermAt (subst sigma t) (q++r)=some u := by
  rw [subtermAt_append,subtermAt_subst atVariable sigma,Option.bind_some]
  exact replacement
end Lamping.Lambda

