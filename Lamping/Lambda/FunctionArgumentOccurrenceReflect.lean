import Lamping.Lambda.FunctionResidualGeometry
import Lamping.Lambda.ArgumentCopies
namespace Lamping.Lambda

private theorem occurrenceRenaming_free_iff (ρ : Nat → Nat) (p : Path) (i k : Nat) :
    occurrenceRenaming ρ p i = k + binderDepth p ↔
      ∃ j, i=j+binderDepth p ∧ ρ j=k := by
  induction p generalizing ρ i k with
  | nil => simp [occurrenceRenaming,binderDepth]
  | cons e p ih =>
    cases e with
    | fn => exact ih ρ i k
    | arg => exact ih ρ i k
    | body =>
      change occurrenceRenaming (liftRen ρ) p i = k+(binderDepth p+1) ↔ _
      rw [show k+(binderDepth p+1)=(k+1)+binderDepth p by omega,ih]
      constructor
      · rintro ⟨j,hj,hρ⟩
        cases j with
        | zero => simp [liftRen] at hρ
        | succ j =>
          refine ⟨j,by simpa only [binderDepth] using hj.trans (by omega),?_⟩
          simpa only [liftRen,Nat.add_right_cancel_iff] using hρ
      · rintro ⟨j,hj,hρ⟩
        exact ⟨j+1,by simp only [binderDepth] at hj; omega,by simp [liftRen,hρ]⟩

private theorem renamed_variable_source (ρ : Nat → Nat) (t : Term) (p : Path) (k : Nat)
    (h : subtermAt (rename ρ t) p=some (.var (k+binderDepth p))) :
    ∃ j, ρ j=k ∧ subtermAt t p=some (.var (j+binderDepth p)) := by
  rw [subtermAt_rename] at h
  cases lookup : subtermAt t p with
  | none => simp [lookup] at h
  | some x =>
    rw [lookup] at h
    cases x with
    | app f a => cases h
    | lam b => cases h
    | var i =>
      have value : occurrenceRenaming ρ p i=k+binderDepth p := Term.var.inj (Option.some.inj h)
      obtain ⟨j,hj,hρ⟩ := (occurrenceRenaming_free_iff ρ p i k).mp value
      exact ⟨j,hρ,by rw [hj]⟩

private theorem liftSubN_at (n : Nat) (σ : Nat → Term) (i : Nat) :
    liftSubN n σ i = if i<n then .var i else rename (fun j => j+n) (σ (i-n)) := by
  induction n generalizing i with
  | zero => simpa only [liftSubN,Nat.not_lt_zero,if_false,Nat.sub_zero,Nat.add_zero] using (rename_id (σ i)).symm
  | succ n ih =>
    cases i with
    | zero => simp [liftSubN,liftSub]
    | succ i =>
      simp only [liftSubN,liftSub,ih]
      by_cases small : i<n
      · simp [small,show i+1<n+1 by omega,rename]
      · simp only [small,if_false,show ¬ i+1<n+1 by omega]
        rw [rename_comp]
        rw [show i+1-(n+1)=i-n by omega]
        apply congrArg (fun z => rename z (σ (i-n)))
        funext j
        change j+n+1=j+(n+1)
        omega

/-- A substitution lifted past a protected variable cannot create an
occurrence of that variable, even inside a substituted external term. -/
theorem subst_protected_occurrence_reflect (t : Term) (σ : Nat → Term)
    (n k : Nat) (bounded : k<n) (p : Path)
    (h : subtermAt (subst (liftSubN n σ) t) p=some (.var (k+binderDepth p))) :
    subtermAt t p=some (.var (k+binderDepth p)) := by
  induction t generalizing n k p with
  | var i =>
    change subtermAt (liftSubN n σ i) p=_ at h
    rw [liftSubN_at] at h
    by_cases small : i<n
    · rw [if_pos small] at h
      exact h
    · rw [if_neg small] at h
      obtain ⟨j,hj,_⟩ := renamed_variable_source _ _ _ _ h
      omega
  | app f a hf ha =>
    cases p with
    | nil => cases h
    | cons e p => cases e with
      | fn => exact hf n k bounded p h
      | arg => exact ha n k bounded p h
      | body => cases h
  | lam b ih =>
    cases p with
    | nil => cases h
    | cons e p => cases e with
      | fn => cases h
      | arg => cases h
      | body =>
        have result := ih (n+1) (k+1) (by omega) p (by
          simpa only [subst,subtermAt,binderDepth,liftSubN,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h)
        simpa only [subtermAt,binderDepth,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using result

theorem ArgumentOccurrence.subst_reflect
    (h : ArgumentOccurrence (subst (liftSub σ) b) occurrence) :
    ArgumentOccurrence b occurrence := by
  simpa only [Nat.zero_add] using subst_protected_occurrence_reflect b σ 1 0 (by omega) occurrence
    (by simpa only [ArgumentOccurrence,liftSubN,Nat.zero_add] using h)

/-- A specified occurrence bound by an old function-part redex's own lambda
already existed before the outer beta step. The occurrence path is literal;
no occurrence-origin certificate is an input. -/
theorem BetaAt.function_argument_occurrence_reflect
    (R : BetaAt t p u) (S' : BetaAt t s' v) (S : BetaAt u s w)
    (inside : ∃ q,s'=(p++[.fn])++q)
    (old : (singleContraction R).derivation.Residual ⟨s',S'.redex⟩ ⟨s,S.redex⟩)
    (lookup : subtermAt u s=some (.app (.lam b) a))
    (occurs : ArgumentOccurrence b occurrence) :
    ∃ b' a', subtermAt t s'=some (.app (.lam b') a') ∧ ArgumentOccurrence b' occurrence := by
  obtain ⟨q,source,target⟩ := R.function_residual_coordinates ⟨s',S'.redex⟩ ⟨s,S.redex⟩ inside old
  change s'=(p++[.fn,.body])++q at source
  change s=p++q at target
  obtain ⟨outerBody,outerArg,rootLookup,replaced⟩ := R
  obtain ⟨innerBody,innerArg,innerLookup,_⟩ := S'
  have localLookup : subtermAt outerBody q=some (.app (.lam innerBody) innerArg) := by
    have h := innerLookup
    rw [source,List.append_assoc,subtermAt_append,rootLookup,Option.bind_some] at h
    exact h
  obtain ⟨result,replace,focus⟩ := replaceAt_lookup rootLookup (contract outerBody outerArg)
  rw [replaced] at replace
  have endpoint := Option.some.inj replace
  cases endpoint
  have substituted := subtermAt_subst localLookup (singleSub outerArg)
  have expected : subtermAt u s=some
      (.app (.lam (subst (liftSub (liftSubN (binderDepth q) (singleSub outerArg))) innerBody))
        (subst (liftSubN (binderDepth q) (singleSub outerArg)) innerArg)) := by
    rw [target,subtermAt_append,focus,Option.bind_some]
    exact substituted
  rw [lookup] at expected
  have bodyEq := Term.lam.inj (Term.app.inj (Option.some.inj expected)).1
  refine ⟨innerBody,innerArg,innerLookup,?_⟩
  apply ArgumentOccurrence.subst_reflect (σ := liftSubN (binderDepth q) (singleSub outerArg))
  rw [←bodyEq]
  exact occurs

end Lamping.Lambda
