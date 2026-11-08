import Lamping.Lambda.RootResidualPaths
import Lamping.Lambda.SubstitutionOrigins
namespace Lamping.Lambda

theorem liftSingle_other (n i : Nat) (a : Term) (hne : i≠n) :
    ∃ j, liftSubN n (singleSub a) i = .var j := by
  induction n generalizing i with
  | zero =>
    cases i with
    | zero => exact False.elim (hne rfl)
    | succ i => exact ⟨i,rfl⟩
  | succ n ih =>
    cases i with
    | zero => exact ⟨0,rfl⟩
    | succ i =>
      obtain ⟨j,hj⟩ := ih i (by omega)
      exact ⟨j+1,by simp only [liftSubN,liftSub,hj,rename]⟩

theorem isRedex_rename_iff (ρ : Nat → Nat) (t : Term) : IsRedex (rename ρ t) ↔ IsRedex t := by
  cases t with
  | var => rfl
  | lam => rfl
  | app f a => cases f <;> rfl

theorem redex_rename_reflect (h : ∃ u, subtermAt (rename ρ t) p=some u ∧ IsRedex u) :
    ∃ u, subtermAt t p=some u ∧ IsRedex u := by
  obtain ⟨u,hu,hr⟩ := h
  rw [subtermAt_rename] at hu
  cases he : subtermAt t p with
  | none => simp [he] at hu
  | some v =>
    simp only [he,Option.map_some,Option.some.injEq] at hu
    subst u
    exact ⟨v,rfl,(isRedex_rename_iff _ v).mp hr⟩

private theorem var_no_redex (i : Nat) (p : Path) :
    ¬ ∃ u, subtermAt (.var i) p=some u ∧ IsRedex u := by
  cases p with
  | nil => simp [subtermAt,IsRedex]
  | cons s p => cases s <;> simp [subtermAt]

/-- A redex newly created inside a root beta contractum can only arise at
a body application whose function was the contracted binder's variable,
when the substituted argument is a lambda. Old body/argument cases are
excluded using actual residual transport, not endpoint syntax alone. -/
theorem root_new_redex_source (s : RedexOcc (contract b a))
    (fresh : ¬ ∃ r : RedexOcc (.app (.lam b) a), (rootContraction b a).Residual r s) :
    ∃ body inner, a=.lam body ∧
      subtermAt b s.val=some (.app (.var (binderDepth s.val)) inner) := by
  have origin := subst_redex_source (σ:=singleSub a) (t:=b) (q:=s.val) s.property
  cases origin with
  | old h =>
    let r : RedexOcc (.app (.lam b) a) := ⟨[.fn,.body]++s.val,by simpa [subtermAt] using h⟩
    exact False.elim (fresh ⟨r,root_body_residual r s rfl⟩)
  | @headVariable i inner atBody isLambda =>
    obtain ⟨body,hbody⟩ := isLambda
    have hi : i=binderDepth s.val := by
      by_cases eq : i=binderDepth s.val
      · exact eq
      · obtain ⟨j,hj⟩ := liftSingle_other (binderDepth s.val) i a eq
        rw [hj] at hbody
        cases hbody
    subst i
    rw [liftSubN_self] at hbody
    cases a with
    | var => cases hbody
    | app => cases hbody
    | lam abody => exact ⟨abody,inner,rfl,atBody⟩
  | @inserted site i tail atVariable atCopy isRedex =>
    have hi : i=binderDepth site := by
      by_cases eq : i=binderDepth site
      · exact eq
      · obtain ⟨j,hj⟩ := liftSingle_other (binderDepth site) i a eq
        rw [hj] at isRedex
        exact False.elim (var_no_redex j tail isRedex)
    subst i
    rw [liftSubN_self] at isRedex
    have oldArgument := redex_rename_reflect isRedex
    let r : RedexOcc (.app (.lam b) a) := ⟨[.arg]++tail,by simpa [subtermAt] using oldArgument⟩
    exact False.elim (fresh ⟨r,root_argument_residual site tail atVariable r s rfl atCopy⟩)
end Lamping.Lambda
