import Lamping.Lambda.ContextualBeta
import Lamping.Lambda.ArgumentCopies
import Lamping.Lambda.AtomicHistories
namespace Lamping.Lambda

theorem subst_contract (σ : Nat → Term) (b a : Term) :
    subst σ (contract b a)=contract (subst (liftSub σ) b) (subst σ a) := by
  simp only [contract,subst_comp]
  congr 1
  funext i
  cases i with
  | zero => rfl
  | succ i =>
    simp only [singleSub,liftSub,subst,subst_rename]
    exact (subst_id (σ i)).symm

/-- Substitution transports an already successful replacement. No claim is
 made for old invalid paths which substitution may turn into new syntax. -/
theorem replaceAt_subst (h : replaceAt t p b=some u) (σ : Nat → Term) :
    replaceAt (subst σ t) p (subst (liftSubN (binderDepth p) σ) b)=some (subst σ u) := by
  induction p generalizing t u σ with
  | nil =>
    simp only [replaceAt,Option.some.injEq] at h
    cases h
    simp only [binderDepth,liftSubN]
    cases subst σ t <;> rfl
  | cons e p ih =>
    cases t with
    | var i => cases e <;> simp [replaceAt] at h
    | lam body =>
      cases e with
      | fn => simp [replaceAt] at h
      | arg => simp [replaceAt] at h
      | body =>
        cases hp : replaceAt body p b with
        | none => simp [replaceAt,hp] at h
        | some target =>
          simp only [replaceAt,hp,Option.map_some,Option.some.injEq] at h
          cases h
          have moved := ih hp (liftSub σ)
          simpa only [subst,replaceAt,binderDepth,liftSubN_shift,moved,Option.map_some] using
            congrArg (Option.map Term.lam) moved
    | app f a =>
      cases e with
      | body => simp [replaceAt] at h
      | fn =>
        cases hp : replaceAt f p b with
        | none => simp [replaceAt,hp] at h
        | some target =>
          simp only [replaceAt,hp,Option.map_some,Option.some.injEq] at h
          cases h
          have moved := ih hp σ
          simp only [subst,replaceAt,binderDepth,moved,Option.map_some]
      | arg =>
        cases hp : replaceAt a p b with
        | none => simp [replaceAt,hp] at h
        | some target =>
          simp only [replaceAt,hp,Option.map_some,Option.some.injEq] at h
          cases h
          have moved := ih hp σ
          simp only [subst,replaceAt,binderDepth,moved,Option.map_some]

theorem BetaAt.subst (h : BetaAt t p u) (σ : Nat → Term) :
    BetaAt (Lambda.subst σ t) p (Lambda.subst σ u) := by
  obtain ⟨b,a,lookup,replaced⟩ := h
  refine ⟨Lambda.subst (liftSub (liftSubN (binderDepth p) σ)) b,
    Lambda.subst (liftSubN (binderDepth p) σ) a,subtermAt_subst lookup σ,?_⟩
  rw [←subst_contract]
  exact replaceAt_subst replaced σ

theorem BetaHistory.subst (h : BetaHistory paths t u) (σ : Nat → Term) :
    BetaHistory paths (Lambda.subst σ t) (Lambda.subst σ u) := by
  induction h with
  | nil => exact .nil _
  | cons head tail ih => exact .cons (head.subst σ) ih

end Lamping.Lambda
