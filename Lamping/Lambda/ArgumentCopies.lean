import Lamping.Lambda.Extraction
namespace Lamping.Lambda

/-- Iterated binder lifting, used to locate the actual substituted argument
 under an arbitrary number of surviving lambdas. -/
def liftSubN : Nat → (Nat → Term) → Nat → Term
  | 0, σ => σ
  | n+1, σ => liftSub (liftSubN n σ)

 theorem liftSubN_shift (n : Nat) (σ : Nat → Term) :
     liftSubN n (liftSub σ) = liftSubN (n+1) σ := by
   induction n with
   | zero => rfl
   | succ n ih => exact congrArg liftSub ih

 theorem subtermAt_subst (hp : subtermAt t p = some u) (σ : Nat → Term) :
     subtermAt (subst σ t) p = some (subst (liftSubN (binderDepth p) σ) u) := by
   induction p generalizing t σ with
   | nil =>
     simp only [subtermAt, Option.some.injEq] at hp
     subst u
     have hnil (x : Term) : subtermAt x [] = some x := by cases x <;> rfl
     exact hnil _
   | cons s p ih =>
     cases t with
     | var i => cases s <;> simp [subtermAt] at hp
     | app f a =>
       cases s with
       | body => simp [subtermAt] at hp
       | fn => exact ih hp σ
       | arg => exact ih hp σ
     | lam b =>
       cases s with
       | fn => simp [subtermAt] at hp
       | arg => simp [subtermAt] at hp
       | body =>
         have hh := ih hp (liftSub σ)
         simpa only [subst, subtermAt, binderDepth, liftSubN_shift] using hh

 theorem liftSubN_self (n : Nat) (σ : Nat → Term) :
     liftSubN n σ n = rename (fun i => i + n) (σ 0) := by
   induction n with
   | zero => exact (rename_id _).symm
   | succ n ih =>
     simp only [liftSubN, liftSub, ih, rename_comp]
     apply rename_congr
     intro i
     change Nat.succ (i + n) = i + (n + 1)
     omega

/-- The i-th argument instance is an actual subterm of the beta contractum;
 its free indices are shifted by exactly the number of binders over that
 occurrence in the body. -/
 theorem argument_copy (hp : ArgumentOccurrence b p) (a : Term) :
     subtermAt (contract b a) p =
       some (rename (fun i => i + binderDepth p) a) := by
   have hh := subtermAt_subst hp (singleSub a)
   simpa only [contract, subst, liftSubN_self, singleSub] using hh
end Lamping.Lambda


