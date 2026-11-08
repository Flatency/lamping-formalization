import Lamping.Lambda.Occurrences
namespace Lamping.Lambda

def singleSub (a : Term) : Nat → Term
  | 0 => a
  | n+1 => .var n

def contract (b a : Term) : Term := subst (singleSub a) b

inductive Beta : Term → Term → Prop where
  | root (b a) : Beta (.app (.lam b) a) (contract b a)
  | fn : Beta f f' → Beta (.app f a) (.app f' a)
  | arg : Beta a a' → Beta (.app f a) (.app f a')
  | body : Beta b b' → Beta (.lam b) (.lam b')

inductive Betas : Term → Term → Prop where
  | refl (t) : Betas t t
  | cons : Beta t u → Betas u v → Betas t v

theorem contract_scoped (hb : Scoped (n+1) b) (ha : Scoped n a) :
    Scoped n (contract b a) := by
  apply scoped_subst hb
  intro i hi
  cases i with
  | zero => exact ha
  | succ i => exact Nat.lt_of_succ_lt_succ hi

theorem Beta.scoped (h : Beta t u) (ht : Scoped n t) : Scoped n u := by
  induction h generalizing n with
  | root b a => exact contract_scoped ht.1 ht.2
  | fn h ih => exact ⟨ih ht.1, ht.2⟩
  | arg h ih => exact ⟨ht.1, ih ht.2⟩
  | body h ih => exact ih ht

end Lamping.Lambda
