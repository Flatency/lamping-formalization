import Lamping.Lambda.Marked
namespace Lamping.Lambda.Marked

def extend (x : Nat) (e : Nat → Nat) : Nat → Nat
  | 0 => x
  | i+1 => e i

/-- All environments are allowed; extra summands retain erased arguments and
    bodies, so even erasing/duplicating contractions strictly decrease. -/
def weight (e : Nat → Nat) : Marked → Nat
  | .var i => e i
  | .lam b => weight (extend 1 e) b + 1
  | .app _ f a => weight e f + weight e a + 1
  | .red _ b a => weight (extend (weight e a) e) b +
      weight (extend 1 e) b + weight e a + 1

theorem weight_mono (t : Marked) {e f : Nat → Nat} (h : ∀ i, e i ≤ f i) :
    weight e t ≤ weight f t := by
  induction t generalizing e f with
  | var i => exact h i
  | lam b hb =>
    have q := hb (e := extend 1 e) (f := extend 1 f) (by intro i; cases i <;> simp [extend, h])
    simp only [weight]; omega
  | app l b a hb ha =>
    have q := hb h; have r := ha h
    simp only [weight]; omega
  | red l b a hb ha =>
    have r := ha h
    have q := hb (e := extend (weight e a) e) (f := extend (weight f a) f)
      (by intro i; cases i <;> simp [extend, h, r])
    have s := hb (e := extend 1 e) (f := extend 1 f) (by intro i; cases i <;> simp [extend, h])
    simp only [weight]; omega

theorem weight_rename (ρ) (t : Marked) (e) :
    weight e (rename ρ t) = weight (fun i => e (ρ i)) t := by
  induction t generalizing ρ e with
  | var i => rfl
  | app l f a hf ha => simp [rename, weight, hf, ha]
  | lam b hb =>
    simp only [rename, weight, hb]
    congr 1; congr 1; funext i; cases i <;> rfl
  | red l b a hb ha =>
    simp only [rename, weight, hb, ha]
    have q (x : Nat) : (fun i => extend x e (liftRen ρ i)) = extend x (fun i => e (ρ i)) := by
      funext i; cases i <;> rfl
    simp only [q]

theorem weight_subst (σ) (t : Marked) (e) :
    weight e (subst σ t) = weight (fun i => weight e (σ i)) t := by
  induction t generalizing σ e with
  | var i => rfl
  | app l f a hf ha => simp [subst, weight, hf, ha]
  | lam b hb =>
    simp only [subst, weight, hb]
    congr 1; congr 1; funext i
    cases i <;> simp [liftSub, weight, weight_rename, extend]
  | red l b a hb ha =>
    simp only [subst, weight, hb, ha]
    have q (x : Nat) : (fun i => weight (extend x e) (liftSub σ i)) = extend x (fun i => weight e (σ i)) := by
      funext i; cases i <;> simp [liftSub, weight, weight_rename, extend]
    simp only [q]

theorem weight_contract (b a : Marked) (e) :
    weight e (contract b a) = weight (extend (weight e a) e) b := by
  simp only [contract, weight_subst]
  congr 1; funext i; cases i <;> rfl

theorem Step.weight_lt (h : Step t u) (e : Nat → Nat) : weight e u < weight e t := by
  induction h generalizing e with
  | root l b a => simp only [weight, weight_contract]; omega
  | lam h ih => have q := ih (extend 1 e); simp only [weight]; omega
  | appL h ih => have q := ih e; simp only [weight]; omega
  | appR h ih => have q := ih e; simp only [weight]; omega
  | @redL b b' l a h ih =>
    have q := ih (extend (weight e a) e)
    have r := ih (extend 1 e)
    simp only [weight]; omega
  | @redR a a' l b h ih =>
    have q := ih e
    have r := weight_mono b (e := extend (weight e a') e) (f := extend (weight e a) e)
      (by intro i; cases i <;> simp [extend]; omega)
    simp only [weight]; omega

/-- Strong finite developments: every active contraction descends in Nat. -/
theorem step_wellFounded : WellFounded (fun u t : Marked => Step t u) :=
  Subrelation.wf (fun h => Step.weight_lt h (fun _ => 1))
    (InvImage.wf (fun t : Marked => weight (fun _ => 1) t) Nat.lt_wfRel.wf)

theorem no_infinite_development : ¬ ∃ f : Nat → Marked, ∀ n, Step (f n) (f (n+1)) := by
  rintro ⟨f, h⟩
  have q (n) : weight (fun _ => 1) (f n) + n ≤ weight (fun _ => 1) (f 0) := by
    induction n with
    | zero => simp
    | succ n ih => have r := Step.weight_lt (h n) (fun _ => 1); omega
  have r := q (weight (fun _ => 1) (f 0) + 1)
  omega

end Lamping.Lambda.Marked

