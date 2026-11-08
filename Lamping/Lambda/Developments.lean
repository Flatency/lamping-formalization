import Lamping.Lambda.DevelopmentMeasure
namespace Lamping.Lambda.Marked

theorem rename_contract (ρ) (b a : Marked) :
    rename ρ (contract b a) = contract (rename (liftRen ρ) b) (rename ρ a) := by
  simp only [contract, rename_subst, subst_rename]
  congr 1; funext i; cases i <;> rfl

theorem subst_contract (σ) (b a : Marked) :
    subst σ (contract b a) = contract (subst (liftSub σ) b) (subst σ a) := by
  simp only [contract, subst_comp]
  congr 1; funext i
  cases i with
  | zero => rfl
  | succ i =>
    simp only [single, liftSub, subst, subst_rename]
    exact (subst_id (σ i)).symm

/-- Complete development preserves the whole passive-tag tree. -/
def dev : Marked → Marked
  | .var i => .var i
  | .lam b => .lam (dev b)
  | .app l f a => .app l (dev f) (dev a)
  | .red _ b a => contract (dev b) (dev a)

theorem dev_rename (ρ) (t : Marked) : dev (rename ρ t) = rename ρ (dev t) := by
  induction t generalizing ρ with
  | var i => rfl
  | lam b hb => simp [rename, dev, hb]
  | app l f a hf ha => simp [rename, dev, hf, ha]
  | red l b a hb ha => simp [rename, dev, hb, ha, rename_contract]

theorem dev_subst (σ) (t : Marked) : dev (subst σ t) = subst (fun i => dev (σ i)) (dev t) := by
  induction t generalizing σ with
  | var i => rfl
  | app l f a hf ha => simp [subst, dev, hf, ha]
  | lam b hb =>
    simp only [subst, dev, hb]
    congr 1; congr 1; funext i
    cases i <;> simp [liftSub, dev, dev_rename]
  | red l b a hb ha =>
    simp only [subst, dev, hb, ha, subst_contract]
    congr 1; congr 1; funext i
    cases i <;> simp [liftSub, dev, dev_rename]

theorem dev_contract (b a : Marked) : dev (contract b a) = contract (dev b) (dev a) := by
  simp only [contract, dev_subst]
  congr 1; funext i; cases i <;> rfl

theorem Step.dev_eq (h : Step t u) : dev t = dev u := by
  induction h with
  | root l b a => exact (dev_contract b a).symm
  | lam h ih => simp [dev, ih]
  | appL h ih => simp [dev, ih]
  | appR h ih => simp [dev, ih]
  | redL h ih => simp [dev, ih]
  | redR h ih => simp [dev, ih]

/-- Completeness says only that no selected redex remains. -/
def Normal : Marked → Prop
  | .var _ => True
  | .lam b => Normal b
  | .app _ f a => Normal f ∧ Normal a
  | .red _ _ _ => False

theorem normal_rename (h : Normal t) (ρ) : Normal (rename ρ t) := by
  induction t generalizing ρ with
  | var i => trivial
  | lam b hb => exact hb h _
  | app l f a hf ha => exact ⟨hf h.1 _, ha h.2 _⟩
  | red l b a hb ha => exact False.elim h

theorem normal_subst (h : Normal t) (hσ : ∀ i, Normal (σ i)) : Normal (subst σ t) := by
  induction t generalizing σ with
  | var i => exact hσ i
  | app l f a hf ha => exact ⟨hf h.1 hσ, ha h.2 hσ⟩
  | lam b hb =>
    apply hb h
    intro i; cases i with
    | zero => trivial
    | succ i => exact normal_rename (hσ i) _
  | red l b a hb ha => exact False.elim h

theorem normal_dev (t : Marked) : Normal (dev t) := by
  induction t with
  | var i => trivial
  | lam b hb => exact hb
  | app l f a hf ha => exact ⟨hf, ha⟩
  | red l b a hb ha =>
    apply normal_subst hb
    intro i; cases i with
    | zero => exact ha
    | succ i => trivial

theorem dev_of_normal (h : Normal t) : dev t = t := by
  induction t with
  | var i => rfl
  | lam b hb => simp [dev, hb h]
  | app l f a hf ha => simp [dev, hf h.1, ha h.2]
  | red l b a hb ha => exact False.elim h

theorem normal_iff_no_step (t : Marked) : Normal t ↔ ¬ ∃ u, Step t u := by
  constructor
  · intro h ⟨u, hs⟩
    induction hs with
    | root l b a => exact h
    | lam hs ih => exact ih h
    | appL hs ih => exact ih h.1
    | appR hs ih => exact ih h.2
    | redL hs ih => exact h
    | redR hs ih => exact h
  · intro h
    induction t with
    | var i => trivial
    | lam b hb =>
      apply hb; rintro ⟨u, hs⟩; exact h ⟨.lam u, .lam hs⟩
    | app l f a hf ha =>
      constructor
      · apply hf; rintro ⟨u, hs⟩; exact h ⟨.app l u a, .appL hs⟩
      · apply ha; rintro ⟨u, hs⟩; exact h ⟨.app l f u, .appR hs⟩
    | red l b a hb ha => exact h ⟨contract b a, .root l b a⟩

inductive Steps : Marked → Marked → Prop where
  | refl (t) : Steps t t
  | cons : Step t u → Steps u v → Steps t v

theorem Steps.trans (h : Steps t u) (k : Steps u v) : Steps t v := by
  induction h with
  | refl => exact k
  | cons h hs ih => exact .cons h (ih k)

theorem Steps.map (h : Steps t u) (f : Marked → Marked)
    (hf : ∀ {a b}, Step a b → Step (f a) (f b)) : Steps (f t) (f u) := by
  induction h with
  | refl => exact .refl _
  | cons h hs ih => exact .cons (hf h) ih

theorem Steps.dev_eq (h : Steps t u) : dev t = dev u := by
  induction h with
  | refl => rfl
  | cons h hs ih => exact h.dev_eq.trans ih

theorem Steps.erase (h : Steps t u) : Betas t.erase u.erase := by
  induction h with
  | refl => exact .refl _
  | cons h hs ih => exact .cons h.erase ih

theorem steps_to_dev (t : Marked) : Steps t (dev t) := by
  induction t with
  | var i => exact .refl _
  | lam b hb => exact hb.map Marked.lam (fun h => .lam h)
  | app l f a hf ha =>
    exact (hf.map (fun u => .app l u a) (fun h => .appL h)).trans
      (ha.map (fun u => .app l (dev f) u) (fun h => .appR h))
  | red l b a hb ha =>
    exact (hb.map (fun u => .red l u a) (fun h => .redL h)).trans
      ((ha.map (fun u => .red l (dev b) u) (fun h => .redR h)).trans
        (.cons (.root l (dev b) (dev a)) (.refl _)))

/-- A finite development, complete exactly when its endpoint has no active red. -/
def Complete (t u : Marked) : Prop := Steps t u ∧ Normal u

theorem complete_exists (t : Marked) : ∃ u, Complete t u :=
  ⟨dev t, steps_to_dev t, normal_dev t⟩

theorem complete_endpoint (h : Complete t u) : u = dev t :=
  (dev_of_normal h.2).symm.trans h.1.dev_eq.symm

/-- Includes passive tags, hence also the residuals of redexes outside F. -/
theorem complete_unique (h : Complete t u) (k : Complete t v) : u = v :=
  (complete_endpoint h).trans (complete_endpoint k).symm

end Lamping.Lambda.Marked

