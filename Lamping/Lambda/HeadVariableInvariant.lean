import Lamping.Lambda.ResidualOrigins
namespace Lamping.Lambda.Marked

/-- Every application carrying the chosen identity has a fixed outer free
variable as its function. Under binders that variable's index is lifted.
Tags may annotate nonredex applications: Valid is deliberately not assumed. -/
def HeadVariable (r : Path) (k : Nat) : Marked → Prop
  | .var _ => True
  | .lam b => HeadVariable r (k+1) b
  | .app l f a => HeadVariable r k f ∧ HeadVariable r k a ∧ (r ∈ l → f=.var k)
  | .red l b a => HeadVariable r (k+1) b ∧ HeadVariable r k a ∧ r ∉ l

theorem HeadVariable.rename (h : HeadVariable r k t) (ρ : Nat → Nat) :
    HeadVariable r (ρ k) (rename ρ t) := by
  induction t generalizing k ρ with
  | var => trivial
  | lam b ih => simpa only [rename,HeadVariable,liftRen] using ih h (liftRen ρ)
  | app l f a hf ha =>
    refine ⟨hf h.1 _,ha h.2.1 _,?_⟩
    intro tag
    rw [h.2.2 tag]
    rfl
  | red l b a hb ha =>
    refine ⟨?_,ha h.2.1 _,h.2.2⟩
    simpa only [liftRen] using hb h.1 (liftRen ρ)

theorem HeadVariable.subst (h : HeadVariable r k t)
    (hσ : ∀ i, HeadVariable r j (σ i)) (hk : σ k=.var j) :
    HeadVariable r j (subst σ t) := by
  induction t generalizing k j σ with
  | var i => exact hσ i
  | lam b ih =>
    refine ih h (σ:=liftSub σ) ?_ ?_
    · intro i
      cases i with
      | zero => trivial
      | succ i => exact (hσ i).rename Nat.succ
    · simp only [liftSub,hk,Marked.rename]
  | app l f a hf ha =>
    refine ⟨hf h.1 hσ hk,ha h.2.1 hσ hk,?_⟩
    intro tag
    rw [h.2.2 tag]
    exact hk
  | red l b a hb ha =>
    refine ⟨hb h.1 (σ:=liftSub σ) ?_ ?_,ha h.2.1 hσ hk,h.2.2⟩
    · intro i
      cases i with
      | zero => trivial
      | succ i => exact (hσ i).rename Nat.succ
    · simp only [liftSub,hk,Marked.rename]

theorem HeadVariable.contract (hb : HeadVariable r (k+1) b) (ha : HeadVariable r k a) :
    HeadVariable r k (contract b a) := by
  apply hb.subst (σ:=single a) (j:=k)
  · intro i
    cases i with
    | zero => exact ha
    | succ i => trivial
  · rfl

private theorem reduction_not_variable (h : ReductionAt p t u) : t≠.var i := by
  cases h <;> intro eq <;> cases eq

theorem ReductionAt.headVariable (h : ReductionAt p t u) (ht : HeadVariable r k t) :
    HeadVariable r k u := by
  induction h generalizing k with
  | appRoot l b a => exact HeadVariable.contract (b:=b) ht.1 ht.2.1
  | redRoot l b a => exact HeadVariable.contract (b:=b) ht.1 ht.2.1
  | lam h ih => exact ih ht
  | appL h ih =>
    refine ⟨ih ht.1,ht.2.1,?_⟩
    intro tag
    exact False.elim (reduction_not_variable h (ht.2.2 tag))
  | appR h ih => exact ⟨ht.1,ih ht.2.1,ht.2.2⟩
  | redL h ih => exact ⟨ih ht.1,ht.2.1,ht.2.2⟩
  | redR h ih => exact ⟨ht.1,ih ht.2.1,ht.2.2⟩

theorem History.headVariable (h : History ps t u) (ht : HeadVariable r k t) : HeadVariable r k u := by
  induction h with
  | nil => exact ht
  | cons h hs ih => exact ih (h.headVariable ht)

theorem HeadVariable.tags_not_redex (h : HeadVariable r k t) (tag : r ∈ tagsAt t q)
    (redex : ∃ u, subtermAt t.erase q=some u ∧ IsRedex u) : False := by
  induction t generalizing k q with
  | var i => cases q <;> simp [tagsAt] at tag
  | lam b ih =>
    cases q with
    | nil => simp [tagsAt] at tag
    | cons s q =>
      cases s with
      | fn => simp [tagsAt] at tag
      | arg => simp [tagsAt] at tag
      | body => exact ih h tag redex
  | app l f a hf ha =>
    cases q with
    | nil =>
      have eq := h.2.2 tag
      simp [erase,subtermAt,eq,IsRedex] at redex
    | cons s q =>
      cases s with
      | fn => exact hf h.1 tag redex
      | arg => exact ha h.2.1 tag redex
      | body => simp [tagsAt] at tag
  | red l b a hb ha =>
    cases q with
    | nil => exact h.2.2 tag
    | cons s q =>
      cases s with
      | arg => exact ha h.2.1 tag redex
      | body => simp [tagsAt] at tag
      | fn =>
        cases q with
        | nil => simp [tagsAt] at tag
        | cons s q =>
          cases s with
          | fn => simp [tagsAt] at tag
          | arg => simp [tagsAt] at tag
          | body => exact hb h.1 tag redex

/-- Identity tracking and ordinary beta agree: an application whose function
is this outer free variable can never become a redex during the history. -/
theorem History.headVariable_no_redex (h : History ps t u) (ht : HeadVariable r k t)
    (tag : q ∈ tracePositions r u) :
    ¬ ∃ v, subtermAt u.erase q=some v ∧ IsRedex v := by
  exact (h.headVariable ht).tags_not_redex ((mem_tagsAt u r q).mpr tag)
end Lamping.Lambda.Marked

