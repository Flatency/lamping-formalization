import Lamping.Lambda.Standardization
namespace Lamping.Lambda
namespace LeftOf
theorem trans (h : LeftOf p q) (k : LeftOf q r) : LeftOf p r := by
  induction h generalizing r with
  | outer s p =>
    cases k with
    | child s k => exact .outer _ _
    | branch p q => exact .outer _ _
  | child s h ih =>
    cases k with
    | child _ k => exact .child _ (ih k)
    | branch p q => exact .branch _ _
  | branch p q =>
    cases k with
    | child _ k => exact .branch _ _

theorem asymm (h : LeftOf p q) : ¬ LeftOf q p := by
  intro k
  exact irrefl p (h.trans k)
end LeftOf

private theorem compare_cons (s : Step)
    (h : p=q ∨ LeftOf p q ∨ LeftOf q p) :
    s::p=s::q ∨ LeftOf (s::p) (s::q) ∨ LeftOf (s::q) (s::p) := by
  rcases h with h | h | h
  · exact Or.inl (congrArg (s::·) h)
  · exact Or.inr (Or.inl (.child s h))
  · exact Or.inr (Or.inr (.child s h))

/-- Comparability holds for occurrences of the same term. Arbitrary path
words are deliberately not asserted comparable (fn and body can conflict). -/
theorem compare_positions (t : Term) (p q : Path)
    (hp : (subtermAt t p).isSome) (hq : (subtermAt t q).isSome) :
    p=q ∨ LeftOf p q ∨ LeftOf q p := by
  induction t generalizing p q with
  | var i =>
    cases p with
    | nil =>
      cases q with
      | nil => exact Or.inl rfl
      | cons s q => cases s <;> simp [subtermAt] at hq
    | cons s p => cases s <;> simp [subtermAt] at hp
  | app f a ihf iha =>
    cases p with
    | nil =>
      cases q with
      | nil => exact Or.inl rfl
      | cons s q => exact Or.inr (Or.inl (.outer s q))
    | cons s p =>
      cases q with
      | nil => exact Or.inr (Or.inr (.outer s p))
      | cons r q =>
        cases s <;> cases r
        · exact compare_cons .fn (ihf p q hp hq)
        · exact Or.inr (Or.inl (.branch p q))
        · simp [subtermAt] at hq
        · exact Or.inr (Or.inr (.branch q p))
        · exact compare_cons .arg (iha p q hp hq)
        · simp [subtermAt] at hq
        all_goals simp [subtermAt] at hp
  | lam b ih =>
    cases p with
    | nil =>
      cases q with
      | nil => exact Or.inl rfl
      | cons s q => exact Or.inr (Or.inl (.outer s q))
    | cons s p =>
      cases q with
      | nil => exact Or.inr (Or.inr (.outer s p))
      | cons r q =>
        cases s <;> cases r
        all_goals solve | exact compare_cons .body (ih p q hp hq) | simp [subtermAt] at hp | simp [subtermAt] at hq

theorem Position.compare (p q : Position t) :
    p=q ∨ LeftOf p.val q.val ∨ LeftOf q.val p.val := by
  rcases compare_positions t p.val q.val p.property q.property with h | h
  · exact Or.inl (Subtype.eq h)
  · exact Or.inr h

theorem RedexOcc.compare (p q : RedexOcc t) :
    p=q ∨ LeftOf p.val q.val ∨ LeftOf q.val p.val := by
  obtain ⟨u, hu, _⟩ := p.property
  obtain ⟨v, hv, _⟩ := q.property
  have hp : (subtermAt t p.val).isSome := by rw [hu]; rfl
  have hq : (subtermAt t q.val).isSome := by rw [hv]; rfl
  rcases compare_positions t p.val q.val hp hq with h | h
  · exact Or.inl (Subtype.eq h)
  · exact Or.inr h

/-- A nonempty finite selection of actual redexes possesses an LO member.
The selection need not be sorted or free of repeated path names. -/
theorem leftmost_selected_exists (F : List Path)
    (valid : ∀ p ∈ F, ∃ u, subtermAt t p=some u ∧ IsRedex u)
    (nonempty : F ≠ []) : ∃ r : RedexOcc t, LeftmostSelected F r := by
  induction F with
  | nil => exact False.elim (nonempty rfl)
  | cons p ps ih =>
    have hp := valid p (List.mem_cons_self ..)
    let r : RedexOcc t := ⟨p,hp⟩
    by_cases tail : ps=[]
    · subst ps
      exact ⟨r,leftmost_singleton r⟩
    · obtain ⟨s,hs,hmin⟩ := ih (fun q hq => valid q (List.mem_cons_of_mem _ hq)) tail
      classical
      by_cases first : LeftOf p s.val
      · refine ⟨r,List.mem_cons_self ..,?_⟩
        intro q hq hleft
        rcases List.mem_cons.mp hq with eq | hq
        · exact LeftOf.irrefl p (by simpa only [show r.val=p from rfl,eq] using hleft)
        · exact hmin q hq (hleft.trans first)
      · refine ⟨s,List.mem_cons_of_mem _ hs,?_⟩
        intro q hq hleft
        rcases List.mem_cons.mp hq with eq | hq
        · exact first (eq ▸ hleft)
        · exact hmin q hq hleft
end Lamping.Lambda


