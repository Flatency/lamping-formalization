import Lamping.Lambda.ResidualInit
namespace Lamping.Lambda.Marked

/-- Active constructors are exactly selected old names; passive constructors
carry no selected names. Shape validity is the independent predicate Valid. -/
def Selected (F : List Path) : Marked → Prop
  | .var _ => True
  | .lam b => Selected F b
  | .app l f a => Selected F f ∧ Selected F a ∧ ∀ r, r ∈ l → r ∉ F
  | .red l b a => Selected F b ∧ Selected F a ∧ ∃ r, r ∈ l ∧ r ∈ F

theorem Selected.rename (ht : Selected F t) (ρ : Nat → Nat) : Selected F (rename ρ t) := by
  induction t generalizing ρ with
  | var i => trivial
  | lam b hb => exact hb ht _
  | app l f a hf ha => exact ⟨hf ht.1 _,ha ht.2.1 _,ht.2.2⟩
  | red l b a hb ha => exact ⟨hb ht.1 _,ha ht.2.1 _,ht.2.2⟩

theorem Selected.subst (ht : Selected F t) (hσ : ∀ i, Selected F (σ i)) :
    Selected F (subst σ t) := by
  induction t generalizing σ with
  | var i => exact hσ i
  | lam b hb =>
    apply hb ht
    intro i; cases i with
    | zero => trivial
    | succ i => exact (hσ i).rename Nat.succ
  | app l f a hf ha => exact ⟨hf ht.1 hσ,ha ht.2.1 hσ,ht.2.2⟩
  | red l b a hb ha =>
    refine ⟨hb ht.1 ?_,ha ht.2.1 hσ,ht.2.2⟩
    intro i; cases i with
    | zero => trivial
    | succ i => exact (hσ i).rename Nat.succ

theorem Selected.contract (hb : Selected F b) (ha : Selected F a) : Selected F (contract b a) := by
  apply hb.subst
  intro i; cases i with
  | zero => exact ha
  | succ i => trivial

theorem ReductionAt.selected (h : ReductionAt p t u) (ht : Selected F t) : Selected F u := by
  induction h with
  | appRoot l b a => exact Selected.contract (b := b) (a := a) ht.1 ht.2.1
  | redRoot l b a => exact ht.1.contract ht.2.1
  | lam h ih => exact ih ht
  | appL h ih => exact ⟨ih ht.1,ht.2.1,ht.2.2⟩
  | appR h ih => exact ⟨ht.1,ih ht.2.1,ht.2.2⟩
  | redL h ih => exact ⟨ih ht.1,ht.2.1,ht.2.2⟩
  | redR h ih => exact ⟨ht.1,ih ht.2.1,ht.2.2⟩

theorem StepAt.selected (h : StepAt p t u) (ht : Selected F t) : Selected F u := h.reductionAt.selected ht

theorem History.selected (h : History ps t u) (ht : Selected F t) : Selected F u := by
  induction h with
  | nil => exact ht
  | cons h hs ih => exact ih (h.selected ht)

theorem selected_markAt (F : List Path) (t : Term) (p : Path) : Selected F (markAt F t p) := by
  induction t generalizing p with
  | var i => trivial
  | lam b hb => exact hb _
  | app f a hf ha =>
    cases f with
    | var i => exact ⟨trivial,ha _,by simp⟩
    | app f b => exact ⟨hf _,ha _,by simp⟩
    | lam b =>
      have hb : Selected F (markAt F b ((p ++ [.fn]) ++ [.body])) := by
        have hh := hf (p ++ [Lambda.Step.fn])
        simpa only [markAt,Selected] using hh
      simp only [markAt]
      split
      · rename_i hp; exact ⟨hb,ha _,p,by simp,hp⟩
      · rename_i hp; exact ⟨hb,ha _,by simpa using hp⟩

theorem selected_mark (F : List Path) (t : Term) : Selected F (mark F t) := selected_markAt F t []

theorem mem_root_tags (r : Path) (l : List Path) (p : Path) :
    p ∈ (if r ∈ l then [[]] else []) ↔ p = [] ∧ r ∈ l := by
  by_cases h : r ∈ l <;> simp [h]

theorem active_iff_selected_trace (ht : Selected F t) (p : Path) :
    p ∈ activePositions t ↔ ∃ r, r ∈ F ∧ p ∈ tracePositions r t := by
  induction t generalizing p with
  | var i => simp [activePositions,tracePositions]
  | lam b hb =>
    cases p with
    | nil => simp [activePositions,tracePositions]
    | cons s p =>
      cases s with
      | fn => simp [activePositions,tracePositions]
      | arg => simp [activePositions,tracePositions]
      | body => simpa [activePositions,tracePositions] using hb ht p
  | app l f a hf ha =>
    cases p with
    | nil =>
      simp only [activePositions,tracePositions,List.mem_append,List.mem_map,mem_root_tags]
      simp only [List.cons_ne_nil, and_false,exists_false,or_false,true_and]
      constructor
      · intro h; exact False.elim h
      · rintro ⟨r,hF,hl⟩; exact False.elim (ht.2.2 r hl hF)
    | cons s p =>
      cases s with
      | fn => simpa [activePositions,tracePositions,mem_root_tags] using hf ht.1 p
      | arg => simpa [activePositions,tracePositions,mem_root_tags] using ha ht.2.1 p
      | body => simp [activePositions,tracePositions]
  | red l b a hb ha =>
    cases p with
    | nil => simpa [activePositions,tracePositions,mem_root_tags,and_comm] using ht.2.2
    | cons s p =>
      cases s with
      | body => simp [activePositions,tracePositions]
      | arg => simpa [activePositions,tracePositions,mem_root_tags] using ha ht.2.1 p
      | fn =>
        cases p with
        | nil => simp [activePositions,tracePositions]
        | cons s p =>
          cases s with
          | fn => simp [activePositions,tracePositions]
          | arg => simp [activePositions,tracePositions]
          | body => simpa [activePositions,tracePositions,mem_root_tags] using hb ht.1 p

end Lamping.Lambda.Marked
