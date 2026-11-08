import Lamping.Lambda.LabelPaths
import Lamping.Lambda.Families
namespace Lamping.Lambda.Labelled

namespace LTerm
theorem label_mem_of_subterm {t u : LTerm} {p : Path} (h : t.subterm p=some u) : u.label∈t.labels := by
  induction p generalizing t with
  | nil => simp only [subterm,Option.some.injEq] at h; cases h; exact label_mem_labels _
  | cons s p ih =>
    cases t with
    | var _ _ => cases s <;> simp [subterm] at h
    | app beta f a =>
      cases s with
      | fn => exact List.mem_cons_of_mem _ (List.mem_append_left _ (ih h))
      | arg => exact List.mem_cons_of_mem _ (List.mem_append_right _ (ih h))
      | body => simp [subterm] at h
    | lam alpha b =>
      cases s with
      | body => exact List.mem_cons_of_mem _ (ih h)
      | fn => simp [subterm] at h
      | arg => simp [subterm] at h

/-- Distinct node occurrences in an initial term have distinct labels. -/
theorem subterm_label_injective (t : LTerm) (nd : t.labels.Nodup)
    (hp : t.subterm p=some v) (hq : t.subterm q=some w) (hl : v.label=w.label) : p=q := by
  induction t generalizing p q v w with
  | var beta i =>
    cases p with
    | nil => cases q with
      | nil => rfl
      | cons s q => cases s <;> simp [subterm] at hq
    | cons s p => cases s <;> simp [subterm] at hp
  | lam alpha b ih =>
    obtain ⟨hn,nb⟩ := List.nodup_cons.mp nd
    cases p with
    | nil =>
      simp only [subterm,Option.some.injEq] at hp; cases hp; simp only [label] at hl
      cases q with
      | nil => rfl
      | cons s q =>
        cases s with
        | fn => simp [subterm] at hq
        | arg => simp [subterm] at hq
        | body => exact False.elim (hn (Eq.mp (congrArg (fun l => l ∈ b.labels) hl.symm) (label_mem_of_subterm (t := b) (p := q) hq)))
    | cons s p =>
      cases s with
      | fn => simp [subterm] at hp
      | arg => simp [subterm] at hp
      | body =>
        cases q with
        | nil =>
          simp only [subterm,Option.some.injEq] at hq; cases hq; simp only [label] at hl
          exact False.elim (hn (Eq.mp (congrArg (fun l => l ∈ b.labels) hl) (label_mem_of_subterm (t := b) (p := p) hp)))
        | cons r q =>
          cases r with
          | fn => simp [subterm] at hq
          | arg => simp [subterm] at hq
          | body => exact congrArg (Step.body :: ·) (ih nb hp hq hl)
  | app beta f a hf ha =>
    obtain ⟨hn,nt⟩ := List.nodup_cons.mp nd
    obtain ⟨nf,na,disj⟩ := List.nodup_append.mp nt
    cases p with
    | nil =>
      simp only [subterm,Option.some.injEq] at hp; cases hp; simp only [label] at hl
      cases q with
      | nil => rfl
      | cons s q =>
        cases s with
        | body => simp [subterm] at hq
        | fn => exact False.elim (hn (List.mem_append_left _ (Eq.mp (congrArg (fun l => l ∈ f.labels) hl.symm) (label_mem_of_subterm (t := f) (p := q) hq))))
        | arg => exact False.elim (hn (List.mem_append_right _ (Eq.mp (congrArg (fun l => l ∈ a.labels) hl.symm) (label_mem_of_subterm (t := a) (p := q) hq))))
    | cons s p =>
      cases s with
      | body => simp [subterm] at hp
      | fn =>
        cases q with
        | nil =>
          simp only [subterm,Option.some.injEq] at hq; cases hq; simp only [label] at hl
          exact False.elim (hn (List.mem_append_left _ (Eq.mp (congrArg (fun l => l ∈ f.labels) hl) (label_mem_of_subterm (t := f) (p := p) hp))))
        | cons r q =>
          cases r with
          | body => simp [subterm] at hq
          | fn => exact congrArg (Step.fn :: ·) (hf nf hp hq hl)
          | arg => exact False.elim (disj _ (label_mem_of_subterm hp) _ (label_mem_of_subterm hq) hl)
      | arg =>
        cases q with
        | nil =>
          simp only [subterm,Option.some.injEq] at hq; cases hq; simp only [label] at hl
          exact False.elim (hn (List.mem_append_right _ (Eq.mp (congrArg (fun l => l ∈ a.labels) hl) (label_mem_of_subterm (t := a) (p := p) hp))))
        | cons r q =>
          cases r with
          | body => simp [subterm] at hq
          | arg => exact congrArg (Step.arg :: ·) (ha na hp hq hl)
          | fn => exact False.elim (disj _ (label_mem_of_subterm hq) _ (label_mem_of_subterm hp) hl.symm)

/-- Function-lambda occurrence whose label is a given redex degree. -/
theorem degreeAt_lambda {t : LTerm} (h : t.degreeAt p=some alpha) :
    ∃ b, t.subterm (p++[.fn])=some (.lam alpha b) := by
  simp only [degreeAt,Option.bind_eq_some_iff] at h
  obtain ⟨u,hu,hd⟩ := h
  have append_lookup : ∀ (t : LTerm) (p q : Path),
      t.subterm (p++q)=(t.subterm p).bind (fun u => u.subterm q) := by
    intro t p q
    induction p generalizing t with
    | nil => simp [subterm]
    | cons s p ih => cases t <;> cases s <;> simp [subterm,ih]
  rw [append_lookup,hu]
  cases u with
  | var _ _ => simp [degree] at hd
  | lam _ _ => simp [degree] at hd
  | app beta f a =>
    cases f with
    | var _ _ => simp [degree] at hd
    | app _ _ _ => simp [degree] at hd
    | lam l b => simp only [degree,Option.some.injEq] at hd; cases hd; exact ⟨b,rfl⟩

/-- The INIT base case of AG6.2.10 uses pairwise-distinct initial labels. -/
theorem initial_degree_injective (hi : INIT t)
    (hp : t.degreeAt p=some alpha) (hq : t.degreeAt q=some alpha) : p=q := by
  obtain ⟨b,hb⟩ := degreeAt_lambda hp
  obtain ⟨c,hc⟩ := degreeAt_lambda hq
  have eq := subterm_label_injective t hi.2 hb hc rfl
  have lens := congrArg List.length eq
  have l : p.length=q.length := by simpa using lens
  have take := congrArg (List.take p.length) eq
  simpa [List.take_append,List.take_length,l] using take
end LTerm

/-- Explicit degree transport from the original source along an actual schedule. -/
def degreeAlong (t : LTerm) (ps : List Path) (p : Path) : Option Label :=
  (t.replay ps).bind (fun u => u.degreeAt p)

theorem degreeAlong_witness (h : History ps t u) : degreeAlong t ps p=u.degreeAt p := by
  simp [degreeAlong,h.replay]

end Lamping.Lambda.Labelled




