import Lamping.Lambda.OccurrenceOrder
namespace Lamping.Lambda

/-- Zero-based preorder index. Invalid path words receive an arbitrary zero;
every ordering theorem below explicitly requires genuine occurrences. -/
def occurrenceRank : Term → Path → Nat
  | _, [] => 0
  | .app f _, .fn::p => 1 + occurrenceRank f p
  | .app f a, .arg::p => 1 + (positions f).length + occurrenceRank a p
  | .lam b, .body::p => 1 + occurrenceRank b p
  | _, _ => 0

theorem occurrenceRank_bound (t : Term) (p : Path)
    (valid : (subtermAt t p).isSome) : occurrenceRank t p < (positions t).length := by
  induction t generalizing p with
  | var i =>
    cases p with
    | nil => simp [occurrenceRank,positions]
    | cons s p => cases s <;> simp [subtermAt] at valid
  | app f a hf ha =>
    cases p with
    | nil => simp [occurrenceRank,positions]
    | cons s p =>
      cases s with
      | fn =>
        have h := hf p valid
        simp only [occurrenceRank,positions,List.length_cons,List.length_append,List.length_map]
        omega
      | arg =>
        have h := ha p valid
        simp only [occurrenceRank,positions,List.length_cons,List.length_append,List.length_map]
        omega
      | body => simp [subtermAt] at valid
  | lam b hb =>
    cases p with
    | nil => simp [occurrenceRank,positions]
    | cons s p =>
      cases s with
      | fn => simp [subtermAt] at valid
      | arg => simp [subtermAt] at valid
      | body =>
        have h := hb p valid
        simp only [occurrenceRank,positions,List.length_cons,List.length_map]
        omega

theorem LeftOf.rank_lt (h : LeftOf p q)
    (hp : (subtermAt t p).isSome) (hq : (subtermAt t q).isSome) :
    occurrenceRank t p < occurrenceRank t q := by
  induction h generalizing t with
  | outer s p =>
    cases t <;> cases s <;> simp only [subtermAt] at hq
    all_goals first | contradiction | simp [occurrenceRank]; omega
  | child s h ih =>
    cases t <;> cases s <;> simp only [subtermAt] at hp hq
    all_goals first | contradiction | (simp only [occurrenceRank]; have := ih hp hq; omega)
  | branch p q =>
    cases t with
    | var i => simp [subtermAt] at hp
    | lam b => simp [subtermAt] at hp
    | app f a =>
      have h := occurrenceRank_bound f p hp
      simp only [occurrenceRank]
      omega

theorem position_left_wellFounded (t : Term) :
    WellFounded (fun p q : Position t => LeftOf p.val q.val) := by
  exact Subrelation.wf (fun {p q} h => h.rank_lt p.property q.property)
    (InvImage.wf (fun p : Position t => occurrenceRank t p.val) Nat.lt_wfRel.wf)

theorem redex_left_wellFounded (t : Term) :
    WellFounded (fun p q : RedexOcc t => LeftOf p.val q.val) := by
  apply Subrelation.wf (r := InvImage (· < ·) (fun p : RedexOcc t => occurrenceRank t p.val))
    (h₂ := InvImage.wf _ Nat.lt_wfRel.wf)
  intro p q h
  obtain ⟨u,hu,_⟩ := p.property
  obtain ⟨v,hv,_⟩ := q.property
  exact h.rank_lt (by rw [hu]; rfl) (by rw [hv]; rfl)
end Lamping.Lambda
