import Lamping.Lambda.OrdinarySplits
namespace Lamping.Lambda

theorem StepProjection.append (first : StepProjection step σ τ middle)
    (second : StepProjection middle σ' τ' last) :
    StepProjection step (σ.append σ') (τ.append τ') last := by
  induction first with
  | nil => exact second
  | cons sq tail ih => exact .cons sq (ih second)

theorem Atomic.append_iff (pre : ParallelHistory t v) (post : ParallelHistory v u) :
    Atomic (pre.append post) ↔ Atomic pre ∧ Atomic post := by
  constructor
  · intro ha
    induction pre with
    | nil => exact ⟨.nil _, ha⟩
    | cons head tail ih =>
      cases ha with
      | cons h hs =>
        obtain ⟨ht, hp⟩ := ih post hs
        exact ⟨.cons h ht, hp⟩
  · rintro ⟨hp, hq⟩
    exact hp.append hq

/-- Cut an ordinary actual projection row at a prescribed bottom boundary.
 Both bottom pieces are retained literally, while the top boundary is recovered
 by ordinary schedule alignment and beta determinism. -/
theorem StepProjection.split_bottom {step : ParallelStep F t u}
    {σ : ParallelHistory t v} (pre : ParallelHistory u mid)
    (post : ParallelHistory mid w) {last : ParallelStep G v w}
    (row : StepProjection step σ (pre.append post) last)
    (ha : Atomic σ) (hb : Atomic pre) (hc : Atomic post) :
    ∃ (x : Term) (K : List Path) (topPre : ParallelHistory t x)
      (topPost : ParallelHistory x v) (vertical : ParallelStep K x mid),
      Atomic topPre ∧ Atomic topPost ∧ σ = topPre.append topPost ∧
      StepProjection step topPre pre vertical ∧
      StepProjection vertical topPost post last := by
  have bound : pre.length ≤ σ.length := by
    have len := row.length
    rw [ParallelHistory.length_append] at len
    omega
  obtain ⟨x, topPre, topPost, hp, hq, he, hlen⟩ := ha.split_at pre.length bound
  rw [he] at row
  obtain ⟨y, K, first, second, vertical, row1, row2, bottom⟩ := row.split_append topPre topPost
  have hatomic : Atomic (first.append second) := by rw [← bottom]; exact hb.append hc
  obtain ⟨hf, hs⟩ := (Atomic.append_iff first second).mp hatomic
  have equalLength : pre.length = first.length := by
    have len := row1.length
    omega
  obtain ⟨endpoint, eqFirst, eqSecond⟩ := hb.prefix_alignment hf hc hs bottom equalLength
  cases endpoint
  cases eq_of_heq eqFirst
  cases eq_of_heq eqSecond
  exact ⟨x, K, topPre, topPost, vertical, hp, hq, he, row1, row2⟩

theorem Atomic.two_contractions {σ : ParallelHistory t u} (ha : Atomic σ)
    (length : σ.length = 2) :
    ∃ (v : Term) (p q : Path) (S : BetaAt t p v) (T : BetaAt v q u),
      σ = .cons (singleContraction S) (.single (singleContraction T)) := by
  cases ha with
  | nil => change 0 = 2 at length; omega
  | @cons t p v u tail S ht =>
    cases ht with
    | nil => change 1 = 2 at length; omega
    | @cons v q w u rest T hr =>
      cases rest with
      | nil => exact ⟨v, p, q, S, T, rfl⟩
      | cons head tail =>
        change 1 + (1 + (1 + tail.length)) = 2 at length
        omega

end Lamping.Lambda
