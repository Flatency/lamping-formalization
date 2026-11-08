import Lamping.Lambda.ProjectionFamilies
namespace Lamping.Lambda

/-- Split an ordinary history at an actual contraction index, preserving
 the exact path schedule and intermediate term. -/
theorem Atomic.split_at {ρ : ParallelHistory t u} (ha : Atomic ρ) (n : Nat)
    (bound : n ≤ ρ.length) :
    ∃ (v : Term) (pre : ParallelHistory t v) (post : ParallelHistory v u),
      Atomic pre ∧ Atomic post ∧ ρ = pre.append post ∧ pre.length = n := by
  induction ha generalizing n with
  | nil t =>
    have hn : n = 0 := by change n ≤ 0 at bound; omega
    subst n
    exact ⟨t, .nil t, .nil t, .nil t, .nil t, rfl, rfl⟩
  | @cons t p v target σ first tail ih =>
    cases n with
    | zero => exact ⟨_, .nil _, _, .nil _, .cons first tail, rfl, rfl⟩
    | succ n =>
      have hb : n ≤ σ.length := by
        change n + 1 ≤ 1 + σ.length at bound
        omega
      obtain ⟨v, pre, post, hp, hq, he, hlen⟩ := ih n hb
      refine ⟨v, .cons (singleContraction first) pre, post, .cons first hp, hq, ?_, ?_⟩
      · rw [he]; rfl
      · change 1 + pre.length = n + 1
        omega

/-- Equal-length prefixes of two decompositions of the same ordinary run
 are the same actual history, including their intermediate term. -/
theorem Atomic.prefix_alignment
    {a : ParallelHistory t v} {b : ParallelHistory v u}
    {c : ParallelHistory t w} {d : ParallelHistory w u}
    (ha : Atomic a) (hc : Atomic c)
    (hb : Atomic b) (hd : Atomic d)
    (whole : a.append b = c.append d) (length : a.length = c.length) :
    v = w ∧ HEq a c ∧ HEq b d := by
  have paths := congrArg (fun h => h.derivation.paths) whole
  simp only [ParallelHistory.derivation_append, Derivation.append] at paths
  have plen : a.derivation.paths.length = c.derivation.paths.length := by
    rw [ha.paths_length, hc.paths_length, length]
  have prePaths := List.append_inj_left paths plen
  have postPaths := List.append_inj_right paths plen
  have hc' : BetaHistory a.derivation.paths t w := by rw [prePaths]; exact c.derivation.valid
  have endpoint := a.derivation.valid.deterministic hc'
  cases endpoint
  exact ⟨rfl, heq_of_eq (ha.paths_injective hc prePaths), heq_of_eq (hb.paths_injective hd postPaths)⟩

/-- Ordinary run identity can be checked on its full actual path schedule;
 endpoint equality follows from beta determinism rather than being assumed. -/
theorem ExtractionRun.ext_paths (r s : ExtractionRun m)
    (paths : r.history.derivation.paths = s.history.derivation.paths) : r = s := by
  cases r with
  | mk rt rh ra =>
    cases s with
    | mk st sh sa =>
      have hs : BetaHistory rh.derivation.paths m st := by rw [paths]; exact sh.derivation.valid
      have target := rh.derivation.valid.deterministic hs
      cases target
      have histories := ra.paths_injective sa paths
      cases histories
      rfl

/-- Compare two deletion-site prefixes of one ordinary schedule. The later
 prefix extends the earlier by a genuine ordinary history, and the remaining
 suffix is exactly that history followed by the later suffix. -/
theorem Atomic.prefix_comparable
    {a : ParallelHistory t v} {b : ParallelHistory v u}
    {c : ParallelHistory t w} {d : ParallelHistory w u}
    (ha : Atomic a) (hc : Atomic c) (hb : Atomic b) (hd : Atomic d)
    (whole : a.append b = c.append d) (length : a.length ≤ c.length) :
    ∃ bridge : ParallelHistory v w, Atomic bridge ∧
      c = a.append bridge ∧ b = bridge.append d := by
  obtain ⟨x, pre, post, hpre, hpost, hcSplit, hlen⟩ := hc.split_at a.length length
  have aligned : a.append b = pre.append (post.append d) := by
    rw [whole, hcSplit, ParallelHistory.append_assoc]
  obtain ⟨endpoint, preEq, postEq⟩ := ha.prefix_alignment hpre hb (hpost.append hd) aligned hlen.symm
  cases endpoint
  refine ⟨post, hpost, ?_, eq_of_heq postEq⟩
  rw [hcSplit, eq_of_heq preEq]

/-- Cut a real projection row at any actual top-history boundary. Both
 resulting rows retain the original horizontal and vertical schedules. -/
theorem StepProjection.split_append {step : ParallelStep F t u}
    (pre : ParallelHistory t v) (post : ParallelHistory v v')
    {projected : ParallelHistory u w} {last : ParallelStep G v' w}
    (row : StepProjection step (pre.append post) projected last) :
    ∃ (mid : Term) (K : List Path) (first : ParallelHistory u mid)
      (second : ParallelHistory mid w) (vertical : ParallelStep K v mid),
      StepProjection step pre first vertical ∧
      StepProjection vertical post second last ∧ projected = first.append second := by
  induction pre generalizing F u w G with
  | nil => exact ⟨u, F, .nil u, projected, step, .nil step, row, rfl⟩
  | cons head tail ih =>
    cases row with
    | cons sq remaining =>
      obtain ⟨mid, K, first, second, vertical, hfirst, hsecond, he⟩ := ih post remaining
      exact ⟨mid, K, .cons sq.afterFirst first, second, vertical,
        .cons sq hfirst, hsecond, by rw [he]; rfl⟩
end Lamping.Lambda
