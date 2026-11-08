import Lamping.Lambda.Extraction
namespace Lamping.Lambda

namespace ArgumentLift
/-- Pulling back a particular argument copy preserves the number of ordinary
contractions. This follows from the two concrete path maps, not a rank field. -/
theorem length (lift : ArgumentLift R σ σ') (hσ : Atomic σ) (hσ' : Atomic σ') :
    σ'.length = σ.length := by
  have hc := congrArg List.length lift.copy_paths
  have ho := congrArg List.length lift.original_paths
  rw [hσ.paths_length, List.length_map] at hc
  rw [hσ'.paths_length, List.length_map] at ho
  exact ho.trans hc.symm
end ArgumentLift

/-- Each of the four concrete extraction generators deletes a contraction.
This result concerns the implemented relation; equivalence of its pullback
presentation to the source's full extraction remains a separate obligation. -/
theorem ExtractionStep.rank_lt (h : ExtractionStep r s) : s.rank < r.rank := by
  cases h with
  | residual ρ hρ R S S' hs =>
    simp [ExtractionRun.rank, ExtractionRun.of, ParallelHistory.length_append,
      ParallelHistory.single, ParallelHistory.length]
  | disjoint ρ hρ R σ hσ σ' hσ' last row positive site apart inside =>
    have eq := row.length
    simp only [ExtractionRun.rank, ExtractionRun.of, ParallelHistory.length_append,
      ParallelHistory.single, ParallelHistory.length]
    omega
  | functionPart ρ hρ R σ hσ σ' hσ' last row positive inside =>
    have eq := row.length
    simp only [ExtractionRun.rank, ExtractionRun.of, ParallelHistory.length_append,
      ParallelHistory.single, ParallelHistory.length]
    omega
  | argumentPart ρ hρ R σ hσ σ' hσ' positive lift =>
    have eq := lift.length hσ hσ'
    simp only [ExtractionRun.rank, ExtractionRun.of, ParallelHistory.length_append,
      ParallelHistory.single, ParallelHistory.length]
    omega

/-- Strong termination: arbitrary choices of extraction rules cannot form an
infinite reduction sequence. No particular normalizing strategy is fixed. -/
theorem no_infinite_extraction (m : Term) :
    ¬ ∃ f : Nat → ExtractionRun m, ∀ n, ExtractionStep (f n) (f (n+1)) := by
  rintro ⟨f, h⟩
  have bound (n : Nat) : (f n).rank + n ≤ (f 0).rank := by
    induction n with
    | zero => omega
    | succ n ih => have := (h n).rank_lt; omega
  have := bound ((f 0).rank+1)
  omega

/-- The reduction orientation is reversed for well-founded induction:
successors are smaller than their source. -/
theorem extraction_wellFounded (m : Term) :
    WellFounded (fun s r : ExtractionRun m => ExtractionStep r s) := by
  exact Subrelation.wf (fun h => h.rank_lt)
    (InvImage.wf ExtractionRun.rank Nat.lt_wfRel.wf)

end Lamping.Lambda

