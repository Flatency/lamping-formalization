import Lamping.Lambda.ExtractionTermination
import Lamping.Lambda.AtomicHistories
import Lamping.Lambda.Standardization
namespace Lamping.Lambda

/-- Source extraction is the reflexive transitive closure of its four rules. -/
inductive Extraction : ExtractionRun m → ExtractionRun m → Prop where
  | refl (r) : Extraction r r
  | cons : ExtractionStep r s → Extraction s t → Extraction r t
namespace Extraction
 theorem single (h : ExtractionStep r s) : Extraction r s := .cons h (.refl _)
 theorem trans (h : Extraction r s) (k : Extraction s t) : Extraction r t := by
   induction h with
   | refl => exact k
   | cons h hs ih => exact .cons h (ih k)
end Extraction

def ExtractionNormal (r : ExtractionRun m) : Prop := ¬ ∃ s, ExtractionStep r s

 theorem ExtractionStep.positive (h : ExtractionStep r s) : 0 < s.rank := by
   cases h with
   | residual => simp [ExtractionRun.rank, ExtractionRun.of, ParallelHistory.length_append,
       ParallelHistory.single, ParallelHistory.length]
   | disjoint ρ hρ R σ hσ σ' hσ' last row positive site apart inside =>
     simp only [ExtractionRun.rank, ExtractionRun.of, ParallelHistory.length_append]
     omega
   | functionPart ρ hρ R σ hσ σ' hσ' last row positive inside =>
     simp only [ExtractionRun.rank, ExtractionRun.of, ParallelHistory.length_append]
     omega
   | argumentPart ρ hρ R σ hσ σ' hσ' positive lift =>
     have he := lift.length hσ hσ'
     simp only [ExtractionRun.rank, ExtractionRun.of, ParallelHistory.length_append]
     omega

 theorem Extraction.positive (h : Extraction r s) (hr : 0 < r.rank) : 0 < s.rank := by
   induction h with
   | refl => exact hr
   | cons h hs ih => exact ih h.positive

/-- Termination yields a normal successor of every run. This existential result
 does not claim decidable extraction, standardness, confluence or a family
 canonical representative. -/
 theorem extraction_normal_exists (r : ExtractionRun m) :
     ∃ s, Extraction r s ∧ ExtractionNormal s := by
   classical
   induction r using (extraction_wellFounded m).induction with
   | h r ih =>
     by_cases hn : ∃ s, ExtractionStep r s
     · obtain ⟨s, hs⟩ := hn
       obtain ⟨q, hq, hnq⟩ := ih s hs
       exact ⟨q, .cons hs hq, hnq⟩
     · exact ⟨r, .refl _, hn⟩

 theorem extraction_normal_exists_positive (r : ExtractionRun m) (hr : 0 < r.rank) :
     ∃ s, Extraction r s ∧ ExtractionNormal s ∧ 0 < s.rank := by
   obtain ⟨s, hs, hns⟩ := extraction_normal_exists r
   exact ⟨s, hs, hns, hs.positive hr⟩

/-- Source canonical condition on a nonempty ordinary contraction sequence.
 No existence or uniqueness is stored as a field. -/
def CanonicalRun (r : ExtractionRun m) : Prop :=
   0 < r.rank ∧ Standard r.history ∧ ExtractionNormal r
end Lamping.Lambda

