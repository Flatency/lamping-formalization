import Lamping.Lambda.ExtractionClosure
import Lamping.Lambda.ExtractionConfluence
namespace Lamping.Lambda

/-- Reattach an actual ordinary history before a pointed run. -/
def ExtractionRun.prepend (pre : ParallelHistory m t) (ha : Atomic pre)
    (r : ExtractionRun t) : ExtractionRun m :=
  .of (pre.append r.history) (ha.append r.atomic)

theorem ExtractionStep.prepend {r s : ExtractionRun t} (h : ExtractionStep r s)
    (pre : ParallelHistory m t) (ha : Atomic pre) :
    ExtractionStep (r.prepend pre ha) (s.prepend pre ha) := by
  cases h with
  | residual ρ hρ R S S' hs =>
    simpa only [ExtractionRun.prepend,ExtractionRun.of,ParallelHistory.append_assoc] using
      ExtractionStep.residual (pre.append ρ) (ha.append hρ) R S S' hs
  | disjoint ρ hρ R σ hσ σ' hσ' last row positive site apart inside =>
    simpa only [ExtractionRun.prepend,ExtractionRun.of,ParallelHistory.append_assoc] using
      ExtractionStep.disjoint (pre.append ρ) (ha.append hρ) R σ hσ σ' hσ' last row positive site apart inside
  | functionPart ρ hρ R σ hσ σ' hσ' last row positive inside =>
    simpa only [ExtractionRun.prepend,ExtractionRun.of,ParallelHistory.append_assoc] using
      ExtractionStep.functionPart (pre.append ρ) (ha.append hρ) R σ hσ σ' hσ' last row positive inside
  | argumentPart ρ hρ R σ hσ σ' hσ' positive lift =>
    simpa only [ExtractionRun.prepend,ExtractionRun.of,ParallelHistory.append_assoc] using
      ExtractionStep.argumentPart (pre.append ρ) (ha.append hρ) R σ hσ σ' hσ' positive lift

theorem Extraction.prepend {r s : ExtractionRun t} (h : Extraction r s)
    (pre : ParallelHistory m t) (ha : Atomic pre) :
    Extraction (r.prepend pre ha) (s.prepend pre ha) := by
  induction h with
  | refl => exact .refl _
  | cons h hs ih => exact .cons (h.prepend pre ha) ih

theorem ExtractionNormal.of_prepend (hn : ExtractionNormal (r.prepend pre ha)) :
    ExtractionNormal r := by
  rintro ⟨s,hs⟩
  exact hn ⟨s.prepend pre ha,hs.prepend pre ha⟩

theorem ExtractionJoin.prepend {r s : ExtractionRun t} (h : ExtractionJoin r s)
    (pre : ParallelHistory m t) (ha : Atomic pre) :
    ExtractionJoin (r.prepend pre ha) (s.prepend pre ha) := by
  obtain ⟨z,hz,kz⟩ := h
  exact ⟨z.prepend pre ha,hz.prepend pre ha,kz.prepend pre ha⟩

end Lamping.Lambda
