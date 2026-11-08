import Lamping.Lambda.MarkedDevelopmentOrigins
import Lamping.Lambda.LabelAtomicOrigins
namespace Lamping.Lambda.Labelled

/-- Completing the actual old-name development eliminates every redex
whose degree is one of those original selected degrees. INIT is used only
to identify the original name; this does not assert full beta normality. -/
theorem relative_complete_no_selected_degree
    {original target : LTerm} {old : List Path} {ps : List Path} {marked : Marked}
    (initial : INIT original)
    (relative : Marked.RelativeHistory ps (Marked.mark old original.erase) marked)
    (normal : Marked.Normal marked) (labels : History ps original target)
    {p : Path} {degree : Label} (atDegree : target.degreeAt p=some degree)
    (selected : SelectedDegree original old degree) : False := by
  have atomic := selected.atomic initial
  have origins := relative.general
  have sourceOrigins : AtomicOrigins (Marked.mark old original.erase) original :=
    AtomicOrigins.markAt original old []
  have targetOrigins := sourceOrigins.history origins labels
  obtain ⟨name,trace⟩ := targetOrigins.atomic_trace atDegree atomic
  have aligned := (DegreeAligned.initial original old).history origins labels
  have oldDegree : original.degreeAt name=some degree := (aligned.trace_degree trace).symm.trans atDegree
  obtain ⟨selectedName,member,selectedDegree⟩ := selected
  have same : selectedName=name := LTerm.initial_degree_injective initial selectedDegree oldDegree
  have selectedMarked := origins.selected (Marked.selected_mark old original.erase)
  have active : p∈Marked.activePositions marked :=
    (Marked.active_iff_selected_trace selectedMarked p).mpr ⟨name,same ▸ member,trace⟩
  have empty := (Marked.normal_iff_active_empty marked).mp normal
  rw [empty] at active
  exact List.not_mem_nil active

end Lamping.Lambda.Labelled
