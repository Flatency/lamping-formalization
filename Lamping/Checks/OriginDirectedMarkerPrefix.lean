import Lamping.Lambda.OriginDirectedMarkerPrefix
import Lamping.Checks.DirectedReadingDecomposition
namespace Lamping.Checks.OriginDirectedMarkerPrefixChecks
open Lambda Lambda.Labelled
open DirectedReadingDecompositionChecks

/-- Every result FUNCTION fixture retains its complete ordinary/overlap
formula while its first marker is forced to over by the actual origin. -/
theorem result_function_marker : ∃first last marker,
    source.subterm [.fn]=some first ∧source.subterm [.fn,.fn,.body]=some last ∧
    ExactDirectedReadingFormula source [.fn] (.atom 2) true first last marker result ∧marker=.over (.atom 2) := by
  obtain ⟨first,last,marker,firstAt,lastAt,_marks,formula⟩ := result_function_decomposition
  have kind := functionOrigin.formula_marker (forward:=true) step rfl ⟨Or.inl ⟨_,_,_,rfl,rfl⟩,rfl⟩ rfl firstAt formula
  exact ⟨first,last,marker,firstAt,lastAt,formula,kind.trans (by simp [originMarker])⟩

theorem copy_context_zero_marker : ∃first last marker,
    source.subterm [.fn,.arg]=some first ∧source.subterm [.fn,.fn,.body]=some last ∧
    ExactDirectedReadingFormula source [.fn] (.atom 2) false first last marker result ∧marker=.under (.atom 2) := by
  obtain ⟨first,last,marker,firstAt,lastAt,_marks,formula⟩ := copy_context_decomposition
  have kind := contextOrigin.formula_marker (forward:=false) step rfl ⟨Or.inr ⟨_,_,rfl,rfl⟩,rfl⟩ rfl firstAt formula
  exact ⟨first,last,marker,firstAt,lastAt,formula,kind.trans (by decide)⟩

theorem result_context_marker : ∃first last marker,
    rSource.subterm [.fn,.fn,.body]=some first ∧rSource.subterm [.fn]=some last ∧
    ExactDirectedReadingFormula rSource [.fn] (.atom 2) false first last marker rResult ∧marker=.over (.atom 2) := by
  obtain ⟨first,last,marker,firstAt,lastAt,_marks,formula⟩ := result_context_decomposition
  have kind := (BetaIncomingReadingOrigin.resultLambda rfl rfl rfl).formula_marker (forward:=false)
    rStep rfl ⟨Or.inr ⟨_,_,rfl,rfl⟩,rfl⟩ rfl firstAt formula
  exact ⟨first,last,marker,firstAt,lastAt,formula,kind.trans (by simp [originMarker])⟩

theorem copy_function_marker : ∃first last marker,
    cSource.subterm [.body,.fn,.body,.fn]=some first ∧cSource.subterm [.body,.arg]=some last ∧
    ExactDirectedReadingFormula cSource [.body] (.atom 2) true first last marker cCurrent ∧marker=.under (.atom 2) := by
  obtain ⟨first,last,marker,firstAt,lastAt,_marks,formula⟩ := copy_function_decomposition
  have kind := cOrigin.formula_marker (forward:=true) cStep rfl ⟨Or.inl ⟨_,_,_,rfl,rfl⟩,rfl⟩ rfl firstAt formula
  exact ⟨first,last,marker,firstAt,lastAt,formula,kind.trans (by decide)⟩

/-- Directly consume the stronger operational theorem at the true q=[]
copy overlap; FIRST ARG and LAST BODY are retained, not interchanged. -/
theorem actual_copied_zero_prefix : ∃first last marker rest,
    source.subterm [.fn,.arg]=some first ∧source.subterm [.fn,.fn,.body]=some last ∧
    marker=.under (.atom 2) ∧
    result.label.readLetters false=first.label.readLetters false++marker::rest := by
  obtain ⟨first,last,marker,rest,firstAt,lastAt,_marks,kind,formula⟩ :=
    contextOrigin.directed_label_prefix_kind (forward:=false) step rfl ⟨Or.inr ⟨_,_,rfl,rfl⟩,rfl⟩ rfl
  exact ⟨first,last,marker,rest,firstAt,lastAt,kind.trans (by decide),formula⟩

#print axioms result_function_marker
#print axioms copy_context_zero_marker
#print axioms result_context_marker
#print axioms copy_function_marker
#print axioms actual_copied_zero_prefix
end Lamping.Checks.OriginDirectedMarkerPrefixChecks
