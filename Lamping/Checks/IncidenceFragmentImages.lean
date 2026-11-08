import Lamping.Lamping.IncidenceFragmentImages
import Lamping.Checks.IncidenceChaseAlgebra
import Lamping.Lamping.InitialMatching

namespace Lamping.Checks.IncidenceFragmentImagesChecks
open Graph Lambda Lambda.Labelled AG SyntaxIncidence
open CreatedReadingIncidenceExpansionChecks DirectedReadingDecompositionChecks
abbrev actualNet := (encode 0 source.erase).net
abbrev actualSelection := OccurrenceFragmentSelection source actualNet (.inl ())

theorem actual_five_blocks (selection : actualSelection) :
    (canonicalIncidenceImage selection Overlap.exact_forward_five).length=5 ∧
    (orientedIncidenceImage selection Overlap.exact_forward_five).length=5 :=
  ⟨canonicalIncidenceImage_length _ _,orientedIncidenceImage_length _ _⟩

/-- Repeated FN remains two slots, referring to exactly the same occurrence. -/
theorem repeated_FN_same_piece (selection : actualSelection) :
    (canonicalIncidenceImage selection Overlap.exact_forward_five)[1]?=
      (canonicalIncidenceImage selection Overlap.exact_forward_five)[3]? := by
  rfl

theorem actual_roundtrip_images (selection : actualSelection) :
    orientedIncidenceImage selection
      (Overlap.exact_forward_five.append Overlap.exact_forward_five.reverse)=
    orientedIncidenceImage selection Overlap.exact_forward_five ++
      (orientedIncidenceImage selection Overlap.exact_forward_five).reverse.map reverseEdges := by
  rw [orientedIncidenceImage_append selection Overlap.exact_forward_five Overlap.exact_forward_five.reverse,
    orientedIncidenceImage_reverse selection Overlap.exact_forward_five]

theorem actual_choices (first second : actualSelection) :
    orientedIncidenceImage first Overlap.exact_forward_five=
      orientedIncidenceImage second Overlap.exact_forward_five :=
  orientedIncidenceImage_choice_independent (encode_closed_matches source.erase closed 0) _ _ _

theorem actual_selection_supply :
    ∃ selection : actualSelection,
      (orientedIncidenceImage selection Overlap.exact_forward_five).length=5 ∧
      (canonicalIncidenceImage selection Overlap.exact_forward_five)[1]?=
        (canonicalIncidenceImage selection Overlap.exact_forward_five)[3]? := by
  obtain ⟨selection⟩ := (encode_closed_matches source.erase closed 0).occurrence_fragment_selection
    (current:=source) closed
  exact ⟨selection,(actual_five_blocks selection).2,repeated_FN_same_piece selection⟩

open IncidenceChaseAlgebraChecks in
theorem actual_binder_reading_adapters :
    ∃ selection : OccurrenceFragmentSelection zeroTerm (encode 0 zeroTerm.erase).net (.inl ()),
      ∃ finish, ∃ chase : IncidenceChase zeroTerm
        (SyntaxIncidence.target zeroTerm zeroClosed ⟨[.fn,.body],by decide⟩) [[.fn]] [false] finish,
        canonicalIncidenceImage selection chase=canonicalChainImage selection binderReading.chain ∧
        orientedIncidenceImage selection chase=orientedChainImage selection binderReading ∧
        (orientedIncidenceImage selection chase).length=1 := by
  obtain ⟨selection⟩ := (encode_closed_matches zeroTerm.erase zeroClosed 0).occurrence_fragment_selection
    (current:=zeroTerm) zeroClosed
  obtain ⟨finish,chase⟩ := binder_zero_extra_edge
  exact ⟨selection,finish,chase,canonicalIncidenceImage_reading selection binderReading chase,
    orientedIncidenceImage_reading selection binderReading chase,orientedIncidenceImage_length selection chase⟩

theorem actual_boundary_reverse (selection : actualSelection) :
    orientedIncidenceImage selection IncidenceChaseAlgebraChecks.boundary.reverse=
      (orientedIncidenceImage selection IncidenceChaseAlgebraChecks.boundary).reverse.map reverseEdges :=
  orientedIncidenceImage_reverse _ _

#print axioms actual_five_blocks
#print axioms repeated_FN_same_piece
#print axioms actual_roundtrip_images
#print axioms actual_choices
#print axioms actual_selection_supply
#print axioms actual_binder_reading_adapters
#print axioms actual_boundary_reverse
end Lamping.Checks.IncidenceFragmentImagesChecks
