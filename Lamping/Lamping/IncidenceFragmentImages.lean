import Lamping.Lamping.IncidenceChaseAlgebra
import Lamping.Lamping.ChainFragmentUniqueness
import Lamping.Lamping.DirectedPhysicalLabelEvaluation

namespace Lamping.AG
open Graph Lambda Lambda.Labelled SyntaxIncidence
section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable {current : LTerm} {g : Net signature N B W} {root : B}

/-- Data-list recursion with an actual position proof at every slot. -/
def canonicalIncidenceImage (selection : OccurrenceFragmentSelection current g root)
    (chase : IncidenceChase current v es ds w) : List (List (Endpoint g)) :=
  es.pmap (fun e valid => (selection ⟨e,valid⟩).fragment.segments) chase.valid_edges

def orientedIncidenceImage (selection : OccurrenceFragmentSelection current g root)
    (chase : IncidenceChase current v es ds w) : List (List (Endpoint g)) :=
  List.zipWith (fun block forward => orientPhysical forward block)
    (canonicalIncidenceImage selection chase) ds

theorem canonicalIncidenceImage_length (selection : OccurrenceFragmentSelection current g root)
    (chase : IncidenceChase current v es ds w) :
    (canonicalIncidenceImage selection chase).length=es.length := List.length_pmap

theorem orientedIncidenceImage_length (selection : OccurrenceFragmentSelection current g root)
    (chase : IncidenceChase current v es ds w) :
    (orientedIncidenceImage selection chase).length=es.length := by
  simp only [orientedIncidenceImage,List.length_zipWith,canonicalIncidenceImage_length,chase.length]
  omega

theorem canonicalIncidenceImage_append (selection : OccurrenceFragmentSelection current g root)
    (first : IncidenceChase current v es ds w) (second : IncidenceChase current w fs bs z) :
    canonicalIncidenceImage selection (first.append second)=
      canonicalIncidenceImage selection first++canonicalIncidenceImage selection second := by
  simp only [canonicalIncidenceImage,List.pmap_append]

theorem orientedIncidenceImage_append (selection : OccurrenceFragmentSelection current g root)
    (first : IncidenceChase current v es ds w) (second : IncidenceChase current w fs bs z) :
    orientedIncidenceImage selection (first.append second)=
      orientedIncidenceImage selection first++orientedIncidenceImage selection second := by
  unfold orientedIncidenceImage
  rw [canonicalIncidenceImage_append]
  exact List.zipWith_append ((canonicalIncidenceImage_length selection first).trans first.length)

theorem canonicalIncidenceImage_reverse (selection : OccurrenceFragmentSelection current g root)
    (chase : IncidenceChase current v es ds w) :
    canonicalIncidenceImage selection chase.reverse=(canonicalIncidenceImage selection chase).reverse := by
  simp only [canonicalIncidenceImage,List.pmap_reverse]

private theorem orient_not (b : Bool) (block : List (Endpoint g)) :
    orientPhysical (!b) block=reverseEdges (orientPhysical b block) := by
  cases b <;> simp [orientPhysical,reverseEdges_involutive]

theorem orientedIncidenceImage_reverse (selection : OccurrenceFragmentSelection current g root)
    (chase : IncidenceChase current v es ds w) :
    orientedIncidenceImage selection chase.reverse=
      (orientedIncidenceImage selection chase).reverse.map reverseEdges := by
  unfold orientedIncidenceImage
  rw [canonicalIncidenceImage_reverse selection chase,
    List.reverse_zipWith ((canonicalIncidenceImage_length selection chase).trans chase.length)]
  simp only [List.zipWith_map_right,List.map_zipWith]
  simp only [orient_not]

theorem canonicalIncidenceImage_choice_independent (matching : Matches g root current.erase)
    (first second : OccurrenceFragmentSelection current g root)
    (chase : IncidenceChase current v es ds w) :
    canonicalIncidenceImage first chase=canonicalIncidenceImage second chase := by
  unfold canonicalIncidenceImage
  apply List.pmap_congr_left
  intro e member left right
  exact OccurrenceFragment.segments_unique matching _ _

theorem orientedIncidenceImage_choice_independent (matching : Matches g root current.erase)
    (first second : OccurrenceFragmentSelection current g root)
    (chase : IncidenceChase current v es ds w) :
    orientedIncidenceImage first chase=orientedIncidenceImage second chase := by
  unfold orientedIncidenceImage
  rw [canonicalIncidenceImage_choice_independent matching first second chase]

/-- Any actual chase with this reading's literal slots has the existing image. -/
theorem canonicalIncidenceImage_reading (selection : OccurrenceFragmentSelection current g root)
    (reading : PrerequisiteReading current p es ds) (chase : IncidenceChase current v es ds w) :
    canonicalIncidenceImage selection chase=canonicalChainImage selection reading.chain := by
  unfold canonicalIncidenceImage canonicalChainImage
  rw [List.pmap_eq_map_attach]
  apply List.map_congr_left
  intro e member
  rfl

theorem orientedIncidenceImage_reading (selection : OccurrenceFragmentSelection current g root)
    (reading : PrerequisiteReading current p es ds) (chase : IncidenceChase current v es ds w) :
    orientedIncidenceImage selection chase=orientedChainImage selection reading := by
  unfold orientedIncidenceImage orientedChainImage
  rw [canonicalIncidenceImage_reading selection reading chase]
  rfl

#print axioms canonicalIncidenceImage_append
#print axioms orientedIncidenceImage_reverse
#print axioms canonicalIncidenceImage_choice_independent
#print axioms orientedIncidenceImage_reading
end
end Lamping.AG
