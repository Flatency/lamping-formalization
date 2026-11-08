import Lamping.Lamping.SourceRouteEvaluation
import Lamping.Lamping.ActionCanonicalRoutes
import Lamping.Lambda.DirectedReadingCreation

namespace Lamping.AG
open Graph Lambda Lambda.Labelled
section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable {g : Net signature N B W}

/-- A physical direction acts on every endpoint block, not just its letters. -/
def orientPhysical (forward : Bool) (edges : List (Endpoint g)) : List (Endpoint g) :=
  if forward then edges else reverseEdges edges

/-- Interpret a directed reading by orienting EACH actual physical block. -/
def interpretReadLetters (atoms : Nat → List (Endpoint g))
    (overWord underWord : List (Endpoint g)) (forward : Bool) (letters : List Letter) :
    List (Endpoint g) :=
  letters.flatMap (fun letter => orientPhysical forward (letter.sourceWord atoms overWord underWord))

theorem physical_reverse_append (xs ys : List (Endpoint g)) :
    reverseEdges (xs++ys)=reverseEdges ys++reverseEdges xs := by
  simp [reverseEdges,List.reverse_append,List.map_append]

theorem interpretReadLetters_append (atoms : Nat → List (Endpoint g))
    (overWord underWord : List (Endpoint g)) (forward : Bool) (xs ys : List Letter) :
    interpretReadLetters atoms overWord underWord forward (xs++ys)=
      interpretReadLetters atoms overWord underWord forward xs++
      interpretReadLetters atoms overWord underWord forward ys := by
  simp only [interpretReadLetters,List.flatMap_append]

private theorem reversed_blocks (blocks : Letter → List (Endpoint g)) (letters : List Letter) :
    letters.reverse.flatMap (fun letter => reverseEdges (blocks letter))=
      reverseEdges (letters.flatMap blocks) := by
  induction letters with
  | nil => rfl
  | cons letter letters ih =>
    simp only [List.reverse_cons,List.flatMap_append,List.flatMap_cons,List.flatMap_nil,
      List.append_nil,physical_reverse_append,ih]

private theorem letters_sourceWord (atoms : Nat → List (Endpoint g))
    (overWord underWord : List (Endpoint g)) : ∀ stamp : Label,
    stamp.letters.flatMap (fun letter => letter.sourceWord atoms overWord underWord)=
      stamp.sourceWord atoms overWord underWord
  | .single letter => by simp only [Label.letters,List.flatMap_cons,List.flatMap_nil,Label.sourceWord,List.append_nil]
  | .cons letter rest => by
    simp only [Label.letters,List.flatMap_cons,Label.sourceWord,letters_sourceWord atoms overWord underWord rest]

theorem interpretReadLetters_label (atoms : Nat → List (Endpoint g))
    (overWord underWord : List (Endpoint g)) (forward : Bool) (stamp : Label) :
    interpretReadLetters atoms overWord underWord forward (stamp.readLetters forward)=
      orientPhysical forward (stamp.sourceWord atoms overWord underWord) := by
  cases forward with
  | true => exact letters_sourceWord atoms overWord underWord stamp
  | false =>
    change stamp.letters.reverse.flatMap (fun letter => reverseEdges (letter.sourceWord atoms overWord underWord))=_
    rw [reversed_blocks,letters_sourceWord]
    rfl

theorem SourceEdgeSelection.interpret_read_label
    (selection : SourceEdgeSelection original g root) (edge : BetaEdge g)
    (forward : Bool) (stamp : Label) :
    interpretReadLetters selection.atomWord edge.principal edge.reverseRoute forward
      (stamp.readLetters forward)=orientPhysical forward (selection.evalLabel edge stamp) :=
  interpretReadLetters_label _ _ _ _ _

theorem directed_marker_routes (atoms : Nat → List (Endpoint g))
    (edge : BetaEdge g) (alpha : Label) :
    interpretReadLetters atoms edge.principal edge.reverseRoute true [.over alpha]=edge.principal ∧
    interpretReadLetters atoms edge.principal edge.reverseRoute false [.over alpha]=edge.reverseRoute ∧
    interpretReadLetters atoms edge.principal edge.reverseRoute true [.under alpha]=edge.reverseRoute ∧
    interpretReadLetters atoms edge.principal edge.reverseRoute false [.under alpha]=edge.principal := by
  have route : reverseEdges edge.principal=edge.reverseRoute := by
    simp only [BetaEdge.reverseRoute,reverseEdges,List.map_reverse]
  have back : reverseEdges edge.reverseRoute=edge.principal := by
    rw [←route,reverseEdges_involutive]
  simp [interpretReadLetters,Letter.sourceWord,orientPhysical,route,back]
end
#print axioms physical_reverse_append
#print axioms interpretReadLetters_append
#print axioms interpretReadLetters_label
#print axioms SourceEdgeSelection.interpret_read_label
#print axioms directed_marker_routes
end Lamping.AG
