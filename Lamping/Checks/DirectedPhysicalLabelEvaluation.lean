import Lamping.Lamping.DirectedPhysicalLabelEvaluation
namespace Lamping.Checks.DirectedPhysicalLabelEvaluationChecks
open AG Graph Lambda Lambda.Labelled
section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable {g : Net signature N B W}

/-- Two actual endpoint occurrences in one atom block. Reversing the syntax
letter leaves this block untouched; physical reversal changes both endpoints.
This is an algebra regression for every real pairing, not a path assertion. -/
theorem two_occurrence_atomic_block_requires_physical_reverse (e : Endpoint g) :
    let atoms : Nat → List (Endpoint g) := fun _ => [e,e]
    ((Label.atom 0).readLetters false).flatMap (fun l => l.sourceWord atoms [] []) ≠
      interpretReadLetters atoms [] [] false ((Label.atom 0).readLetters false) := by
  dsimp [Label.atom,Label.readLetters,Label.letters,interpretReadLetters,orientPhysical,
    Letter.sourceWord,reverseEdges]
  intro same
  have first : e=g.wire e := (List.cons.inj same).1
  exact g.wire.fixedPointFree e first.symm

theorem directed_literal_routes (atoms : Nat → List (Endpoint g)) (edge : BetaEdge g) (alpha : Label) :
    interpretReadLetters atoms edge.principal edge.reverseRoute false [.under alpha]=edge.principal :=
  (directed_marker_routes atoms edge alpha).2.2.2
end
#print axioms two_occurrence_atomic_block_requires_physical_reverse
#print axioms directed_literal_routes
end Lamping.Checks.DirectedPhysicalLabelEvaluationChecks
