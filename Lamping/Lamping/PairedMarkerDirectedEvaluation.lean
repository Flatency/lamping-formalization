import Lamping.Lamping.DirectedPhysicalLabelEvaluation
import Lamping.Lamping.PairedMarkerFirstComparison

namespace Lamping.AG
open Graph Lambda Lambda.Labelled
section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable {g : Net signature N B W} {root : B}

private theorem interpret_cons (atoms : Nat → List (Endpoint g))
    (overWord underWord : List (Endpoint g)) (forward : Bool) (letter : Letter) (letters : List Letter) :
    interpretReadLetters atoms overWord underWord forward (letter::letters)=
      orientPhysical forward (letter.sourceWord atoms overWord underWord)++
        interpretReadLetters atoms overWord underWord forward letters := rfl

/-- A physical interpretation of the COMPLETE local reading formula. The
actual extra ARG or APP lookup is retained at either root overlap. -/
def ExactPhysicalDirectedFormula (selection : SourceEdgeSelection original g root)
    (edge : BetaEdge g) (source : LTerm) (site : Path) (alpha : Label)
    (forward : Bool) (firstNode lastNode : LTerm) (marker : Letter) (current : LTerm) : Prop :=
  orientPhysical forward (selection.evalLabel edge current.label)=
    orientPhysical forward (selection.evalLabel edge firstNode.label)++
      orientPhysical forward (marker.sourceWord selection.atomWord edge.principal edge.reverseRoute)++
        orientPhysical forward (selection.evalLabel edge lastNode.label) ∨
  (forward=true ∧marker=.over alpha ∧∃ argument,source.subterm (site++[.arg])=some argument ∧
    orientPhysical forward (selection.evalLabel edge current.label)=
      orientPhysical forward (selection.evalLabel edge firstNode.label)++
        orientPhysical forward (marker.sourceWord selection.atomWord edge.principal edge.reverseRoute)++
          (orientPhysical forward (selection.evalLabel edge lastNode.label)++
            orientPhysical forward ((Letter.under alpha).sourceWord selection.atomWord edge.principal edge.reverseRoute)++
              orientPhysical forward (selection.evalLabel edge argument.label))) ∨
  (forward=false ∧marker=.under alpha ∧∃ app,source.subterm site=some app ∧
    orientPhysical forward (selection.evalLabel edge current.label)=
      orientPhysical forward (selection.evalLabel edge firstNode.label)++
        orientPhysical forward (marker.sourceWord selection.atomWord edge.principal edge.reverseRoute)++
          (orientPhysical forward (selection.evalLabel edge lastNode.label)++
            orientPhysical forward ((Letter.over alpha).sourceWord selection.atomWord edge.principal edge.reverseRoute)++
              orientPhysical forward (selection.evalLabel edge app.label)))

theorem exact_directed_formula_physical
    (selection : SourceEdgeSelection original g root) (edge : BetaEdge g)
    (formula : ExactDirectedReadingFormula source site alpha forward firstNode lastNode marker current) :
    ExactPhysicalDirectedFormula selection edge source site alpha forward firstNode lastNode marker current := by
  rcases formula with ordinary | resultOverlap | copyOverlap
  · apply Or.inl
    have evaluated := congrArg (interpretReadLetters selection.atomWord edge.principal edge.reverseRoute forward) ordinary
    simpa only [interpretReadLetters_append,interpret_cons,SourceEdgeSelection.interpret_read_label,List.append_assoc] using evaluated
  · obtain ⟨direction,markerKind,argument,lookup,equation⟩ := resultOverlap
    refine Or.inr (Or.inl ⟨direction,markerKind,argument,lookup,?_⟩)
    subst forward
    have normalized : current.label.readLetters true=firstNode.label.readLetters true++marker::
        (lastNode.label.readLetters true++(.under alpha)::argument.label.readLetters true) := equation
    have evaluated := congrArg (interpretReadLetters selection.atomWord edge.principal edge.reverseRoute true) normalized
    simpa only [interpretReadLetters_append,interpret_cons,SourceEdgeSelection.interpret_read_label,
      List.append_assoc] using evaluated
  · obtain ⟨direction,markerKind,app,lookup,equation⟩ := copyOverlap
    refine Or.inr (Or.inr ⟨direction,markerKind,app,lookup,?_⟩)
    subst forward
    have normalized : current.label.readLetters false=firstNode.label.readLetters false++marker::
        (lastNode.label.readLetters false++(.over alpha)::app.label.readLetters false) := equation
    have evaluated := congrArg (interpretReadLetters selection.atomWord edge.principal edge.reverseRoute false) normalized
    simpa only [interpretReadLetters_append,interpret_cons,SourceEdgeSelection.interpret_read_label,
      List.append_assoc] using evaluated

theorem PairedMarkerEventGeometry.physical_formula
    {leaf : DirectedMarkerLeafOutput F source degree forward ps word}
    (paired : PairedMarkerEventGeometry leaf localSource localTarget)
    (selection : SourceEdgeSelection original g root) (edge : BetaEdge g) :
    ExactPhysicalDirectedFormula selection edge paired.middle leaf.site paired.alpha forward
      paired.firstNode paired.lastNode paired.marker paired.current :=
  exact_directed_formula_physical selection edge paired.formula

/-- The accepted FIRST comparison, with the actual physical direction. -/
theorem paired_marker_first_oriented_evaluations
    (left : DirectedMarkerLeafOutput F source degree forward ps leftWord)
    (right : DirectedMarkerLeafOutput F source degree forward ps rightWord)
    (leftPaired : PairedMarkerEventGeometry left (initLabels source.erase) localTarget)
    (rightPaired : PairedMarkerEventGeometry right (initLabels source.erase) localTarget)
    (matching : Matches g root source.erase)
    (selected : ∀name∈F,source.degreeAt name=some degree)
    (sourceSafe : source.OuterBarsSafe (fun x=>x≠degree))
    (prefixHistory : History prior original source) (initial : INIT original)
    (closed : Closed source.erase)
    (sourceSelection : OccurrenceFragmentSelection source g root)
    (representation : ChainRepresentationInvariant closed sourceSelection)
    (selection : SourceEdgeSelection (initLabels source.erase) g root)
    (physical : BetaEdge g) (sameWord : leftWord=rightWord) :
    orientPhysical forward (selection.evalLabel physical leftPaired.firstNode.label)=
      orientPhysical forward (selection.evalLabel physical rightPaired.firstNode.label) := by
  exact congrArg (orientPhysical forward) (paired_marker_first_evaluations left right leftPaired rightPaired
    matching selected sourceSafe prefixHistory initial closed sourceSelection representation selection physical sameWord)
end
#print axioms exact_directed_formula_physical
#print axioms PairedMarkerEventGeometry.physical_formula
#print axioms paired_marker_first_oriented_evaluations
end Lamping.AG
