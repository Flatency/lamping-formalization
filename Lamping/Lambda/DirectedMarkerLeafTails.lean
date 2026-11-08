import Lamping.Lambda.DirectedMarkerLeafWords
import Lamping.Lambda.SafeIncomingHistory
namespace Lamping.Lambda.Labelled

/-- Three actual local remainders. The overlap cases retain the actual ARG
or APP lookup, not a freely supplied word. This is an OUTPUT classification. -/
def ExactMarkerLeafTail
    (leaf : DirectedMarkerLeafOutput F source degree forward ps word) (tail : List Letter) : Prop :=
  tail=leaf.lastNode.label.readLetters forward ∨
  (forward=true ∧leaf.marker=.over degree ∧∃argument,
    leaf.middle.subterm (leaf.site++[.arg])=some argument ∧
    tail=leaf.lastNode.label.readLetters forward++(.under degree)::argument.label.letters) ∨
  (forward=false ∧leaf.marker=.under degree ∧∃app,
    leaf.middle.subterm leaf.site=some app ∧
    tail=leaf.lastNode.label.readLetters forward++(.over degree)::app.label.letters.reverse)

/-- Recover the exact ordinary/overlap tail of THIS actual safe leaf. -/
theorem DirectedMarkerLeafOutput.local_tail
    (leaf : DirectedMarkerLeafOutput F source degree forward ps word) :
    ∃tail,ExactMarkerLeafTail leaf tail ∧
      leaf.current.label.readLetters forward=leaf.firstNode.label.readLetters forward++leaf.marker::tail := by
  rcases leaf.formula with ordinary | resultOverlap | copyOverlap
  · exact ⟨_,Or.inl rfl,ordinary⟩
  · obtain ⟨direction,marker,argument,atArgument,equation⟩ := resultOverlap
    exact ⟨_,Or.inr (Or.inl ⟨direction,marker,argument,atArgument,rfl⟩),equation⟩
  · obtain ⟨direction,marker,app,atApp,equation⟩ := copyOverlap
    exact ⟨_,Or.inr (Or.inr ⟨direction,marker,app,atApp,rfl⟩),equation⟩

/-- The full tail includes the derived continuation. No cancellation of
unknown continuations or identification with a physical suffix is made. -/
theorem DirectedMarkerLeafOutput.full_tail
    (leaf : DirectedMarkerLeafOutput F source degree forward ps word) :
    ∃tail,ExactMarkerLeafTail leaf tail ∧
      word=leaf.firstNode.label.readLetters forward++leaf.marker::(tail++leaf.continuation) := by
  obtain ⟨tail,kind,equation⟩ := leaf.local_tail
  refine ⟨tail,kind,leaf.equation.trans ?_⟩
  have extended:=congrArg (fun xs : List Letter=>xs++leaf.continuation) equation
  exact extended.trans (by simp only [List.append_assoc,List.cons_append])

/-- Equal complete words in the SAME actual reading direction determine
safe first labels, marker, and FULL tails, even when leaf event times differ.
They do not determine the two local lastNode labels by cancellation. -/
theorem DirectedMarkerLeafOutput.compare_full_tails
    (left : DirectedMarkerLeafOutput leftF leftSource degree forward leftPs leftWord)
    (right : DirectedMarkerLeafOutput rightF rightSource degree forward rightPs rightWord)
    (same : leftWord=rightWord) :
    ∃leftTail rightTail,ExactMarkerLeafTail left leftTail ∧ExactMarkerLeafTail right rightTail ∧
      left.firstNode.label=right.firstNode.label ∧left.marker=right.marker ∧
      leftTail++left.continuation=rightTail++right.continuation := by
  obtain ⟨leftTail,leftKind,leftEquation⟩ := left.full_tail
  obtain ⟨rightTail,rightKind,rightEquation⟩ := right.full_tail
  have compared:=Label.readLetters_first_marker_unique
    left.firstSafe right.firstSafe left.marks right.marks
    (leftEquation.symm.trans (same.trans rightEquation))
  exact ⟨leftTail,rightTail,leftKind,rightKind,compared⟩

/-- The real leaf prefix history supplies an actual original first-node
lookup with the same FULL label. Its coordinate is never inferred from a label. -/
theorem DirectedMarkerLeafOutput.original_first_label
    (leaf : DirectedMarkerLeafOutput F source degree forward ps word)
    (selected : ∀name∈F,source.degreeAt name=some degree) :
    ∃position node,source.subterm position=some node ∧
      BetaNodeHistoryPreimage leaf.event.labels leaf.first position ∧
      node.label=leaf.firstNode.label := by
  obtain ⟨position,node,atNode,trace⟩ := leaf.event.labels.node_preimage_from_lookup leaf.firstLookup
  have uncreated:=leaf.event.beforeOld.safe_incoming_uncreated
    (DegreeAligned.initial source F) selected trace leaf.firstLookup leaf.firstSafe
  obtain ⟨actual,atActual,same⟩ := uncreated.source_label leaf.firstLookup
  exact ⟨position,actual,atActual,trace,same⟩

/-- This compares only ORIGINAL first-node labels from the actual two leaf
prefixes. Neither current coordinates nor paired other-last labels are equalized. -/
theorem DirectedMarkerLeafOutput.compare_original_first_labels
    (left : DirectedMarkerLeafOutput F source degree forward leftPs leftWord)
    (right : DirectedMarkerLeafOutput F source degree forward rightPs rightWord)
    (selected : ∀name∈F,source.degreeAt name=some degree)
    (same : leftWord=rightWord) :
    ∃leftPosition rightPosition leftNode rightNode,
      source.subterm leftPosition=some leftNode ∧source.subterm rightPosition=some rightNode ∧
      BetaNodeHistoryPreimage left.event.labels left.first leftPosition ∧
      BetaNodeHistoryPreimage right.event.labels right.first rightPosition ∧
      leftNode.label=rightNode.label := by
  obtain ⟨_,_,_,_,firstEqual,_,_⟩ := left.compare_full_tails right same
  obtain ⟨lp,ln,atL,traceL,labelL⟩ := left.original_first_label selected
  obtain ⟨rp,rn,atR,traceR,labelR⟩ := right.original_first_label selected
  exact ⟨lp,rp,ln,rn,atL,atR,traceL,traceR,labelL.trans (firstEqual.trans labelR.symm)⟩

#print axioms DirectedMarkerLeafOutput.local_tail
#print axioms DirectedMarkerLeafOutput.full_tail
#print axioms DirectedMarkerLeafOutput.compare_full_tails
#print axioms DirectedMarkerLeafOutput.original_first_label
#print axioms DirectedMarkerLeafOutput.compare_original_first_labels
end Lamping.Lambda.Labelled
