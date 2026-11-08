import Lamping.Lambda.DirectedMarkerLeafTails
namespace Lamping.Lambda.Labelled

/-- OUTPUT of the operational marker spine: an actual complete chain in its
relative OLD source. These fields are proved by the producer below. -/
structure MarkerSourceChain (F : List Path) (source : LTerm) (degree : Label)
    (forward : Bool) (beforeLabels : List (Option Label)) (word : List Letter) where
  start : Path
  before : List Path
  reader : Path
  first : Path
  selectedName : Path
  firstNode : LTerm
  marker : Letter
  rest : List Letter
  selected : selectedName∈F
  lookup : source.subterm first=some firstNode
  safe : firstNode.label.OuterBarsSafe (fun x=>x≠degree)
  segment : PrerequisitePrefix source start before reader
  reading : PrerequisiteReadsDirected source reader first forward
  chain : PrerequisiteChain source start (before++[first,selectedName++[.fn]])
  before_eq : beforeLabels=before.map source.labelAt
  marks : marker.MarksDegree degree
  equation : word=firstNode.label.readLetters forward++marker::rest

def MarkerSourceChain.edges (output : MarkerSourceChain F source degree forward beforeLabels word) : List Path :=
  output.before++[output.first,output.selectedName++[.fn]]

/-- No caller supplies a source chain or source isomorphism. -/
theorem DirectedMarkerSpine.source_chain_output
    (spine : DirectedMarkerSpine F source degree forward ps target beforeLabels edge)
    (selected : ∀name∈F,source.degreeAt name=some degree)
    (sourceSafe : source.OuterBarsSafe (fun x=>x≠degree))
    (lookup : target.subterm edge=some current) :
    Nonempty (MarkerSourceChain F source degree forward beforeLabels (current.label.readLetters forward)) := by
  obtain ⟨s,bs,r,f,name,node,marker,rest,chosen,atNode,safe,segment,reading,chain,labels,marks,equation⟩ :=
    spine.source_marker_prefix selected sourceSafe lookup
  exact ⟨⟨s,bs,r,f,name,node,marker,rest,chosen,atNode,safe,segment,reading,chain,labels,marks,equation⟩⟩

private theorem degree_function_label {source : LTerm} {name : Path} {degree : Label} (selected : source.degreeAt name=some degree) :
    source.labelAt (name++[.fn])=some degree := by
  obtain ⟨beta,body,arg,lookup⟩ := LTerm.degreeAt_redex selected
  rw [LTerm.labelAt,LTerm.subterm_append,lookup];rfl

/-- Equal complete current words, in the SAME direction, compare the safe
original first labels and marker remainders. No continuation is cancelled. -/
theorem MarkerSourceChain.compare_first
    (left : MarkerSourceChain F source degree forward leftBefore leftWord)
    (right : MarkerSourceChain F source degree forward rightBefore rightWord)
    (same : leftWord=rightWord) :
    left.firstNode.label=right.firstNode.label ∧left.marker=right.marker ∧left.rest=right.rest := by
  exact Label.readLetters_first_marker_unique left.safe right.safe left.marks right.marks
    (left.equation.symm.trans (same.trans right.equation))

/-- These are full label vectors of the two actual COMPLETE source chains,
including the final selected redex edge. This is not yet a bare incidence iso. -/
theorem MarkerSourceChain.compare_chain_labels
    (left : MarkerSourceChain F source degree forward leftBefore leftWord)
    (right : MarkerSourceChain F source degree forward rightBefore rightWord)
    (selected : ∀name∈F,source.degreeAt name=some degree)
    (sameBefore : leftBefore=rightBefore) (sameWord : leftWord=rightWord) :
    left.edges.map source.labelAt=right.edges.map source.labelAt := by
  have first := (left.compare_first right sameWord).1
  have before := left.before_eq.symm.trans (sameBefore.trans right.before_eq)
  have leftLookup : source.labelAt left.first=some left.firstNode.label := by
    simp only [LTerm.labelAt,left.lookup,Option.map_some]
  have rightLookup : source.labelAt right.first=some right.firstNode.label := by
    simp only [LTerm.labelAt,right.lookup,Option.map_some]
  simp only [MarkerSourceChain.edges,List.map_append,List.map_cons,List.map_nil,
    leftLookup,rightLookup,degree_function_label (selected _ left.selected),
    degree_function_label (selected _ right.selected),first,before]

/-- Pair the two actual source-chain outputs. Equal vectors are a conclusion;
the pending incidence reflection bridge is not an input. -/
theorem DirectedMarkerSpine.compare_source_chain_outputs
    (leftSpine : DirectedMarkerSpine F source degree forward leftPs leftTarget leftBefore leftEdge)
    (rightSpine : DirectedMarkerSpine F source degree forward rightPs rightTarget rightBefore rightEdge)
    (selected : ∀name∈F,source.degreeAt name=some degree)
    (sourceSafe : source.OuterBarsSafe (fun x=>x≠degree))
    (leftLookup : leftTarget.subterm leftEdge=some leftCurrent)
    (rightLookup : rightTarget.subterm rightEdge=some rightCurrent)
    (sameBefore : leftBefore=rightBefore)
    (sameWord : leftCurrent.label.readLetters forward=rightCurrent.label.readLetters forward) :
    ∃ left : MarkerSourceChain F source degree forward leftBefore (leftCurrent.label.readLetters forward),
    ∃ right : MarkerSourceChain F source degree forward rightBefore (rightCurrent.label.readLetters forward),
      left.firstNode.label=right.firstNode.label ∧
      left.edges.map source.labelAt=right.edges.map source.labelAt := by
  obtain ⟨left⟩ := leftSpine.source_chain_output selected sourceSafe leftLookup
  obtain ⟨right⟩ := rightSpine.source_chain_output selected sourceSafe rightLookup
  exact ⟨left,right,(left.compare_first right sameWord).1,
    left.compare_chain_labels right selected sameBefore sameWord⟩

#print axioms DirectedMarkerSpine.source_chain_output
#print axioms MarkerSourceChain.compare_first
#print axioms DirectedMarkerSpine.compare_source_chain_outputs
#print axioms MarkerSourceChain.compare_chain_labels
end Lamping.Lambda.Labelled
