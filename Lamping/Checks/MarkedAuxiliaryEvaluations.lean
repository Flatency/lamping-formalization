import Lamping.Lamping.MarkedAuxiliaryEvaluations
import Lamping.Checks.PairedAuxWritingFirstAtoms

namespace Lamping.Checks.MarkedAuxiliaryEvaluationsChecks
open Graph Lambda Lambda.Labelled AG SyntaxIncidence
open NodeLabelSuffixOriginsChecks AuxiliaryNodeHistoryOriginsChecks

abbrev edge : SyntaxIncidence.Edge target:=PairedAuxWritingFirstAtomsChecks.App.edge
abbrev F : List Path:=AuxWritingFirstAtomOriginChecks.App.F

def currentArgumentVertex : ProperPosition target:=⟨[.arg],Or.inl ⟨_,_,_,rfl⟩⟩

theorem target_iso : SuccessfulEndpointIso target (actualHistory.closed closed)
    (SyntaxIncidence.target target (actualHistory.closed closed) edge)
    (SyntaxIncidence.target target (actualHistory.closed closed) edge) := by
  have spec : Target target edge.val (some currentArgumentVertex):=Or.inl rfl
  rw [SyntaxIncidence.target_eq_of_spec target (actualHistory.closed closed) edge spec]
  exact .refl_of_chain actual_target_endpoint_chain

/-- A real marked APP incoming edge with real successful source and target
endpoint chains directly invokes the NEW complete-word theorem. SOURCEJoint
is an honest graph induction hypothesis, not fixture history truth. -/
theorem actual_marked_app_whole
    {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
    {g : Net signature N B W} {root : B}
    (matching : Matches g root source.erase)
    (sourceSelection : OccurrenceFragmentSelection source g root)
    (sourceJoint : JointRepresentation closed sourceSelection)
    (selection : SourceEdgeSelection (initLabels source.erase) g root)
    (physical : BetaEdge g) :
    selection.evalLabel physical currentArgument.label=selection.evalLabel physical currentArgument.label :=
  marked_auxiliary_whole_evaluations initial (.nil source)
    AuxWritingFirstAtomOriginChecks.App.old actualHistory
    PairedAuxWritingFirstAtomsChecks.App.selected (initial.outerBarsSafe _) closed matching sourceSelection sourceJoint
    AuxWritingFirstAtomOriginChecks.App.localHistory edge edge actual_lookup actual_lookup actual_lookup actual_lookup
    actual_auxiliary actual_auxiliary rfl actual_marked PairedAuxWritingFirstAtomsChecks.App.source_iso target_iso
    selection physical

/-- FALSE direction reverses the COMPLETE already compared evaluator values;
no local-map tail cancellation or prerequisite membership of Aux is used. -/
theorem actual_marked_app_reverse_whole
    {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
    {g : Net signature N B W} {root : B}
    (matching : Matches g root source.erase)
    (sourceSelection : OccurrenceFragmentSelection source g root)
    (sourceJoint : JointRepresentation closed sourceSelection)
    (selection : SourceEdgeSelection (initLabels source.erase) g root)
    (physical : BetaEdge g) :
    interpretReadLetters selection.atomWord physical.principal physical.reverseRoute false
        (currentArgument.label.readLetters false)=
      interpretReadLetters selection.atomWord physical.principal physical.reverseRoute false
        (currentArgument.label.readLetters false) := by
  have complete:=actual_marked_app_whole matching sourceSelection sourceJoint selection physical
  exact (selection.interpret_read_label physical false currentArgument.label).trans
    ((congrArg (orientPhysical false) complete).trans
      (selection.interpret_read_label physical false currentArgument.label).symm)

theorem real_marked_app_domain : INIT source ∧Closed source.erase ∧
    History [[.arg]] source target ∧AuxiliaryAt target [.arg] ∧
    ¬currentArgument.label.OuterBarsSafe (fun x=>x≠Label.atom 4) ∧
    currentArgument.label.letters=[.atom 3,.over (.atom 4),.atom 5,.under (.atom 4),.atom 6] ∧
    PrerequisiteChain target [] [[.fn]] ∧PrerequisiteChain target [.arg] [[.arg,.fn]] :=
  ⟨initial,closed,actualHistory,actual_auxiliary,actual_marked,actual_overlap_word,
    actual_source_endpoint_chain,actual_target_endpoint_chain⟩

theorem literal_five_writing_blocks
    {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
    {g : Net signature N B W} {root : B}
    (selection : SourceEdgeSelection (initLabels source.erase) g root) (physical : BetaEdge g) :
    interpretReadLetters selection.atomWord physical.principal physical.reverseRoute true
      currentArgument.label.letters=
      selection.atomWord 3++physical.principal++selection.atomWord 5++physical.reverseRoute++selection.atomWord 6 := by
  rw [actual_overlap_word]
  simp only [interpretReadLetters,List.flatMap_cons,List.flatMap_nil,orientPhysical,if_true,
    Letter.sourceWord,List.append_nil,List.append_assoc]

theorem literal_five_reverse_blocks
    {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
    {g : Net signature N B W} {root : B}
    (selection : SourceEdgeSelection (initLabels source.erase) g root) (physical : BetaEdge g) :
    interpretReadLetters selection.atomWord physical.principal physical.reverseRoute false
      (currentArgument.label.readLetters false)=
      reverseEdges (selection.atomWord 6)++reverseEdges physical.reverseRoute++
      reverseEdges (selection.atomWord 5)++reverseEdges physical.principal++reverseEdges (selection.atomWord 3) := by
  change interpretReadLetters selection.atomWord physical.principal physical.reverseRoute false
    [.atom 6,.under (.atom 4),.atom 5,.over (.atom 4),.atom 3]=_
  simp only [interpretReadLetters,List.flatMap_cons,List.flatMap_nil,orientPhysical,Bool.false_eq_true,if_false,
    Letter.sourceWord,List.append_nil,List.append_assoc]

-- The actual lexical VAR-FIRST geometry remains a negative D017 boundary:
-- its parent has no successful chain; it is not a positive Aux-high fixture.

#print axioms actual_marked_app_whole
#print axioms actual_marked_app_reverse_whole
#print axioms real_marked_app_domain
#print axioms literal_five_writing_blocks
#print axioms literal_five_reverse_blocks
#print axioms target_iso
#print axioms PairedAuxWritingFirstAtomsChecks.App.source_iso
#print axioms PairedAuxWritingFirstAtomsChecks.Var.no_source_iso
end Lamping.Checks.MarkedAuxiliaryEvaluationsChecks
