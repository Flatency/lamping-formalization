import Lamping.Lamping.PairedAuxWritingFirstAtoms
import Lamping.Checks.AuxWritingFirstAtomOrigin
namespace Lamping.Checks.PairedAuxWritingFirstAtomsChecks
open Graph Lambda Lambda.Labelled AG SyntaxIncidence InteriorSourceBlock
namespace App
open NodeLabelSuffixOriginsChecks AuxiliaryNodeHistoryOriginsChecks
abbrev F : List Path:=AuxWritingFirstAtomOriginChecks.App.F
def edge : SyntaxIncidence.Edge target:=⟨[.arg],by rw [←LTerm.erase_subterm,actual_lookup];rfl⟩
theorem selected (name : Path) (member : name∈F) : source.degreeAt name=some (.atom 4) := by
  have eq:=List.mem_singleton.mp member;subst name;rfl

theorem source_iso : SuccessfulEndpointIso target (actualHistory.closed closed)
    (SyntaxIncidence.source target edge) (SyntaxIncidence.source target edge) := by
  rw [SyntaxIncidence.source_eq_of_spec target edge target_source_endpoint]
  exact .refl_of_chain actual_source_endpoint_chain

/-- Actual INIT/OLD/marked APP inputs directly instantiate the new high.
Matching and SOURCEAux are honest conditional graph data, not a fake carrier. -/
theorem actual_first_pair
    {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
    {g : Net signature N B W} {root : B}
    (matching : Matches g root source.erase)
    (sourceSelection : OccurrenceFragmentSelection source g root)
    (sourceAux : AuxiliarySeparation closed sourceSelection)
    (selection : SourceEdgeSelection (initLabels source.erase) g root) :
    selection.atomWord 3=selection.atomWord 3 :=
  paired_aux_writing_first_atom_words initial (.nil source)
    AuxWritingFirstAtomOriginChecks.App.old actualHistory AuxWritingFirstAtomOriginChecks.App.localHistory
    selected (initial.outerBarsSafe _) closed edge edge actual_lookup actual_lookup
    actual_auxiliary actual_auxiliary rfl actual_lookup actual_lookup
    (by rfl : currentArgument.label.letters=[.atom 3,bar true (.atom 4)]++[.atom 5,.under (.atom 4),.atom 6])
    (by rfl : currentArgument.label.letters=[.atom 3,bar true (.atom 4)]++[.atom 5,.under (.atom 4),.atom 6])
    source_iso matching sourceSelection sourceAux selection

theorem actual_history_and_both_endpoint_chains : INIT source ∧Closed source.erase ∧
    History [[.arg]] source target ∧PrerequisiteChain target [] [[.fn]] ∧
      PrerequisiteChain target [.arg] [[.arg,.fn]] :=
  ⟨initial,closed,actualHistory,actual_source_endpoint_chain,actual_target_endpoint_chain⟩

theorem source_hom_boundary :
    ¬BetaVertexPreimage (.var (.atom 5) 0) argumentTerm [.arg] source target
      (some currentOuter) (some oldInner) := no_created_source_incidence_map
end App
namespace Var
open DirectedReadingDecompositionChecks
theorem parent_no_chain : NoPrerequisite cTarget [.body] := by
  apply (no_prerequisite_application_iff (current:=cTarget) (p:=[.body]) rfl).mpr
  exact ⟨(by intro _ _ impossible;cases impossible),
    (no_prerequisite_variable_iff (current:=cTarget) (leaf:=[.body,.fn]) (parent:=[]) (rest:=[.fn])
      rfl rfl rfl rfl).mpr (no_prerequisite_root_lambda rfl)⟩

def edge : SyntaxIncidence.Edge cTarget:=⟨[.body,.arg],by rw [←LTerm.erase_subterm,AuxWritingFirstAtomOriginChecks.Var.lookup];rfl⟩
theorem no_source_iso : ¬SuccessfulEndpointIso cTarget
    (AuxWritingFirstAtomOriginChecks.Var.labels.closed AuxWritingFirstAtomOriginChecks.Var.closed)
    (SyntaxIncidence.source cTarget edge) (SyntaxIncidence.source cTarget edge) := by
  have spec : Source cTarget edge.val (some AuxWritingFirstAtomOriginChecks.Var.parent) :=
    ⟨.arg,_,_,rfl,rfl,.arg⟩
  rw [SyntaxIncidence.source_eq_of_spec cTarget edge spec]
  intro relation
  obtain ⟨es,chain⟩:=relation.left_available
  exact parent_no_chain ⟨es,chain⟩

-- The positive lexical/binder origin is retained separately from failed availability.
def actual_var_geometry := AuxWritingFirstAtomOriginChecks.Var.actual_var_binder_first
end Var
#print axioms App.source_iso
#print axioms App.actual_first_pair
#print axioms App.actual_history_and_both_endpoint_chains
#print axioms App.source_hom_boundary
#print axioms Var.parent_no_chain
#print axioms Var.no_source_iso
#print axioms Var.actual_var_geometry
end Lamping.Checks.PairedAuxWritingFirstAtomsChecks
