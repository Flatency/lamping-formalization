import Lamping.Lamping.SimpleIncidencePathIso
import Lamping.Lamping.ChainSyntaxIncidence
import Lamping.Checks.PrerequisiteIncidencePaths
namespace Lamping.Checks.SimpleIncidencePathIsoChecks
open Graph Lambda Lambda.Labelled AG SyntaxIncidence
open DirectedReadingDecompositionChecks
abbrev closedTarget : Closed target.erase := history.closed closed
noncomputable abbrev G := syntaxIncidenceGraph target closedTarget
def actualEdge : Edge target := ⟨[.fn],by rw [←LTerm.erase_subterm];rfl⟩
abbrev app : Vertex target := some PrerequisiteIncidencePathsChecks.Singleton.appVertex
abbrev lam : Vertex target := some PrerequisiteIncidencePathsChecks.Singleton.lamVertex
theorem distinct : app≠lam := by
  intro equal
  exact PrerequisiteIncidencePathsChecks.Singleton.same_edge_different_start (Option.some.inj equal)
theorem actualSource : G.source actualEdge=app :=
  source_eq_of_spec target actualEdge ⟨.fn,_,_,rfl,rfl,.fn⟩
theorem actualTarget : G.target actualEdge=lam :=
  target_eq_of_spec target closedTarget actualEdge (Or.inl rfl)
noncomputable def forwardPath : IndexedSimpleIncidencePath (G.induced (fun e=>e=actualEdge)) 1 :=
  .singleton (g:=G) actualEdge app lam distinct (Or.inl ⟨actualSource,actualTarget⟩)
noncomputable def backwardPath : IndexedSimpleIncidencePath (G.induced (fun e=>e=actualEdge)) 1 :=
  .singleton (g:=G) actualEdge lam app distinct.symm (Or.inr ⟨actualTarget,actualSource⟩)
theorem actual_slot_dichotomy :
    (∀k,(IndexedSimpleIncidencePath.mappedSlot forwardPath backwardPath (ChainIncidenceIso.refl _) k).val=k.val) ∨
    (∀k,(IndexedSimpleIncidencePath.mappedSlot forwardPath backwardPath (ChainIncidenceIso.refl _) k).val=1-k.val) :=
  forwardPath.iso_order_or_reverse backwardPath (ChainIncidenceIso.refl _)

theorem actual_reversed_start :
    (IndexedSimpleIncidencePath.mappedSlot forwardPath backwardPath (ChainIncidenceIso.refl _) 0).val=1 := by
  classical
  simp [IndexedSimpleIncidencePath.mappedSlot,forwardPath,backwardPath,
    IndexedSimpleIncidencePath.singleton,ChainIncidenceIso.refl,Bij.refl]
  rw [if_neg distinct]
  rfl

theorem actual_slot_reversal :
    ∀k,(IndexedSimpleIncidencePath.mappedSlot forwardPath backwardPath (ChainIncidenceIso.refl _) k).val=1-k.val := by
  rcases actual_slot_dichotomy with same | reverse
  · have zero:=same (0 : Fin 2)
    rw [actual_reversed_start] at zero
    cases zero
  · exact reverse

theorem selected_actual_singleton (edge : Edge target) : edge.val∈[[.fn]] ↔edge=actualEdge := by
  constructor
  · intro member;exact Subtype.ext (List.mem_singleton.mp member)
  · intro equal;subst edge;exact List.mem_singleton_self _

theorem actual_same_initial_successful_chains : INIT source ∧History [[.fn]] source target ∧
    PrerequisiteChain target [] [[.fn]] ∧PrerequisiteChain target [.fn] [[.fn]] :=
  ⟨initial,history,successful_function,successful_context⟩

#print axioms finite_unit_path_order_or_reverse
#print axioms finite_path_slot_order_or_reverse
#print axioms IndexedSimpleIncidencePath.mapped_slot_adjacent
#print axioms IndexedSimpleIncidencePath.iso_order_or_reverse
#print axioms actual_slot_dichotomy
#print axioms actual_reversed_start
#print axioms actual_slot_reversal
#print axioms selected_actual_singleton
#print axioms actual_same_initial_successful_chains
end Lamping.Checks.SimpleIncidencePathIsoChecks
