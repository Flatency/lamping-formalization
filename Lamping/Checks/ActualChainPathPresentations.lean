import Lamping.Lamping.ActualChainPathPresentations
import Lamping.Checks.PrerequisiteIncidencePaths
namespace Lamping.Checks.ActualChainPathPresentationsChecks
open Graph Lambda Lambda.Labelled AG SyntaxIncidence
namespace Singleton
open DirectedReadingDecompositionChecks
abbrev closedTarget : Closed target.erase := history.closed closed
noncomputable def appPath := actual_chain_incidence_presentation closedTarget successful_function
noncomputable def lamPath := actual_chain_incidence_presentation closedTarget successful_context
theorem actual_app_first : appPath.first.val=[] := by
  let app : ProperPosition target := PrerequisiteIncidencePathsChecks.Singleton.appVertex
  have equal : appPath.first=app := Option.some.inj (Target.unique appPath.endpoint (Or.inl rfl))
  exact congrArg Subtype.val equal
theorem actual_lam_first : lamPath.first.val=[.fn] := by
  let lam : ProperPosition target := PrerequisiteIncidencePathsChecks.Singleton.lamVertex
  have equal : lamPath.first=lam := Option.some.inj (Target.unique lamPath.endpoint (Or.inl rfl))
  exact congrArg Subtype.val equal
theorem actual_same_literal_edge :
    (appPath.presentation.edges ⟨0,by decide⟩).val.val=[.fn] ∧
    (lamPath.presentation.edges ⟨0,by decide⟩).val.val=[.fn] := ⟨appPath.edge_at ⟨0,by decide⟩,lamPath.edge_at ⟨0,by decide⟩⟩
theorem actual_slot_dichotomy :
    (∀k,(IndexedSimpleIncidencePath.mappedSlot appPath.presentation lamPath.presentation (ChainIncidenceIso.refl _) k).val=k.val) ∨
    (∀k,(IndexedSimpleIncidencePath.mappedSlot appPath.presentation lamPath.presentation (ChainIncidenceIso.refl _) k).val=1-k.val) :=
  appPath.presentation.iso_order_or_reverse lamPath.presentation (ChainIncidenceIso.refl _)
theorem actual_forced_reverse :
    ∀k,(IndexedSimpleIncidencePath.mappedSlot appPath.presentation lamPath.presentation (ChainIncidenceIso.refl _) k).val=1-k.val := by
  rcases actual_slot_dichotomy with same | reverse
  · have zero : IndexedSimpleIncidencePath.mappedSlot appPath.presentation lamPath.presentation
        (ChainIncidenceIso.refl _) 0=0 := Fin.ext (same 0)
    have vertices := congrArg lamPath.presentation.vertices zero
    simp only [IndexedSimpleIncidencePath.mappedSlot,lamPath.presentation.vertices.right_inv,
      ChainIncidenceIso.refl,Bij.refl] at vertices
    have originalVertices := congrArg Subtype.val vertices
    simp only [id_eq] at originalVertices
    rw [appPath.vertex_zero,lamPath.vertex_zero] at originalVertices
    have positions := congrArg Subtype.val (Option.some.inj originalVertices)
    rw [actual_app_first,actual_lam_first] at positions
    cases positions
  · exact reverse
theorem actual_same_initial : INIT source ∧History [[.fn]] source target := ⟨initial,history⟩
end Singleton

namespace VariableJump
open WrappedSuccessfulChains
noncomputable def bodyPath := actual_chain_incidence_presentation targetClosed body_chain
noncomputable def jumpPath := actual_chain_incidence_presentation targetClosed PrerequisiteIncidencePathsChecks.BinderJump.variableChain
theorem actual_two_literal_edges : ∀k,
    (bodyPath.presentation.edges k).val.val=bodyEdges.get k := bodyPath.edge_at
theorem actual_three_distinct_vertices : bodyPath.vertices.Nodup ∧bodyPath.vertices.length=3 :=
  ⟨bodyPath.nodup,bodyPath.walk.length⟩
theorem actual_binder_start : jumpPath.first.val=[.fn] ∧jumpPath.first.val≠bodyFunction := by
  let binder : ProperPosition current := ⟨[.fn],Or.inr ⟨_,_,rfl⟩⟩
  have endpoint : Target current bodyFunction (some binder) :=
    Or.inr ⟨.atom 6,0,functionLabel,_,[.fn],rfl,rfl,rfl,rfl⟩
  have equal : jumpPath.first=binder := Option.some.inj (Target.unique jumpPath.endpoint endpoint)
  exact ⟨congrArg Subtype.val equal,by rw [congrArg Subtype.val equal];decide⟩
end VariableJump

#print axioms actual_chain_incidence_presentation
#print axioms ActualChainPathPresentation.vertex_zero
#print axioms Singleton.actual_app_first
#print axioms Singleton.actual_lam_first
#print axioms Singleton.actual_same_literal_edge
#print axioms Singleton.actual_forced_reverse
#print axioms Singleton.actual_same_initial
#print axioms VariableJump.actual_two_literal_edges
#print axioms VariableJump.actual_three_distinct_vertices
#print axioms VariableJump.actual_binder_start
end Lamping.Checks.ActualChainPathPresentationsChecks
