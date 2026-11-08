import Lamping.Lambda.PrerequisiteIncidencePaths
import Lamping.Checks.DirectedReadingDecomposition
import Lamping.Checks.WrappedSuccessfulChains
namespace Lamping.Checks.PrerequisiteIncidencePathsChecks
open Lambda Lambda.Labelled SyntaxIncidence
namespace Singleton
open DirectedReadingDecompositionChecks
def appVertex : ProperPosition target := ⟨[],Or.inl ⟨_,_,_,rfl⟩⟩
def lamVertex : ProperPosition target := ⟨[.fn],Or.inr ⟨_,_,rfl⟩⟩
theorem actual_app_geometry : ∃first : ProperPosition target,∃vertices,
    first=appVertex ∧ProperIncidenceWalk target first [[.fn]] vertices ∧
    vertices.Nodup ∧vertices.length=2 := by
  obtain ⟨first,vertices,endpoint,walk,nodup,_⟩ := successful_function.incidence_path
  have equal : first=appVertex := Option.some.inj (Target.unique endpoint (Or.inl rfl))
  exact ⟨first,vertices,equal,walk,nodup,walk.length⟩
theorem actual_lambda_geometry : ∃first : ProperPosition target,∃vertices,
    first=lamVertex ∧ProperIncidenceWalk target first [[.fn]] vertices ∧
    vertices.Nodup ∧vertices.length=2 := by
  obtain ⟨first,vertices,endpoint,walk,nodup,_⟩ := successful_context.incidence_path
  have equal : first=lamVertex := Option.some.inj (Target.unique endpoint (Or.inl rfl))
  exact ⟨first,vertices,equal,walk,nodup,walk.length⟩
theorem actual_forward_walk : ProperIncidenceWalk target appVertex [[.fn]] [appVertex,lamVertex] :=
  .cons (Or.inl ⟨⟨.fn,_,_,rfl,rfl,.fn⟩,Or.inl rfl⟩) (.nil _)
theorem actual_reverse_walk : ProperIncidenceWalk target lamVertex [[.fn]] [lamVertex,appVertex] :=
  .cons (Or.inr ⟨Or.inl rfl,⟨.fn,_,_,rfl,rfl,.fn⟩⟩) (.nil _)
theorem same_edge_different_start : appVertex≠lamVertex := by
  intro equal
  have paths := congrArg Subtype.val equal
  cases paths
theorem one_initial_actual_history : INIT source ∧History [[.fn]] source target := ⟨initial,history⟩
end Singleton

namespace BinderJump
open WrappedSuccessfulChains
def variableChain : PrerequisiteChain current bodyFunction rootEdges :=
  .var (parent:=[.fn]) (rest:=[.fn]) rfl rfl rfl rfl (.redex_lam (p:=[]) rfl)
theorem actual_variable_compression : ∃first : ProperPosition current,∃vertices,
    first.val=[.fn] ∧first.val≠bodyFunction ∧
    ProperIncidenceWalk current first rootEdges vertices ∧vertices.Nodup ∧vertices.length=2 := by
  obtain ⟨first,vertices,endpoint,walk,nodup,_⟩ := variableChain.incidence_path
  let binder : ProperPosition current := ⟨[.fn],Or.inr ⟨_,_,rfl⟩⟩
  have actualTarget : Target current bodyFunction (some binder) :=
    Or.inr ⟨.atom 6,0,functionLabel,_,[.fn],rfl,rfl,rfl,rfl⟩
  have equal : first=binder := Option.some.inj (Target.unique endpoint actualTarget)
  subst first
  exact ⟨binder,vertices,rfl,by decide,walk,nodup,walk.length⟩
theorem actual_two_edge_path : ∃first : ProperPosition current,∃vertices,
    Target current bodyApp (some first) ∧ProperIncidenceWalk current first bodyEdges vertices ∧
    vertices.Nodup ∧vertices.length=3 ∧
    (∀vertex∈vertices,PrerequisiteIncident current bodyEdges vertex.val) := by
  obtain ⟨first,vertices,endpoint,walk,nodup,incident⟩ := body_chain.incidence_path
  exact ⟨first,vertices,endpoint,walk,nodup,walk.length,incident⟩
theorem actual_terminal_structure : ∃before last,bodyEdges=before++[last] ∧
    PrerequisiteRedexEdge current last ∧∀edge∈before,¬PrerequisiteRedexEdge current edge :=
  body_chain.redex_only_last
end BinderJump

#print axioms PrerequisiteChain.incidence_path
#print axioms ProperIncidenceWalk.length
#print axioms ProperIncidenceWalk.covers_incident
#print axioms Singleton.actual_app_geometry
#print axioms Singleton.actual_lambda_geometry
#print axioms Singleton.actual_forward_walk
#print axioms Singleton.actual_reverse_walk
#print axioms Singleton.same_edge_different_start
#print axioms Singleton.one_initial_actual_history
#print axioms BinderJump.actual_variable_compression
#print axioms BinderJump.actual_two_edge_path
#print axioms BinderJump.actual_terminal_structure
end Lamping.Checks.PrerequisiteIncidencePathsChecks
