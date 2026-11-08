import Lamping.Lamping.ActionCopiedBindingComparison
import Lamping.Lamping.ActionCopiedBindingFragmentCuts
import Lamping.Lamping.ActionCopiedLambdaBodyPrefixes
import Lamping.Lamping.ActionKeptFragmentComparison
import Lamping.Lamping.PhysicalCorridorPresentation
import Lamping.Lamping.GraphTraceSoundness
import Lamping.Checks.Soundness
import Lamping.Lamping.ActionFragmentCuts
import Lamping.Lamping.ActionLambdaCanonicalAccess
import Lamping.Lamping.ActionPendingLambdaPadding
import Lamping.Lamping.ActionPendingCanonicalAccess
import Lamping.Lamping.ActionPendingCanonicalTrim
import Lamping.Lamping.ActionCanonicalOutsideCut
import Lamping.Lamping.UnaryCanonicalComparison
import Lamping.Lamping.UnaryCanonicalUniqueness
import Lamping.Lambda.PrerequisiteUndefined
import Lamping.Lamping.ActionPendingLambdaBranches
import Lamping.Lamping.FragmentWriterSuffix
import Lamping.Lamping.ActionPrerequisiteCopyBranches
import Lamping.Lamping.ActionPendingFunctionBranches
import Lamping.Lamping.ActionParentFunctionBranches
import Lamping.Lamping.ActionFunctionBranches
import Lamping.Lamping.ActionEmptyWordPassages
import Lamping.Lamping.ActionCanonicalUniqueness
import Lamping.Lamping.ActionPassiveReplay
import Lamping.Lamping.CancellationFragmentTransport
import Lamping.Lamping.CancellationCanonicalComparison
import Lamping.Lamping.FamilyRepresentation
import Lamping.Lamping.CancellationCanonicalResidual
import Lamping.Lamping.PrincipalSiteRealization
import Lamping.Lamping.CancellationCanonicalPrefixes
import Lamping.Lamping.EndpointPrerequisites
import Lamping.Lamping.ChainIncidenceWalk
import Lamping.Lambda.PrerequisiteOrder
import Lamping.Lamping.ChainRepresentation
import Lamping.Lamping.ChainFragmentUniqueness
import Lamping.Lamping.ChainSyntaxIncidence
import Lamping.Lamping.OccurrencePhysicalNodes
import Lamping.Lamping.InitialMatching

namespace Lamping.Checks.FamilyRepresentation
open Lambda Lambda.Labelled

/-- Repeated labels deliberately do not identify syntax occurrences. -/
def identity : LTerm := .lam (.atom 1) (.var (.atom 1) 0)
def term : LTerm := .app (.atom 0) identity identity

theorem actual_closed : Closed term.erase := by change (0<1) ∧ 0<1; decide

theorem function_chain : PrerequisiteChain term [.fn] [[.fn]] :=
  .redex_lam (p:=[]) rfl

theorem argument_chain : PrerequisiteChain term [.arg] [[.arg],[.fn]] :=
  .lam (parent:=[]) (step:=.arg) rfl (by decide) (.redex_app rfl)

theorem argument_variable_chain :
    PrerequisiteChain term [.arg,.body] [[.arg],[.fn]] :=
  .var rfl (parent:=[.arg]) rfl (rest:=[]) rfl rfl argument_chain

theorem argument_chain_has_context_edge :
    [.arg]∈([[.arg],[.fn]] : List Path) ∧
    PrerequisiteEligible term [.arg] :=
  ⟨by simp, argument_chain.eligible (by simp)⟩

theorem argument_chain_stops_at_actual_root_redex :
    ([[.arg],[.fn]] : List Path).getLast?=some [.fn] ∧
    PrerequisiteRedexEdge term [.fn] :=
  ⟨rfl,[],.atom 0,.atom 1,_,identity,rfl,rfl⟩

theorem no_successful_empty_chain (p : Path) : ¬PrerequisiteChain term p [] := by
  intro chain
  exact chain.nonempty rfl

theorem same_label_is_not_same_binder_occurrence :
    term.subterm [.fn]=term.subterm [.arg] ∧
    ¬∃ tail,([.arg,.body] : Path)=[]++(.body::tail) := by
  constructor
  · rfl
  · rintro ⟨tail,wrong⟩
    cases wrong

end Lamping.Checks.FamilyRepresentation

#print axioms Lamping.Checks.FamilyRepresentation.argument_chain
#print axioms Lamping.Checks.FamilyRepresentation.argument_variable_chain
#print axioms Lamping.Checks.FamilyRepresentation.argument_chain_stops_at_actual_root_redex
#print axioms Lamping.Lambda.Labelled.PrerequisiteChain.last_redex
namespace Lamping.Checks.FamilyRepresentation
open Lambda Lambda.Labelled

theorem argument_chain_has_only_terminal_redex :
    ∃ before last,([[.arg],[.fn]] : List Path)=before++[last] ∧
      PrerequisiteRedexEdge term last ∧
      ∀ edge∈before,¬PrerequisiteRedexEdge term edge :=
  argument_chain.redex_only_last

theorem argument_context_is_not_redex : ¬PrerequisiteRedexEdge term [.arg] := by
  rintro ⟨parent,a,l,b,arg,wrong,_⟩
  have reversed := congrArg List.reverse wrong
  cases parent with
  | nil => cases wrong
  | cons first rest =>
    have lengths := congrArg List.length wrong
    simp only [List.length_append,List.length_cons,List.length_nil] at lengths
    omega

end Lamping.Checks.FamilyRepresentation
#print axioms Lamping.Lambda.Labelled.PrerequisiteChain.redex_only_last
#print axioms Lamping.Checks.FamilyRepresentation.argument_chain_has_only_terminal_redex
namespace Lamping.Checks.FamilyRepresentation
open Lambda Lambda.Labelled

theorem every_argument_chain_is_literal (other : PrerequisiteChain term [.arg] edges) :
    edges=([[.arg],[.fn]] : List Path) := other.unique argument_chain

theorem root_identity_has_no_chain (edges : List Path) :
    ¬PrerequisiteChain identity [] edges := by
  intro chain
  rcases chain.lambda_cases rfl with ⟨parent,_,_,wrong,_,_⟩ |
    ⟨parent,step,tail,wrong,_,_,_⟩
  all_goals
    have lengths := congrArg List.length wrong
    simp only [List.length_append,List.length_cons,List.length_nil] at lengths
    omega

end Lamping.Checks.FamilyRepresentation
#print axioms Lamping.Lambda.Labelled.PrerequisiteChain.unique
#print axioms Lamping.Checks.FamilyRepresentation.root_identity_has_no_chain
namespace Lamping.Checks.FamilyRepresentation
open Lambda Lambda.Labelled

theorem actual_argument_dependency : PrerequisiteDependency term [.arg] [] :=
  .lam (parent:=[]) (step:=.arg) rfl rfl (by decide)

theorem actual_variable_dependency : PrerequisiteDependency term [.arg,.body] [.arg] :=
  .var rfl rfl rfl rfl

theorem actual_strict_order :
    prerequisiteOrder term []=2 ∧prerequisiteOrder term [.arg]=3 ∧
    prerequisiteOrder term [.arg,.body]=4 := ⟨rfl,rfl,rfl⟩

theorem actual_argument_uniform_bound :
    ([[.arg],[.fn]] : List Path).length≤prerequisiteOrder term [.arg]+1 :=
  argument_chain.length_le

theorem no_dependency_cycle (p : Path) : ¬PrerequisiteDependency term p p := by
  intro dependency
  have smaller := dependency.order_lt
  omega

theorem actual_argument_not_auxiliary : ¬AuxiliaryAt term [.arg] :=
  argument_chain.not_auxiliary (by simp)

theorem actual_variable_edge_auxiliary : AuxiliaryAt term [.arg,.body] := by
  constructor
  · rintro ⟨parent,stamp,fn,arg,equal,_⟩
    have heads := congrArg List.head? (congrArg List.reverse equal)
    simp only [List.reverse_cons,List.reverse_nil,List.reverse_append,
      List.nil_append,List.cons_append,List.head?_cons] at heads
    cases heads
  · rintro ⟨stamp,body,lookup⟩
    cases lookup

end Lamping.Checks.FamilyRepresentation
#print axioms Lamping.Lambda.Labelled.prerequisiteDependency_wellFounded
#print axioms Lamping.Lambda.Labelled.PrerequisiteChain.length_le
#print axioms Lamping.Lambda.Labelled.PrerequisiteChain.not_auxiliary
#print axioms Lamping.Checks.FamilyRepresentation.actual_variable_edge_auxiliary
namespace Lamping.Checks.FamilyRepresentation
open Graph Lambda Lambda.Labelled AG

abbrev actualNet := (encode 0 term.erase).net
abbrev actualRoot : Boundary term.erase := .inl ()

def functionPosition : Position term.erase := ⟨[.fn],rfl⟩
def argumentPosition : Position term.erase := ⟨[.arg],rfl⟩
def functionVariablePosition : Position term.erase := ⟨[.fn,.body],rfl⟩
def argumentVariablePosition : Position term.erase := ⟨[.arg,.body],rfl⟩

theorem current_not_init : ¬INIT term := by
  intro initial
  have distinct := initial.2
  simp [term,identity,LTerm.labels] at distinct

theorem actual_occurrence_selection :
    Nonempty (OccurrenceFragmentSelection term actualNet actualRoot) :=
  (encode_closed_matches term.erase actual_closed 0).occurrence_fragment_selection actual_closed

theorem same_redex_canonical_but_opposite_readings
    (selection : OccurrenceFragmentSelection term actualNet actualRoot) :
    canonicalChainImage selection (.redex_app (p:=[]) rfl)=
      canonicalChainImage selection function_chain ∧
    orientedChainImage selection (PrerequisiteReading.redex_app (p:=[]) rfl)=
      [(selection functionPosition).fragment.segments] ∧
    orientedChainImage selection (PrerequisiteReading.redex_lam (p:=[]) rfl)=
      [reverseEdges (selection functionPosition).fragment.segments] :=
  ⟨rfl,rfl,rfl⟩

theorem variable_occurrence_accesses_differ
    (selection : OccurrenceFragmentSelection term actualNet actualRoot) :
    (selection functionVariablePosition).fragment.access≠
      (selection argumentVariablePosition).fragment.access := by
  intro same
  have words := congrArg (fun access : RootAccess actualNet actualRoot => accessWord actualNet access.val) same
  dsimp only at words
  rw [(selection functionVariablePosition).fragment.word,
    (selection argumentVariablePosition).fragment.word] at words
  cases words

private theorem function_variable_source
    (fragment : OccurrenceFragment term actualNet actualRoot [.fn,.body]) :
    sourceEdge fragment.environment fragment.context fragment.term=
      sourceEdge [.atom 1] (.lamBody (.atom 1)) (.var (.atom 1) 0) := by
  rcases fragment with ⟨sub,environment,context,occurrence,physical⟩
  dsimp only [term,identity] at occurrence
  cases occurrence with
  | fn occurrence =>
    cases occurrence with
    | body occurrence => cases occurrence; rfl

private theorem argument_variable_source
    (fragment : OccurrenceFragment term actualNet actualRoot [.arg,.body]) :
    sourceEdge fragment.environment fragment.context fragment.term=
      sourceEdge [.atom 1] (.lamBody (.atom 1)) (.var (.atom 1) 0) := by
  rcases fragment with ⟨sub,environment,context,occurrence,physical⟩
  dsimp only [term,identity] at occurrence
  cases occurrence with
  | arg occurrence =>
    cases occurrence with
    | body occurrence => cases occurrence; rfl

theorem repeated_source_edge_does_not_merge_accesses
    (selection : OccurrenceFragmentSelection term actualNet actualRoot) :
    sourceEdge (selection functionVariablePosition).environment
      (selection functionVariablePosition).context (selection functionVariablePosition).term=
      sourceEdge (selection argumentVariablePosition).environment
        (selection argumentVariablePosition).context (selection argumentVariablePosition).term ∧
    (selection functionVariablePosition).fragment.access≠
      (selection argumentVariablePosition).fragment.access :=
  ⟨(function_variable_source _).trans (argument_variable_source _).symm,
    variable_occurrence_accesses_differ selection⟩

end Lamping.Checks.FamilyRepresentation
#print axioms Lamping.AG.Matches.occurrence_fragment_selection
#print axioms Lamping.Checks.FamilyRepresentation.actual_occurrence_selection
#print axioms Lamping.Checks.FamilyRepresentation.same_redex_canonical_but_opposite_readings
#print axioms Lamping.Checks.FamilyRepresentation.repeated_source_edge_does_not_merge_accesses
namespace Lamping.Checks.FamilyRepresentation
open Graph Lambda Lambda.Labelled AG

theorem noninit_arbitrary_fragment_choices_agree
    (first second : OccurrenceFragmentSelection term actualNet actualRoot) :
    canonicalChainImage first argument_chain=canonicalChainImage second argument_chain ∧
    (first functionVariablePosition).fragment.segments=
      (second functionVariablePosition).fragment.segments ∧
    orientedChainImage first (PrerequisiteReading.redex_lam (p:=[]) rfl)=
      orientedChainImage second (PrerequisiteReading.redex_lam (p:=[]) rfl) := by
  have matching := encode_closed_matches term.erase actual_closed 0
  exact ⟨canonicalChainImage_choice_independent matching first second argument_chain,
    OccurrenceFragment.segments_unique matching _ _,
    orientedChainImage_choice_independent matching first second _⟩

theorem actual_selection_with_choice_independent_image :
    ∃ first : OccurrenceFragmentSelection term actualNet actualRoot,
      ∀ second : OccurrenceFragmentSelection term actualNet actualRoot,
      canonicalChainImage first argument_chain=canonicalChainImage second argument_chain := by
  obtain ⟨first⟩ := actual_occurrence_selection
  exact ⟨first,fun second=>(noninit_arbitrary_fragment_choices_agree first second).1⟩

end Lamping.Checks.FamilyRepresentation
#print axioms Lamping.AG.OccurrenceFragment.segments_unique
#print axioms Lamping.AG.canonicalChainImage_choice_independent
#print axioms Lamping.Checks.FamilyRepresentation.noninit_arbitrary_fragment_choices_agree
#print axioms Lamping.Checks.FamilyRepresentation.actual_selection_with_choice_independent_image
namespace Lamping.Checks.FamilyRepresentation
open Graph Lambda Lambda.Labelled AG

def applicationVertex : SyntaxIncidence.Vertex term :=
  some ⟨[],Or.inl ⟨.atom 0,identity,identity,rfl⟩⟩
def functionLambdaVertex : SyntaxIncidence.Vertex term :=
  some ⟨[.fn],Or.inr ⟨.atom 1,.var (.atom 1) 0,rfl⟩⟩

theorem function_edge_actual_source :
    SyntaxIncidence.source term functionPosition=applicationVertex :=
  SyntaxIncidence.source_eq_of_spec term functionPosition
    ⟨.fn,term,.appFn (.atom 0),rfl,rfl,.fn⟩

theorem function_edge_actual_target :
    SyntaxIncidence.target term actual_closed functionPosition=functionLambdaVertex :=
  SyntaxIncidence.target_eq_of_spec term actual_closed functionPosition (Or.inl rfl)

theorem actual_redex_vertices_distinct : applicationVertex≠functionLambdaVertex := by
  intro equal
  have paths := congrArg (fun vertex : SyntaxIncidence.Vertex term =>
    vertex.map (fun position=>position.val)) equal
  cases paths

theorem actual_redex_edge_subgraph_has_only_two_vertices
    (vertex : (chainSyntaxIncidence term actual_closed [[.fn]]).Vertex) :
    vertex.val=applicationVertex ∨vertex.val=functionLambdaVertex := by
  obtain ⟨edge,selected,endpoint⟩ := vertex.property
  have edgePath : edge.val=[.fn] := List.mem_singleton.mp selected
  have edgeEq : edge=functionPosition := Subtype.ext edgePath
  change vertex.val=SyntaxIncidence.source term edge ∨
    vertex.val=SyntaxIncidence.target term actual_closed edge at endpoint
  rw [edgeEq,function_edge_actual_source,function_edge_actual_target] at endpoint
  exact endpoint

theorem actual_redex_edge_subgraph_has_only_one_edge
    (edge : (chainSyntaxIncidence term actual_closed [[.fn]]).Edge) :
    edge.val=functionPosition :=
  Subtype.ext (List.mem_singleton.mp edge.property)

noncomputable def actual_same_redex_nonpointed_iso :
    ChainIncidenceIso (chainSyntaxIncidence term actual_closed [[.fn]])
      (chainSyntaxIncidence term actual_closed [[.fn]]) :=
  chainSyntaxIncidence_same_edges_iso term actual_closed
    (PrerequisiteChain.redex_app (p:=[]) rfl) function_chain

theorem actual_prerequisite_edges_do_not_collapse :
    ([[.arg],[.fn]] : List Path).Nodup ∧
    ([[.arg],[.fn]] : List Path).Nodup :=
  ⟨argument_chain.nodup,argument_variable_chain.nodup⟩

end Lamping.Checks.FamilyRepresentation
#print axioms Lamping.Lambda.Labelled.PrerequisiteChain.nodup
#print axioms Lamping.Checks.FamilyRepresentation.actual_redex_edge_subgraph_has_only_two_vertices
#print axioms Lamping.Checks.FamilyRepresentation.actual_same_redex_nonpointed_iso
namespace Lamping.Checks.FamilyRepresentation
open Graph Lambda Lambda.Labelled AG

def argumentLambdaVertex : SyntaxIncidence.Vertex term :=
  some ⟨[.arg],Or.inr ⟨.atom 1,.var (.atom 1) 0,rfl⟩⟩

theorem repeated_label_variables_have_actual_lexical_targets :
    SyntaxIncidence.target term actual_closed functionVariablePosition=functionLambdaVertex ∧
    SyntaxIncidence.target term actual_closed argumentVariablePosition=argumentLambdaVertex := by
  constructor
  · exact SyntaxIncidence.target_eq_of_spec term actual_closed functionVariablePosition
      (Or.inr ⟨.atom 1,0,.atom 1,.var (.atom 1) 0,[],rfl,rfl,rfl,rfl⟩)
  · exact SyntaxIncidence.target_eq_of_spec term actual_closed argumentVariablePosition
      (Or.inr ⟨.atom 1,0,.atom 1,.var (.atom 1) 0,[],rfl,rfl,rfl,rfl⟩)

theorem actual_physical_incidence_realization :
    ∃ fragments : OccurrenceFragmentSelection term actualNet actualRoot,
    ∃ nodes : PhysicalContextSelection term actualNet actualRoot,
    ∀ edge : SyntaxIncidence.Edge term,
      endpointVertex (fragments edge).fragment.fromEndpoint=
        some (physicalSyntaxVertex nodes (SyntaxIncidence.source term edge)) ∧
      endpointVertex (fragments edge).fragment.toEndpoint=
        some (physicalSyntaxVertex nodes (SyntaxIncidence.target term actual_closed edge)) :=
  (encode_closed_matches term.erase actual_closed 0).occurrence_incidence_realization actual_closed

theorem actual_repeated_label_variable_physical_targets
    (fragments : OccurrenceFragmentSelection term actualNet actualRoot)
    (nodes : PhysicalContextSelection term actualNet actualRoot) :
    endpointVertex (fragments functionVariablePosition).fragment.toEndpoint=
      some (physicalSyntaxVertex nodes functionLambdaVertex) ∧
    endpointVertex (fragments argumentVariablePosition).fragment.toEndpoint=
      some (physicalSyntaxVertex nodes argumentLambdaVertex) := by
  have matching := encode_closed_matches term.erase actual_closed 0
  have left := (fragments functionVariablePosition).target_vertex matching actual_closed nodes functionVariablePosition
  have right := (fragments argumentVariablePosition).target_vertex matching actual_closed nodes argumentVariablePosition
  rw [repeated_label_variables_have_actual_lexical_targets.1] at left
  rw [repeated_label_variables_have_actual_lexical_targets.2] at right
  exact ⟨left,right⟩

theorem actual_physical_node_choice_independent
    (first second : PhysicalContextSelection term actualNet actualRoot) :
    physicalSyntaxVertex first=physicalSyntaxVertex second :=
  physicalSyntaxVertex_choice_independent (encode_closed_matches term.erase actual_closed 0) first second

end Lamping.Checks.FamilyRepresentation
#print axioms Lamping.AG.OccurrenceFragment.source_vertex
#print axioms Lamping.AG.OccurrenceFragment.target_vertex
#print axioms Lamping.AG.Matches.occurrence_incidence_realization
#print axioms Lamping.Checks.FamilyRepresentation.actual_physical_incidence_realization
#print axioms Lamping.Checks.FamilyRepresentation.actual_repeated_label_variable_physical_targets
namespace Lamping.Checks.FamilyRepresentation
open Graph Lambda Lambda.Labelled AG

theorem actual_argument_incidence_from_reading :
    ∃ finish, IncidenceChase term argumentLambdaVertex [[.arg],[.fn]] [false,true] finish := by
  let reading : PrerequisiteReading term [.arg] [[.arg],[.fn]] [false,true] :=
    .lam (parent:=[]) (step:=.arg) rfl (by decide) (.redex_app rfl)
  exact reading.incidence_chase actual_closed (Or.inl rfl)

theorem actual_variable_incidence_starts_at_lexical_binder :
    SyntaxIncidence.target term actual_closed argumentVariablePosition=argumentLambdaVertex ∧
    ∃ finish,IncidenceChase term
      (SyntaxIncidence.target term actual_closed argumentVariablePosition)
      [[.arg],[.fn]] [false,true] finish := by
  refine ⟨repeated_label_variables_have_actual_lexical_targets.2,?_⟩
  let reading : PrerequisiteReading term [.arg,.body] [[.arg],[.fn]] [false,true] :=
    .var rfl (parent:=[.arg]) rfl (rest:=[]) rfl rfl
      (.lam (parent:=[]) (step:=.arg) rfl (by decide) (.redex_app rfl))
  exact reading.incidence_chase_at_position actual_closed argumentVariablePosition

/-- Both actual edges meet at the application. This is an incidence join,
not a claim of an ordinary binding-port-to-context turn. -/
theorem actual_argument_incidence_has_exact_endpoint :
    IncidenceChase term argumentLambdaVertex [[.arg],[.fn]] [false,true]
      functionLambdaVertex := by
  apply IncidenceChase.backward (show SyntaxIncidence.Target term [.arg] argumentLambdaVertex from Or.inl rfl)
    (show SyntaxIncidence.Source term [.arg] applicationVertex from
      ⟨.arg,term,.appArg (.atom 0),rfl,rfl,.arg⟩)
  exact IncidenceChase.forward
    ⟨.fn,term,.appFn (.atom 0),rfl,rfl,.fn⟩
    (show SyntaxIncidence.Target term [.fn] functionLambdaVertex from Or.inl rfl) .nil
end Lamping.Checks.FamilyRepresentation
#print axioms Lamping.Lambda.Labelled.PrerequisiteReading.incidence_chase
#print axioms Lamping.Checks.FamilyRepresentation.actual_argument_incidence_from_reading
#print axioms Lamping.Checks.FamilyRepresentation.actual_variable_incidence_starts_at_lexical_binder
#print axioms Lamping.Checks.FamilyRepresentation.actual_argument_incidence_has_exact_endpoint
namespace Lamping.Checks.FamilyRepresentation
open Graph Lambda Lambda.Labelled AG

def identityRootVertex : SyntaxIncidence.Vertex identity :=
  some ⟨[],Or.inr ⟨.atom 1,.var (.atom 1) 0,rfl⟩⟩

theorem identity_endpoint_is_undefined :
    ¬∃ es,EndpointChain identity identityRootVertex es := by
  rintro ⟨es,chain⟩
  exact root_identity_has_no_chain es chain

theorem external_and_identity_root_have_same_partial_status :
    PartialEndpointIso identity (by change 0<1; decide) none identityRootVertex ∧
      (none : SyntaxIncidence.Vertex identity)≠identityRootVertex := by
  refine ⟨Or.inl ⟨?_,identity_endpoint_is_undefined⟩,?_⟩
  · rintro ⟨es,chain⟩; exact chain
  · intro equal; cases equal

theorem argument_endpoint_has_actual_chain :
    ∃ es,EndpointChain term argumentLambdaVertex es :=
  ⟨[[.arg],[.fn]],argument_chain⟩

theorem undefined_external_not_equivalent_to_argument :
    ¬PartialEndpointIso term actual_closed none argumentLambdaVertex := by
  intro relation
  obtain ⟨es,chain⟩ := relation.available_iff.mpr argument_endpoint_has_actual_chain
  exact chain

theorem actual_argument_endpoint_status_is_reflexive :
    PartialEndpointIso term actual_closed argumentLambdaVertex argumentLambdaVertex :=
  Or.inr ⟨[[.arg],[.fn]],[[.arg],[.fn]],argument_chain,argument_chain,
    ⟨ChainIncidenceIso.refl _⟩⟩
end Lamping.Checks.FamilyRepresentation
#print axioms Lamping.AG.PartialEndpointIso.trans
#print axioms Lamping.Checks.FamilyRepresentation.external_and_identity_root_have_same_partial_status
#print axioms Lamping.Checks.FamilyRepresentation.undefined_external_not_equivalent_to_argument
#print axioms Lamping.Checks.FamilyRepresentation.actual_argument_endpoint_status_is_reflexive


namespace Lamping.Checks.CancellationPrefixFixture
open AG Graph
private def kept : Unit → Graph.Label signature := fun _=>label .lam 2
private def direct : Site (.fanCancel 1) kept (B:=Bool⊕Unit) (W:=Empty) where
 wire := {
  mate := fun e=>match e with
   | .inl ⟨.inl _,.inl _⟩ => .inl ⟨.inr (.inr ()),.inr false⟩
   | .inl ⟨.inl _,.inr b⟩ => .inl ⟨.inl (),.inr (!b)⟩
   | .inl ⟨.inr (.inl _),.inl _⟩ => .inl ⟨.inr (.inr ()),.inl ()⟩
   | .inl ⟨.inr (.inr _),.inl _⟩ => .inl ⟨.inr (.inl ()),.inl ()⟩
   | .inl ⟨.inr (.inl _),.inr b⟩ => .inr (.inl (.inl b))
   | .inl ⟨.inr (.inr _),.inr false⟩ => .inl ⟨.inl (),.inl ()⟩
   | .inl ⟨.inr (.inr _),.inr true⟩ => .inr (.inl (.inr ()))
   | .inr (.inl (.inl b)) => .inl ⟨.inr (.inl ()),.inr b⟩
   | .inr (.inl (.inr _)) => .inl ⟨.inr (.inr ()),.inr true⟩
   | .inr (.inr ⟨.inl e,_⟩) => nomatch e
   | .inr (.inr ⟨.inr e,_⟩) => nomatch e
  involutive := by
   rintro (⟨node,p⟩|((b|u)|⟨e|e,d⟩))
   · rcases node with u|(u|u)
     · cases u;cases p with | inl u=>cases u;rfl | inr b=>cases b <;> rfl
     · cases u;cases p with | inl u=>cases u;rfl | inr b=>cases b <;> rfl
     · cases u;cases p with | inl u=>cases u;rfl | inr b=>cases b <;> rfl
   · rfl
   · cases u;rfl
   · exact nomatch e
   · exact nomatch e
  fixedPointFree := by
   rintro (⟨node,p⟩|((b|u)|⟨e|e,d⟩))
   · rcases node with u|(u|u)
     · cases u;cases p with | inl u=>intro h;cases h | inr b=>cases b <;> (intro h;cases h)
     · cases u;cases p with | inl u=>intro h;cases h | inr b=>cases b <;> (intro h;cases h)
     · cases u;cases p with | inl u=>intro h;cases h | inr b=>cases b <;> (intro h;cases h)
   · intro h;cases h
   · intro h;cases h
   · exact nomatch e
   · exact nomatch e }
 principal := rfl
private def site := direct.pathSite
private abbrev entry : Endpoint site.net := .inr (.inl (.inl false))
private abbrev principal : Endpoint site.net := .inl ⟨.inr (.inl ()),.inl ()⟩
private abbrev exit : Endpoint site.net := .inl ⟨.inr (.inr ()),.inr false⟩
private def path : List (Endpoint site.net) := [entry,principal,exit]
private theorem actual_labels (a : Context) : Labelling site.net path a a := by
 have event := InitialOffsets.Event.apply_rel (.fan 1 false) a
 exact .cons (.node _ _ _ (.direct event))
   (.cons (.node _ _ _ (.inverse event)) (.single _ _))
private theorem actual_typed : accessKind site.net path=some .lam := rfl

theorem actual_fixed_route_suffix (a : Context) :
 ∃ rest,path=entry::(([principal].dropLast)++site.net.wire (.inl ⟨.inr (.inr ()),.inl ()⟩)::
   (.inl ⟨.inr (.inr ()),.inr false⟩)::rest) ∧Labelling site.net (exit::rest) a a := by
 obtain ⟨q,rest,same,split,tail⟩ := site.cancel_fixed_prefix (.fan 1) [principal] rfl rfl
   (by intro e f member;cases member) false (actual_labels a) ⟨.lam,actual_typed⟩ rfl
 have eq : false=q := eq_of_heq same
 subst q
 exact ⟨rest,split,tail⟩
end Lamping.Checks.CancellationPrefixFixture
#print axioms Lamping.AG.PathSite.cancel_fixed_prefix
#print axioms Lamping.AG.PathSite.cancel_reverse_fixed_prefix
#print axioms Lamping.Checks.CancellationPrefixFixture.actual_fixed_route_suffix

namespace Lamping.Checks.FamilyRepresentation
open Graph Lambda Lambda.Labelled AG

theorem actual_chain_comparisons (selection : OccurrenceFragmentSelection term actualNet actualRoot) :
    SameChainRepresentation selection (PrerequisiteChain.redex_app (p:=[]) rfl) function_chain ∧
      SameChainRepresentation selection argument_chain argument_variable_chain :=
  ⟨rfl,rfl⟩

theorem actual_different_chain_lengths_have_different_representations
    (selection : OccurrenceFragmentSelection term actualNet actualRoot) :
    ¬SameChainRepresentation selection argument_chain function_chain := by
  intro equal
  have lengths := congrArg List.length equal
  rw [canonicalChainImage_length,canonicalChainImage_length] at lengths
  cases lengths

theorem actual_joint_representation_is_choice_independent
    (first second : OccurrenceFragmentSelection term actualNet actualRoot) :
    JointRepresentation actual_closed first ↔JointRepresentation actual_closed second :=
  JointRepresentation.choice_independent (encode_closed_matches term.erase actual_closed 0)
    actual_closed first second
end Lamping.Checks.FamilyRepresentation

namespace Lamping.Checks.CancellationPrefixFixture
open AG Graph
private abbrev cut := cutFragment site.net (pathPartition (.fanCancel 1) Empty) site.closed
private def firstCut : Endpoint cut := .inr (.inl (.inl (.inl false)))
private def lastCut : Endpoint cut := .inr (.inl (.inr (.inr false)))

theorem actual_canonical_contraction_and_reconstruction :
    ∃ fronts : (Schema.fanCancel 1).Frontier → List (Endpoint site.net),
      (∀ a : Context,∃ es,Labelling site.reduce es a a ∧
        CanonicalCancellationResidual site fronts es path ∧CancellationResidual site es path) ∧
      ∀ (es : List (Endpoint site.reduce)) (left right : List (Endpoint site.net)),
        CanonicalCancellationResidual site fronts es left →
        CanonicalCancellationResidual site fronts es right →left=right := by
  obtain ⟨fronts,contract⟩ := site.cancellation_canonical_source_contraction (.fan 1)
  refine ⟨fronts,?_,?_⟩
  · intro a
    obtain ⟨es,labels,residual,_head,_last⟩ :=
      contract (actual_labels a) ⟨.lam,actual_typed⟩ firstCut lastCut rfl rfl
    exact ⟨es,labels,residual,residual.erase site (.fan 1)⟩
  · intro es left right first second
    exact CanonicalCancellationResidual.source_unique site (.fan 1) first second
end Lamping.Checks.CancellationPrefixFixture
#print axioms Lamping.AG.JointRepresentation.choice_independent
#print axioms Lamping.Checks.FamilyRepresentation.actual_chain_comparisons
#print axioms Lamping.Checks.FamilyRepresentation.actual_different_chain_lengths_have_different_representations
#print axioms Lamping.AG.PathSite.cancellation_canonical_source_contraction
#print axioms Lamping.AG.CanonicalCancellationResidual.source_unique
#print axioms Lamping.Checks.CancellationPrefixFixture.actual_canonical_contraction_and_reconstruction
namespace Lamping.Checks.CancellationPrefixFixture
open AG Graph

theorem actual_canonical_contraction_shares_principal :
    ∃ principal : SiteActionPrincipal site,∀ a : Context,
      ∃ es,Labelling site.reduce es a a ∧CanonicalCancellationResidual site
        (site.cancellation_canonical_fronts principal.edges) es path := by
  obtain ⟨principal,contract⟩ := site.cancellation_canonical_source_contraction_with_routes (.fan 1)
  refine ⟨principal,?_⟩
  intro a
  obtain ⟨es,labels,residual,_head,_last⟩ :=
    contract (actual_labels a) ⟨.lam,actual_typed⟩ firstCut lastCut rfl rfl
  exact ⟨es,labels,residual⟩
end Lamping.Checks.CancellationPrefixFixture
#print axioms Lamping.AG.PathSite.cancellation_canonical_source_contraction_with_routes
#print axioms Lamping.Checks.CancellationPrefixFixture.actual_canonical_contraction_shares_principal
namespace Lamping.Checks.CancellationPrefixFixture
open AG Graph
/-- Public geometric reuse of the already checked literal fan1/kept-lambda2 site. -/
abbrev geometrySite := site

def geometryPrincipal : SiteActionPrincipal geometrySite where
  edges := [principal]
  first := rfl
  last := rfl
  transparent := by intro e f member;cases member
end Lamping.Checks.CancellationPrefixFixture
namespace Lamping.Checks.CancellationPrefixFixture
open AG Graph

theorem actual_one_canonical_target_for_all_assignments :
    ∃ principal : SiteActionPrincipal site,∃ es,
      CanonicalCancellationResidual site (site.cancellation_canonical_fronts principal.edges) es path ∧
      ∀ a : Context,Labelling site.reduce es a a := by
  obtain ⟨principal,contract⟩ := actual_canonical_contraction_shares_principal
  obtain ⟨es,_labels,residual⟩ := contract Context.empty
  refine ⟨principal,es,residual,?_⟩
  intro a
  obtain ⟨again,labels,againResidual⟩ := contract a
  have same := CanonicalCancellationResidual.target_unique site (.fan 1) principal residual againResidual
  rw [same]
  exact labels
end Lamping.Checks.CancellationPrefixFixture
#print axioms Lamping.AG.CanonicalWireResidual.target_unique
#print axioms Lamping.AG.CanonicalCancellationResidual.target_unique
#print axioms Lamping.AG.CanonicalCancellationResidual.equality_iff
#print axioms Lamping.Checks.CancellationPrefixFixture.actual_one_canonical_target_for_all_assignments
namespace Lamping.Checks.CancellationPrefixFixture
open AG Graph Lambda Lambda.Labelled
private def rootSyntax : LTerm := .lam (.atom 0) (.var (.atom 1) 0)
private def actualAccess : RootAccess site.net (.inl false) :=
  ⟨path,⟨⟨⟨Context.empty,Context.empty,actual_labels Context.empty⟩,
    .node (.inr (.inl ())) (.inr false) (.inl ()) rfl rfl True.intro
      (.node (.inr (.inr ())) (.inl ()) (.inr false) rfl rfl True.intro (.single _))⟩,
    rfl,⟨.lam,actual_typed⟩⟩⟩

private def actualRootFragment : SourceEdgeFragment rootSyntax site.net (.inl false)
    (sourceEdge [] .external rootSyntax) [] where
  access := actualAccess
  word := rfl
  occurrence := ⟨[],.external,rootSyntax,.nil,rfl⟩
  before := []
  segments := path
  fromEndpoint := entry
  toEndpoint := .inl ⟨.inl (),.inl ()⟩
  fromRealizes := .external
  toRealizes := .lamContext (p:=[]) rfl actualAccess rfl rfl HEq.rfl rfl
  literal := rfl
  start := rfl
  finish := rfl
  forward := actualAccess.property.1.2
  emptyWord := rfl
  assignments := fun a _b labels=>⟨a,Or.inl ⟨rfl,rfl⟩,labels⟩

/-- The automatic fragment contract consumes real rooted/SPR data crossing
both controls. This does not supply full Matches for this fixture graph. -/
theorem actual_root_fragment_automatic_contraction :
    ∃ principal : SiteActionPrincipal site,∀ a : Context,
      ∃ (middle : Context) (first terminal : Endpoint cut) (es : List (Endpoint site.reduce)),
        actualRootFragment.fromEndpoint=site.outsideEnd first ∧
        actualRootFragment.toEndpoint=site.outsideEnd terminal ∧
        (actualRootFragment.before=[] ∧middle=a ∨
          Labelling site.net actualRootFragment.before a middle) ∧
        Labelling site.reduce es middle a ∧
        CanonicalCancellationResidual site (site.cancellation_canonical_fronts principal.edges)
          es actualRootFragment.segments ∧
        es.head?=some (plugLeft cut (Schema.fanCancel 1).right.net first) ∧
        es.getLast?=some (site.reduce.wire (plugLeft cut (Schema.fanCancel 1).right.net terminal)) := by
  obtain ⟨principal,contract⟩ := site.cancellation_fragment_contract_actual (.fan 1)
  exact ⟨principal,fun a=>contract actualRootFragment (actual_labels a)⟩
end Lamping.Checks.CancellationPrefixFixture
#print axioms Lamping.AG.PathSite.cancellation_realized_outside
#print axioms Lamping.AG.PathSite.cancellation_canonical_root_accesses
#print axioms Lamping.AG.PathSite.cancellation_occurrence_fragments
#print axioms Lamping.AG.PathSite.cancellation_occurrence_equality
#print axioms Lamping.Checks.CancellationPrefixFixture.actual_root_fragment_automatic_contraction
namespace Lamping.Checks.ActionCanonicalUniqueness
open AG Graph

/-- Both distinct four-segment copies are genuine labelled paths. Each consumes
its own actual fan marker, and both reflect to the same literal app turn. -/
theorem actual_passive_copies (a : Context) :
    fanPassiveEdges (f:=.app) (i:=0) (j:=1) false false true ≠
      fanPassiveEdges (f:=.app) (i:=0) (j:=1) true false true ∧
    ∀ branch : Bool,
      Labelling (fanRight .app 0 1) (fanPassiveEdges branch false true)
        (InitialOffsets.fanAt 0 branch a) (InitialOffsets.fanAt 0 branch a) ∧
      Labelling (leftNet .fan .app 0 1)
        [.inr (.inl (.inr false)),.inl ⟨.inr (),appArg⟩]
        (InitialOffsets.fanAt 0 branch a) (InitialOffsets.fanAt 0 branch a) := by
  refine ⟨by simp [fanPassiveEdges],?_⟩
  intro branch
  have actual := fanAction_passive_replay 0 1 branch (InitialOffsets.fanAt 0 branch a) a
    (.inverse (InitialOffsets.Event.apply_rel (.fan 0 branch) a))
  exact ⟨actual,fanAction_passive_inverse .app 0 1 branch false true _ _ actual⟩

/-- A genuine forward crossing never uses the passive split constructor;
its fixed RHS route is sufficient to recover the old route. -/
theorem crossing_reflects_same_old
    {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
    {kept : K → Label signature}
    (site : PathSite (.fanAction .app 0 1 (by decide)) kept (B:=B) (W:=W) (V:=V))
    (principal : SiteActionPrincipal site) (branch : Bool) {old}
    (other : FanCanonicalLocal site principal (fanCrossEdges branch true) old) :
    old=principal.crossing site branch true :=
  other.fixed_source_unique site (FanCanonicalLocal.cross (site:=site) (principal:=principal) branch true)
end Lamping.Checks.ActionCanonicalUniqueness
#print axioms Lamping.AG.ActionCanonicalLocal.fixed_source_unique
#print axioms Lamping.AG.ActionCanonicalBlocks.fixed_source_unique
#print axioms Lamping.AG.FanCanonicalLocal.passive_copies_split
#print axioms Lamping.Checks.ActionCanonicalUniqueness.actual_passive_copies
#print axioms Lamping.Checks.ActionCanonicalUniqueness.crossing_reflects_same_old
namespace Lamping.Checks.ActionCanonicalUniqueness
open AG Graph Lambda
/-- The split passive copies emit a real token, even though their first
boundary departure is skipped. They are not empty-word syntax fragments. -/
theorem actual_passive_copy_word (branch : Bool) :
    accessWord (fanRight .app 0 1) (fanPassiveEdges branch false true)=[.arg] := rfl

/-- The first departure is exceptional: its own token may be nonempty in
an empty-word singleton. Later-departure exclusion must keep its nonempty
prefix guard. -/
theorem actual_skipped_first_argument :
    accessWord (fanRight .app 0 1) [.inl ⟨.inl false,appArg⟩]=[] ∧
      arrivalWord (fanRight .app 0 1) (.inl ⟨.inl false,appArg⟩)=[.arg] := ⟨rfl,rfl⟩
end Lamping.Checks.ActionCanonicalUniqueness

namespace Lamping.Checks.CancellationPrefixFixture
open AG Graph
/-- This actual crossing fragment cannot hide a complete passive passage
at any ordinal, even when physical nodes repeat elsewhere. -/
theorem actual_fragment_excludes_passive (p q : Aux (Schema.fanCancel 1).passive)
    (pre post : List (Endpoint site.net)) :
    actualRootFragment.segments≠pre++site.net.wire (.inl ⟨.inr (.inr ()),.inr p⟩)::
      .inl ⟨.inr (.inr ()),.inr q⟩::post :=
  actualRootFragment.no_complete_passive site p q pre post
end Lamping.Checks.CancellationPrefixFixture
#print axioms Lamping.AG.empty_word_later_emission
#print axioms Lamping.AG.PathSite.no_passive_in_empty_word
#print axioms Lamping.AG.SourceEdgeFragment.no_complete_passive
#print axioms Lamping.Checks.ActionCanonicalUniqueness.actual_passive_copy_word
#print axioms Lamping.Checks.ActionCanonicalUniqueness.actual_skipped_first_argument
#print axioms Lamping.Checks.CancellationPrefixFixture.actual_fragment_excludes_passive
namespace Lamping.Checks.ActionFunctionBranchFixture
open AG Graph Lambda Lambda.Labelled
private def kept : Unit → Graph.Label signature := fun _=>label .lam 2
private def direct : Site (.fanAction .app 0 1 (by decide)) kept (B:=Bool⊕Unit) (W:=Empty) where
 wire := {
  mate := fun e=>match e with
   | .inl ⟨.inl _,.inl _⟩ => .inl ⟨.inr (.inl ()),.inr false⟩
   | .inl ⟨.inl _,.inr b⟩ => .inl ⟨.inl (),.inr (!b)⟩
   | .inl ⟨.inr (.inl _),.inl _⟩ => .inl ⟨.inr (.inr ()),.inl ()⟩
   | .inl ⟨.inr (.inr _),.inl _⟩ => .inl ⟨.inr (.inl ()),.inl ()⟩
   | .inl ⟨.inr (.inl _),.inr false⟩ => .inl ⟨.inl (),.inl ()⟩
   | .inl ⟨.inr (.inl _),.inr true⟩ => .inr (.inl (.inr ()))
   | .inl ⟨.inr (.inr _),.inr b⟩ => .inr (.inl (.inl b))
   | .inr (.inl (.inl b)) => .inl ⟨.inr (.inr ()),.inr b⟩
   | .inr (.inl (.inr _)) => .inl ⟨.inr (.inl ()),.inr true⟩
   | .inr (.inr ⟨.inl e,_⟩) => nomatch e
   | .inr (.inr ⟨.inr e,_⟩) => nomatch e
  involutive := by
   rintro (⟨node,p⟩|((b|u)|⟨e|e,d⟩))
   · rcases node with u|(u|u)
     · cases u;cases p with | inl u=>cases u;rfl | inr b=>cases b <;> rfl
     · cases u;cases p with | inl u=>cases u;rfl | inr b=>cases b <;> rfl
     · cases u;cases p with | inl u=>cases u;rfl | inr b=>cases b <;> rfl
   · rfl
   · cases u;rfl
   · exact nomatch e
   · exact nomatch e
  fixedPointFree := by
   rintro (⟨node,p⟩|((b|u)|⟨e|e,d⟩))
   · rcases node with u|(u|u)
     · cases u;cases p with | inl u=>intro h;cases h | inr b=>cases b <;> (intro h;cases h)
     · cases u;cases p with | inl u=>intro h;cases h | inr b=>cases b <;> (intro h;cases h)
     · cases u;cases p with | inl u=>intro h;cases h | inr b=>cases b <;> (intro h;cases h)
   · intro h;cases h
   · intro h;cases h
   · exact nomatch e
   · exact nomatch e }
 principal := rfl
private def site := direct.pathSite
private abbrev rootEnd : Endpoint site.net := .inr (.inl (.inl false))
private abbrev functionEnd : Endpoint site.net := .inl ⟨.inr (.inr ()),.inl ()⟩
private abbrev fanExit : Endpoint site.net := .inl ⟨.inr (.inl ()),.inr false⟩
private def piece : List (Endpoint site.net) := [functionEnd,fanExit]
private def wholePath : List (Endpoint site.net) := [rootEnd,functionEnd,fanExit]
private theorem piece_labels (a : Context) :
    Labelling site.net piece (InitialOffsets.fanAt 0 false a) a :=
  .cons (.node _ _ _ (.inverse (InitialOffsets.Event.apply_rel (.fan 0 false) a))) (.single _ _)
private theorem whole_labels (a : Context) :
    Labelling site.net wholePath (InitialOffsets.fanAt 0 false a) a :=
  .cons (.node _ _ _ (.direct (.appFun _))) (piece_labels a)
private def parent : RootAccess site.net (.inl false) :=
  ⟨[rootEnd],⟨⟨⟨Context.empty,Context.empty,.single _ _⟩,.single _⟩,rfl,⟨.app,rfl⟩⟩⟩
private def access : RootAccess site.net (.inl false) :=
  ⟨wholePath,⟨⟨⟨_,_,whole_labels Context.empty⟩,
    .node (.inr (.inr ())) appCtx (.inl ()) rfl rfl ⟨rfl,Or.inl rfl⟩
      (.node (.inr (.inl ())) (.inl ()) (.inr false) rfl rfl True.intro (.single _))⟩,
    rfl,⟨.lam,rfl⟩⟩⟩
private def identity : LTerm := .lam (.atom 1) (.var (.atom 2) 0)
private def currentTerm : LTerm := .app (.atom 0) identity identity
private def fragment : SourceEdgeFragment currentTerm site.net (.inl false)
    (sourceEdge [] (.appFn (.atom 0)) identity) [.fn] where
 access := access
 word := rfl
 occurrence := ⟨[],.appFn (.atom 0),identity,.fn .nil,rfl⟩
 before := [rootEnd]
 segments := piece
 fromEndpoint := functionEnd
 toEndpoint := .inl ⟨.inl (),.inl ()⟩
 fromRealizes := .departure (p:=[]) rfl (.fn) parent rfl .function rfl
 toRealizes := .lamContext (p:=[.fn]) rfl access rfl rfl HEq.rfl rfl
 literal := rfl
 start := rfl
 finish := rfl
 forward := .node (.inr (.inl ())) (.inl ()) (.inr false) rfl rfl True.intro (.single _)
 emptyWord := rfl
 assignments := by
  intro a b labels
  cases labels with
  | cons turn rest =>
    cases turn with
    | node node p q rule =>
      have equal := rule.proper_context
      subst_vars
      exact ⟨_,Or.inr (.single _ _),rest⟩

theorem actual_function_fragment_fixes_false :
    ∀ input output,Labelling site.net fragment.segments input output →
      ∃ middle,Traversal 0 (.op .fan) (.inl ()) (.inr false) input middle := by
  obtain ⟨q,uniform⟩ := fragment.function_control_branch site (Or.inl rfl) rfl
  obtain ⟨middle,turn⟩ := uniform _ _ (piece_labels Context.empty)
  have branch : q=false := turn.control_auxiliary_unique (Or.inl rfl)
    (.inverse (InitialOffsets.Event.apply_rel (.fan 0 false) Context.empty))
  subst q
  exact uniform

/-- Choosing the other fan copy is incompatible with this SAME physical
function fragment, rather than a missing context-totality assumption. -/
theorem actual_function_fragment_rejects_true :
    ¬(∀ input output,Labelling site.net fragment.segments input output →
      ∃ middle,Traversal 0 (.op .fan) (.inl ()) (.inr true) input middle) := by
  intro other
  have impossible := fragment.function_control_branch_unique site (Or.inl rfl)
    actual_function_fragment_fixes_false other
  cases impossible
end Lamping.Checks.ActionFunctionBranchFixture
#print axioms Lamping.AG.SourceEdgeFragment.function_control_branch
#print axioms Lamping.AG.SourceEdgeFragment.function_control_branch_unique
#print axioms Lamping.AG.SourceEdgeFragment.equal_function_control_branch
#print axioms Lamping.Checks.ActionFunctionBranchFixture.actual_function_fragment_fixes_false
#print axioms Lamping.Checks.ActionFunctionBranchFixture.actual_function_fragment_rejects_true
namespace Lamping.Checks.ActionFunctionBranchFixture
open AG Graph
private theorem actual_function_prefix_labels (a : Context) :
    Labelling site.net (fragment.before++[fragment.fromEndpoint])
      (InitialOffsets.fanAt 0 false a) (InitialOffsets.fanAt 0 false a) :=
  .cons (.node _ _ _ (.direct (.appFun _))) (.single _ _)

/-- Only one existing assignment is transported at a time. No arbitrary
input is asserted to pass the actual inverse reader. -/
theorem actual_same_prefix_piece (a : Context) :
    Labelling site.net fragment.segments (InitialOffsets.fanAt 0 false a) a :=
  fragment.piece_labels_at_prefix site (whole_labels a) (actual_function_prefix_labels a)

/-- The branch is recovered from true whole/prefix/reader assignments,
with arbitrary payload; no branch equality is supplied as an input. -/
theorem actual_branch_at_same_prefix :
    ∃ q : Bool,
      (∀ input output,Labelling site.net fragment.segments input output →
        ∃ middle,Traversal 0 (.op .fan) (.inl ()) (.inr q) input middle) ∧
      ∀ a : Context,∃ middle,Traversal 0 (.op .fan) (.inl ()) (.inr q)
        (InitialOffsets.fanAt 0 false a) middle ∧q=false := by
  obtain ⟨q,uniform,identify⟩ := fragment.function_branch_at_prefix site (Or.inl rfl) rfl
  refine ⟨q,uniform,?_⟩
  intro a
  obtain ⟨middle,reader⟩ := uniform _ _ (actual_same_prefix_piece a)
  exact ⟨middle,reader,identify (whole_labels a) (actual_function_prefix_labels a)
    (.inverse (InitialOffsets.Event.apply_rel (.fan 0 false) a))⟩
end Lamping.Checks.ActionFunctionBranchFixture
#print axioms Lamping.AG.SourceEdgeFragment.piece_labels_at_prefix
#print axioms Lamping.AG.SourceEdgeFragment.function_branch_at_prefix
#print axioms Lamping.AG.SourceEdgeFragment.parent_function_control_branch
#print axioms Lamping.Checks.ActionFunctionBranchFixture.actual_same_prefix_piece
#print axioms Lamping.Checks.ActionFunctionBranchFixture.actual_branch_at_same_prefix
namespace Lamping.Checks.ActionFunctionBranchFixture
open AG Graph
private abbrev right := (Schema.fanAction .app 0 1 (show 0<1 from by decide)).right.net
private abbrev fragmentCut := cutFragment (F:=Bool⊕Bool) (I:=Bool⊕(Empty×Bool)) site.net
  (pathPartition (Schema.fanAction .app 0 1 (show 0<1 from by decide)) Empty) site.closed
private def outsideRoot : Endpoint fragmentCut := .inr (.inl (.inl (.inl false)))
private def pendingInside : List (Endpoint right) :=
  [.inr (.inl (.inr false)),.inl ⟨.inr false,.inr false⟩]
private def pendingRaw : List (PlugSegment fragmentCut right) :=
  [.inl outsideRoot]++pendingInside.map Sum.inr
private def referencePending (a : Context) :
    PendingRhsBlock fragmentCut right pendingRaw (InitialOffsets.fanAt 0 false a) a where
  pre := [.inl outsideRoot]
  last := outsideRoot
  enter := .inr false
  middle := InitialOffsets.fanAt 0 false a
  inside := pendingInside
  equation := rfl
  prefixPath := .single _ _
  prefixHead := rfl
  prefixLast := rfl
  arrival := rfl
  insideHead := rfl
  insideLabels :=
    .cons (.node _ _ _ (.inverse (InitialOffsets.Event.apply_rel (.fan 0 false) a))) (.single _ _)

/-- A genuine pending RHS path supplies its own actual low reader. The
original whole/prefix assignment has that SAME frontier seam. -/
theorem actual_pending_fixes_function_branch (a : Context) :
    ∀ input output,Labelling site.net fragment.segments input output →
      ∃ middle,Traversal 0 (.op .fan) (.inl ()) (.inr false) input middle :=
  fragment.fan_pending_branch_at_reference site rfl (referencePending a)
    (whole_labels a) (actual_function_prefix_labels a) false rfl

/-- The pending record has an actual contracted physical labelling. The
literal gluing departure remains present, so this is not a two-node shortcut. -/
theorem actual_pending_physical_labels (a : Context) :
    Labelling site.reduce (pendingRaw.map (plugEnd fragmentCut.label right.label))
      (InitialOffsets.fanAt 0 false a) a :=
  ((referencePending a).labelling fragmentCut right).actual fragmentCut right
end Lamping.Checks.ActionFunctionBranchFixture
#print axioms Lamping.AG.SourceEdgeFragment.fan_pending_branch_at_reference
#print axioms Lamping.AG.SourceEdgeFragment.fan_pending_function_branch
#print axioms Lamping.AG.SourceEdgeFragment.fan_target_app_function_branch
#print axioms Lamping.Checks.ActionFunctionBranchFixture.actual_pending_fixes_function_branch
#print axioms Lamping.Checks.ActionFunctionBranchFixture.actual_pending_physical_labels
namespace Lamping.Checks.FamilyRepresentation
open AG Graph Lambda Lambda.Labelled
/-- The actual repeated-label current term still fixes this occurrence's
function source role. Label uniqueness and INIT are not premises. -/
theorem actual_selected_function_role
    (selection : OccurrenceFragmentSelection term actualNet actualRoot) :
    SourceDeparture term .fn
      (sourceEdge (selection functionPosition).environment (selection functionPosition).context
        (selection functionPosition).term).fromPort :=
  selected_function_role selection (p:=[]) rfl functionPosition rfl

/-- The real two-edge argument chain retains its true first occurrence;
it is not silently replaced by the terminal redex edge. -/
theorem actual_argument_first_block
    (selection : OccurrenceFragmentSelection term actualNet actualRoot) :
    (canonicalChainImage selection argument_chain).head?=
      some (selection argumentPosition).fragment.segments :=
  canonical_chain_head selection argument_chain argumentPosition rfl
end Lamping.Checks.FamilyRepresentation
#print axioms Lamping.AG.canonical_chain_head
#print axioms Lamping.AG.selected_function_role
#print axioms Lamping.AG.PathSite.prerequisite_app_copy_branches
#print axioms Lamping.Checks.FamilyRepresentation.actual_selected_function_role
#print axioms Lamping.Checks.FamilyRepresentation.actual_argument_first_block
namespace Lamping.Checks.LambdaWriterFragmentFixture
open AG Graph Lambda Lambda.Labelled
private def kept : Empty → Graph.Label signature := Empty.elim
private def direct : Site (.fanAction .lam 0 1 (by decide)) kept (B:=Bool) (W:=Empty) where
 wire := {
  mate := fun e=>match e with
   | .inl ⟨.inl empty,_⟩ => nomatch empty
   | .inl ⟨.inr (.inl _),.inl _⟩ => .inl ⟨.inr (.inr ()),.inl ()⟩
   | .inl ⟨.inr (.inr _),.inl _⟩ => .inl ⟨.inr (.inl ()),.inl ()⟩
   | .inl ⟨.inr (.inl _),.inr false⟩ => .inl ⟨.inr (.inr ()),.inr true⟩
   | .inl ⟨.inr (.inl _),.inr true⟩ => .inr (.inl false)
   | .inl ⟨.inr (.inr _),.inr false⟩ => .inr (.inl true)
   | .inl ⟨.inr (.inr _),.inr true⟩ => .inl ⟨.inr (.inl ()),.inr false⟩
   | .inr (.inl false) => .inl ⟨.inr (.inl ()),.inr true⟩
   | .inr (.inl true) => .inl ⟨.inr (.inr ()),.inr false⟩
   | .inr (.inr ⟨.inl empty,_⟩) => nomatch empty
   | .inr (.inr ⟨.inr empty,_⟩) => nomatch empty
  involutive := by
   rintro (⟨empty|(u|u),p⟩|(b|⟨empty|empty,d⟩))
   · exact nomatch empty
   · cases u;cases p with | inl u=>cases u;rfl | inr b=>cases b <;> rfl
   · cases u;cases p with | inl u=>cases u;rfl | inr b=>cases b <;> rfl
   · cases b <;> rfl
   · exact nomatch empty
   · exact nomatch empty
  fixedPointFree := by
   rintro (⟨empty|(u|u),p⟩|(b|⟨empty|empty,d⟩))
   · exact nomatch empty
   · cases u;cases p with | inl u=>intro same;cases same | inr b=>cases b <;> (intro same;cases same)
   · cases u;cases p with | inl u=>intro same;cases same | inr b=>cases b <;> (intro same;cases same)
   · cases b <;> (intro same;cases same)
   · exact nomatch empty
   · exact nomatch empty }
 principal := rfl
private def site := direct.pathSite
private def principal : SiteActionPrincipal site where
 edges := [.inl ⟨.inr (.inl ()),.inl ()⟩]
 first := rfl
 last := rfl
 transparent := by intro x y member; cases member
private abbrev rootEnd : Endpoint site.net := .inr (.inl false)
private abbrev controlEnd : Endpoint site.net := .inl ⟨.inr (.inl ()),.inl ()⟩
private abbrev bodyEnd : Endpoint site.net := .inl ⟨.inr (.inr ()),lamBody⟩
private def parentPath : List (Endpoint site.net) := [rootEnd,controlEnd]
private def wholePath : List (Endpoint site.net) := [rootEnd,controlEnd,bodyEnd,controlEnd]
private def piece : List (Endpoint site.net) := [bodyEnd,controlEnd]
private theorem parent_labels (a : Context) :
    Labelling site.net parentPath a (InitialOffsets.fanAt 0 true a) :=
  .cons (.node _ _ _ (.direct (InitialOffsets.Event.apply_rel (.fan 0 true) a))) (.single _ _)
private theorem piece_labels (a : Context) : Labelling site.net piece a (InitialOffsets.fanAt 0 false a) :=
  .cons (.node _ _ _ (.direct (InitialOffsets.Event.apply_rel (.fan 0 false) a))) (.single _ _)
private theorem whole_labels (a : Context) : Labelling site.net wholePath a
    (InitialOffsets.fanAt 0 false (InitialOffsets.fanAt 0 true a)) :=
  .cons (.node _ _ _ (.direct (InitialOffsets.Event.apply_rel (.fan 0 true) a)))
    (.cons (.node _ _ _ (.direct (.lamBody _))) (piece_labels _))
private def parent : RootAccess site.net false :=
  ⟨parentPath,⟨⟨⟨_,_,parent_labels Context.empty⟩,
    .node (.inr (.inl ())) (.inr true) (.inl ()) rfl rfl True.intro (.single _)⟩,rfl,⟨.lam,rfl⟩⟩⟩
private def access : RootAccess site.net false :=
  ⟨wholePath,⟨⟨⟨_,_,whole_labels Context.empty⟩,
    .node (.inr (.inl ())) (.inr true) (.inl ()) rfl rfl True.intro
      (.node (.inr (.inr ())) (.inl ()) lamBody rfl rfl ⟨rfl,rfl⟩
        (.node (.inr (.inl ())) (.inr false) (.inl ()) rfl rfl True.intro (.single _)))⟩,
    rfl,⟨.lam,rfl⟩⟩⟩
private def child : LTerm := .lam (.atom 1) (.var (.atom 2) 0)
private def currentTerm : LTerm := .lam (.atom 0) child
private def fragment : SourceEdgeFragment currentTerm site.net false
    (sourceEdge [.atom 0] (.lamBody (.atom 0)) child) [.body] where
 access := access
 word := rfl
 occurrence := ⟨[.atom 0],.lamBody (.atom 0),child,.body .nil,rfl⟩
 before := parentPath
 segments := piece
 fromEndpoint := bodyEnd
 toEndpoint := .inl ⟨.inr (.inr ()),.inl ()⟩
 fromRealizes := .departure (p:=[]) rfl .body parent rfl .body rfl
 toRealizes := .lamContext (p:=[.body]) rfl access rfl rfl HEq.rfl rfl
 literal := rfl
 start := rfl
 finish := rfl
 forward := .node (.inr (.inl ())) (.inr false) (.inl ()) rfl rfl True.intro (.single _)
 emptyWord := rfl
 assignments := by
  intro a b labels
  obtain ⟨middle,before,after⟩ := labels.split_segment (pre:=[rootEnd]) (e:=controlEnd)
  cases after with
  | cons turn rest =>
    cases turn with
    | node node p q rule =>
      have same := rule.proper_context
      cases same
      exact ⟨middle,Or.inr before,rest⟩

theorem actual_removed_body_outside :
    site.outsideEnd (.inr (.inl (.inr (.inr true))))=fragment.fromEndpoint := rfl

theorem actual_fragment_suffix (a : Context) :
    ∃ pre branch input middle,
      fragment.segments=pre++principal.edges ∧
      pre.getLast?=some (site.net.wire (.inl ⟨.inr (.inl ()),.inr branch⟩)) ∧
      Labelling site.net pre input middle ∧
      Traversal 0 (.op .fan) (.inr branch) (.inl ()) middle
        (InitialOffsets.fanAt 0 false (InitialOffsets.fanAt 0 true a)) := by
  obtain ⟨pre,branch,input,middle,split,_first,last,_piece,labels,writer⟩ :=
    fragment.lambda_writer_suffix site (Or.inl rfl) rfl principal (whole_labels a) rfl
  exact ⟨pre,branch,input,middle,split,last,labels,writer⟩

/-- The suffix proof recovers the actual false auxiliary from the literal
piece, independently of which valid original assignment was supplied. -/
theorem actual_suffix_recovers_false (a : Context) :
    ∃ input middle,Labelling site.net [bodyEnd] input middle ∧
      Traversal 0 (.op .fan) (.inr false) (.inl ()) middle
        (InitialOffsets.fanAt 0 false (InitialOffsets.fanAt 0 true a)) := by
  obtain ⟨pre,branch,input,middle,split,last,labels,writer⟩ := actual_fragment_suffix a
  have literal : pre++principal.edges=[bodyEnd]++principal.edges := split.symm.trans rfl
  have sameBranch : branch=false := site.writer_suffix_aux_unique principal literal last rfl
  have samePre : pre=[bodyEnd] := List.append_cancel_right literal
  subst branch
  subst pre
  exact ⟨input,middle,labels,writer⟩
end Lamping.Checks.LambdaWriterFragmentFixture
#print axioms Lamping.AG.SourcePortRealizes.syntax_departure_word
#print axioms Lamping.AG.SourceEdgeFragment.lambda_first_noninternal
#print axioms Lamping.AG.PathSite.outside_of_noninternal
#print axioms Lamping.AG.SourceEdgeFragment.lambda_writer_suffix
#print axioms Lamping.AG.PathSite.writer_suffix_aux_unique
#print axioms Lamping.Checks.LambdaWriterFragmentFixture.actual_removed_body_outside
#print axioms Lamping.Checks.LambdaWriterFragmentFixture.actual_fragment_suffix
#print axioms Lamping.Checks.LambdaWriterFragmentFixture.actual_suffix_recovers_false
namespace Lamping.Checks.LambdaWriterFragmentFixture
open AG Graph Lambda Lambda.Labelled
private abbrev right := (Schema.fanAction .lam 0 1 (show 0<1 from by decide)).right.net
private abbrev fragmentCut := cutFragment (F:=Bool⊕Bool) (I:=Bool⊕(Empty×Bool)) site.net
  (pathPartition (Schema.fanAction .lam 0 1 (show 0<1 from by decide)) Empty) site.closed
private def outsideRoot : Endpoint fragmentCut := .inr (.inl (.inl false))
private def pendingRaw : List (PlugSegment fragmentCut right) :=
  [.inl outsideRoot,.inr (.inr (.inl (.inl true)))]
private def referencePending (a : Context) : PendingRhsBlock fragmentCut right pendingRaw a a where
  pre := [.inl outsideRoot]
  last := outsideRoot
  enter := .inl true
  middle := a
  inside := [.inr (.inl (.inl true))]
  equation := rfl
  prefixPath := .single _ _
  prefixHead := rfl
  prefixLast := rfl
  arrival := rfl
  insideHead := rfl
  insideLabels := .single _ _

/-- The copied lambda has a real singleton RHS prefix and a real glued
physical path. The original writer is the true branch, not an assumed seam. -/
theorem actual_pending_lambda_labels (a : Context) :
    Labelling site.reduce (pendingRaw.map (plugEnd fragmentCut.label right.label)) a a :=
  ((referencePending a).labelling fragmentCut right).actual fragmentCut right

theorem actual_pending_fixed_writer (a : Context) :
    ∃ pre,Labelling site.net (pre++principal.edges) a (InitialOffsets.fanAt 0 true a) ∧
      pre.head?=some rootEnd ∧
      pre.getLast?=some (site.net.wire (.inl ⟨.inr (.inl ()),.inr true⟩)) ∧
      (pre++principal.edges).getLast?=some (site.net.wire (.inl ⟨.inr (.inr ()),.inl ()⟩)) ∧
      accessWord site.reduce (pendingRaw.map (plugEnd fragmentCut.label right.label))=
        accessWord site.net (pre++principal.edges) :=
  (referencePending a).fixed_principal_ancestor site (.fan .lam 0 1 (by decide)) principal
    outsideRoot rfl true rfl rfl (show Traversal 0 (.op .fan) (.inr true) (.inl ()) a (InitialOffsets.fanAt 0 true a) from .direct (InitialOffsets.Event.apply_rel (.fan 0 true) a))

/-- The same physical finite principal and original root edge occur in the
actual source parent access. This consumer supplies a nonempty principal. -/
theorem actual_original_parent_writer (a : Context) :
    Labelling site.net ([rootEnd]++principal.edges) a (InitialOffsets.fanAt 0 true a) :=
  parent_labels a
end Lamping.Checks.LambdaWriterFragmentFixture
#print axioms Lamping.AG.PendingRhsBlock.fixed_principal_ancestor
#print axioms Lamping.AG.SourceEdgeFragment.pending_lambda_writer
#print axioms Lamping.AG.SourceEdgeFragment.target_lambda_writer
#print axioms Lamping.AG.PathSite.prerequisite_lambda_copy_branches
#print axioms Lamping.Checks.LambdaWriterFragmentFixture.actual_pending_lambda_labels
#print axioms Lamping.Checks.LambdaWriterFragmentFixture.actual_pending_fixed_writer
#print axioms Lamping.Checks.LambdaWriterFragmentFixture.actual_original_parent_writer
namespace Lamping.Checks.UndefinedPrerequisiteFixture
open AG Graph Lambda Lambda.Labelled
private def term : LTerm := .lam (.atom 7)
  (.app (.atom 7) (.var (.atom 7) 0) (.var (.atom 7) 0))
private theorem closed : Closed term.erase := by change 0<1 ∧0<1; decide

theorem actual_root_undefined : NoPrerequisite term [] :=
  no_prerequisite_root_lambda rfl

theorem actual_function_variable_undefined : NoPrerequisite term [.body,.fn] :=
  (no_prerequisite_variable_iff (current:=term) (leaf:=[.body,.fn]) (parent:=[]) (rest:=[.fn])
    rfl rfl rfl rfl).mpr actual_root_undefined

theorem actual_argument_variable_undefined : NoPrerequisite term [.body,.arg] :=
  (no_prerequisite_variable_iff (current:=term) (leaf:=[.body,.arg]) (parent:=[]) (rest:=[.arg])
    rfl rfl rfl rfl).mpr actual_root_undefined

theorem actual_application_undefined : NoPrerequisite term [.body] := by
  apply (no_prerequisite_application_iff (current:=term) (p:=[.body]) rfl).mpr
  exact ⟨(by intro _ _ same; cases same),actual_function_variable_undefined⟩

/-- No successful chain is invented: the finite failed chase reads the
function edge and performs the actual zero-edge jump back to the root binder. -/
theorem actual_application_failure_prefix :
    PrerequisitePrefix term [.body] [[.body,.fn]] [] :=
  .app rfl (fun _ _ same=>by cases same) (.var rfl rfl rfl rfl .refl)

theorem actual_undefined_top : ∃ stamp body edges,term.subterm []=some (.lam stamp body) ∧
    PrerequisitePrefix term [.body] edges [] :=
  no_prerequisite_root_prefix closed (position:=[.body]) rfl actual_application_undefined

theorem actual_variable_zero_jump :
    PrerequisitePrefix term [.body,.arg] [] [] := .var rfl rfl rfl rfl .refl

/-- A real redex cannot use the undefined branch merely because its labels repeat. -/
theorem actual_redex_not_undefined :
    ¬NoPrerequisite (.app (.atom 7) (.lam (.atom 7) (.var (.atom 7) 0))
      (.lam (.atom 7) (.var (.atom 7) 0))) [] := by
  intro noChain
  exact noChain ⟨[[.fn]],.redex_app rfl⟩
end Lamping.Checks.UndefinedPrerequisiteFixture
#print axioms Lamping.Lambda.Labelled.no_prerequisite_root_prefix
#print axioms Lamping.Lambda.Labelled.no_prerequisite_variable_iff
#print axioms Lamping.Lambda.Labelled.no_prerequisite_application_iff
#print axioms Lamping.Checks.UndefinedPrerequisiteFixture.actual_application_undefined
#print axioms Lamping.Checks.UndefinedPrerequisiteFixture.actual_application_failure_prefix
#print axioms Lamping.Checks.UndefinedPrerequisiteFixture.actual_undefined_top
#print axioms Lamping.Checks.UndefinedPrerequisiteFixture.actual_variable_zero_jump
#print axioms Lamping.Checks.UndefinedPrerequisiteFixture.actual_redex_not_undefined
namespace Lamping.Checks.UnaryCanonicalFixture
open AG Graph
private def kept : Empty → Graph.Label signature := Empty.elim
private def direct : Site (.croAction .lam 0 1 (by decide)) kept (B:=Unit) (W:=Empty) where
  wire := {
    mate := fun e=>match e with
      | .inl ⟨.inl empty,_⟩ => nomatch empty
      | .inl ⟨.inr (.inl _),.inl _⟩ => .inl ⟨.inr (.inr ()),.inl ()⟩
      | .inl ⟨.inr (.inr _),.inl _⟩ => .inl ⟨.inr (.inl ()),.inl ()⟩
      | .inl ⟨.inr (.inl _),.inr _⟩ => .inl ⟨.inr (.inr ()),.inr true⟩
      | .inl ⟨.inr (.inr _),.inr false⟩ => .inr (.inl ())
      | .inl ⟨.inr (.inr _),.inr true⟩ => .inl ⟨.inr (.inl ()),.inr ()⟩
      | .inr (.inl _) => .inl ⟨.inr (.inr ()),.inr false⟩
      | .inr (.inr ⟨.inl empty,_⟩) => nomatch empty
      | .inr (.inr ⟨.inr empty,_⟩) => nomatch empty
    involutive := by
      rintro (⟨empty|(u|u),p⟩|(u|⟨empty|empty,d⟩))
      · exact nomatch empty
      · cases u; cases p with | inl u=>cases u;rfl | inr u=>cases u;rfl
      · cases u; cases p with | inl u=>cases u;rfl | inr b=>cases b <;> rfl
      · cases u;rfl
      · exact nomatch empty
      · exact nomatch empty
    fixedPointFree := by
      rintro (⟨empty|(u|u),p⟩|(u|⟨empty|empty,d⟩))
      · exact nomatch empty
      · cases u; cases p with | inl u=>intro same;cases same | inr u=>intro same;cases same
      · cases u; cases p with | inl u=>intro same;cases same | inr b=>cases b <;> (intro same;cases same)
      · intro same; cases same
      · exact nomatch empty
      · exact nomatch empty }
  principal := rfl
private def site := direct.pathSite
private def principal : SiteActionPrincipal site where
  edges := [.inl ⟨.inr (.inl ()),.inl ()⟩]
  first := rfl
  last := rfl
  transparent := by intro e f member; cases member
private def crossing := principal.crossing site () true
private theorem actual_cross_labels (a : Context) :
    Labelling site.net crossing a (InitialOffsets.croAt 0 a) :=
  .cons (.node _ _ _ (.direct (InitialOffsets.Event.apply_rel (.cro 0) a)))
    (.cons (.node _ _ _ (.direct (.lamBody _))) (.single _ _))

theorem actual_cross_unique (rhs : List (Endpoint (unaryRightCore .cro .lam (Bij.refl Unit) 0 0)))
    (other : UnaryCanonicalLocal site (Bij.refl Unit) (k:=0) principal rhs crossing) :
    rhs=unaryCrossEdges (s:=Schema.croAction .lam 0 1 (by decide)) (k:=0) (Bij.refl Unit) true :=
  other.fixed_target_unique site (Bij.refl Unit) (UnaryCanonicalLocal.cross (site:=site) (single:=Bij.refl Unit) (principal:=principal) (k:=0) true) rfl

theorem actual_reverse_unique
    (rhs : List (Endpoint (unaryRightCore .cro .lam (Bij.refl Unit) 0 0)))
    (other : UnaryCanonicalLocal site (Bij.refl Unit) (k:=0) principal rhs (reverseEdges crossing)) :
    rhs=reverseEdges (unaryCrossEdges (s:=Schema.croAction .lam 0 1 (by decide)) (k:=0) (Bij.refl Unit) true) :=
  other.fixed_target_unique site (Bij.refl Unit) (UnaryCanonicalLocal.backward (site:=site) (single:=Bij.refl Unit) (principal:=principal) (k:=0) true) rfl

theorem actual_old_assignment_and_reverse (a : Context) :
    Labelling site.net crossing a (InitialOffsets.croAt 0 a) ∧
      Labelling site.net (reverseEdges crossing) (InitialOffsets.croAt 0 a) a :=
  ⟨actual_cross_labels a,(actual_cross_labels a).reverse⟩
end Lamping.Checks.UnaryCanonicalFixture
#print axioms Lamping.AG.UnaryCanonicalLocal.fixed_target_unique
#print axioms Lamping.Checks.UnaryCanonicalFixture.actual_cross_unique
#print axioms Lamping.Checks.UnaryCanonicalFixture.actual_reverse_unique
#print axioms Lamping.Checks.UnaryCanonicalFixture.actual_old_assignment_and_reverse
namespace Lamping.Checks.UnaryCanonicalFixture
open AG Graph
private abbrev schema := Schema.croAction .lam 0 1 (show 0<1 from by decide)
private abbrev right := schema.right.net
private abbrev fragmentCut := cutFragment (F:=Unit⊕Bool) (I:=Bool⊕(Empty×Bool)) site.net
  (pathPartition schema Empty) site.closed
private def outsideBody : Endpoint fragmentCut := .inr (.inl (.inr (.inr true)))
private def localPath (a : Context) : LocalPath right (.inl ()) (.inr true) a (InitialOffsets.croAt 0 a) where
  edges := unaryCrossEdges (s:=schema) (k:=0) (Bij.refl Unit) true
  start := rfl
  finish := rfl
  labeling := .cons (LabelledTurn.node (g:=right) (.inl ()) _ _ (.direct (.lamBody a)))
    (.cons (LabelledTurn.node (g:=right) (.inr true) _ _ (.direct (InitialOffsets.Event.apply_rel (.cro 0) a))) (.single _ _))
private def wholeRaw : List (PlugSegment fragmentCut right) :=
  .inl outsideBody::((localPath Context.empty).edges.map Sum.inr++[.inl outsideBody])
private theorem wholeLabels (a : Context) : PlugLabelling fragmentCut right wholeRaw a (InitialOffsets.croAt 0 a) :=
  (PlugExcursions.through (c:=fragmentCut) (r:=right) (e:=outsideBody) (localPath a) rfl (.single outsideBody _)).labelling fragmentCut right
private theorem wholeCanonical : ActionCanonicalBlocks site principal wholeRaw crossing :=
  .through ((localPath Context.empty).edges)
    [site.net.wire (.inl ⟨.inr (.inl ()),.inr ()⟩),.inl ⟨.inr (.inl ()),.inl ()⟩]
    (.cro (UnaryCanonicalLocal.cross (site:=site) (single:=Bij.refl Unit) (principal:=principal) (k:=0) true)) rfl (.single outsideBody)

/-- The actual whole RHS has one complete through block, an entry, and an
exit. It can be compared against any other genuinely labelled presentation. -/
theorem actual_whole_target_unique
    (raw : List (PlugSegment fragmentCut right))
    (relation : ActionCanonicalBlocks site principal raw crossing) {a b : Context}
    (labels : PlugLabelling fragmentCut right raw a b) : raw=wholeRaw :=
  relation.unary_target_unique_of_labels site (by intro impossible; cases impossible)
    wholeCanonical labels (wholeLabels Context.empty) rfl

theorem actual_whole_all_assignments (a : Context) :
    PlugLabelling fragmentCut right wholeRaw a (InitialOffsets.croAt 0 a) ∧
      Labelling site.reduce (wholeRaw.map (plugEnd fragmentCut.label right.label)) a (InitialOffsets.croAt 0 a) :=
  ⟨wholeLabels a,(wholeLabels a).actual fragmentCut right⟩
end Lamping.Checks.UnaryCanonicalFixture
#print axioms Lamping.AG.ActionCanonicalBlocks.unary_target_unique_of_labels
#print axioms Lamping.AG.ActionCanonicalLocal.unary_front_unique
#print axioms Lamping.Checks.UnaryCanonicalFixture.actual_whole_target_unique
#print axioms Lamping.Checks.UnaryCanonicalFixture.actual_whole_all_assignments
namespace Lamping.Checks.UnaryCanonicalFixture
open AG Graph
private abbrev oldBody : Endpoint site.net := .inl ⟨.inr (.inr ()),.inr true⟩
private abbrev oldControl : Endpoint site.net := .inl ⟨.inr (.inl ()),.inl ()⟩

/-- The same outside endpoint occurs at both ends of this real crossing.
This application selects its FIRST literal occurrence. -/
theorem actual_first_outside_cut : ∃ rawBefore rawAfter,
    wholeRaw=rawBefore++Sum.inl outsideBody::rawAfter ∧
    ActionCanonicalBlocks site principal (rawBefore++[Sum.inl outsideBody]) [oldBody] ∧
    ActionCanonicalBlocks site principal (Sum.inl outsideBody::rawAfter) crossing :=
  wholeCanonical.split_at_outside site outsideBody (before:=[]) (after:=[oldControl,oldBody]) rfl

/-- This application selects the LAST occurrence of that same endpoint;
the complete through block now belongs to the left prefix. -/
theorem actual_last_outside_cut : ∃ rawBefore rawAfter,
    wholeRaw=rawBefore++Sum.inl outsideBody::rawAfter ∧
    ActionCanonicalBlocks site principal (rawBefore++[Sum.inl outsideBody]) crossing ∧
    ActionCanonicalBlocks site principal (Sum.inl outsideBody::rawAfter) [oldBody] :=
  wholeCanonical.split_at_outside site outsideBody (before:=[oldBody,oldControl]) (after:=[]) rfl

theorem actual_principal_not_an_outside_cut (outside : Endpoint fragmentCut) :
    oldControl≠site.outsideEnd outside := site.internal_outside_ne (.inl false) outside
end Lamping.Checks.UnaryCanonicalFixture
#print axioms Lamping.AG.ActionCanonicalLocal.front_tail_internal
#print axioms Lamping.AG.ActionCanonicalBlocks.split_at_outside
#print axioms Lamping.Checks.UnaryCanonicalFixture.actual_first_outside_cut
#print axioms Lamping.Checks.UnaryCanonicalFixture.actual_last_outside_cut
#print axioms Lamping.Checks.UnaryCanonicalFixture.actual_principal_not_an_outside_cut
namespace Lamping.Checks.UnaryCanonicalFixture
open AG Graph
private def auxiliaryOutside : Endpoint fragmentCut := .inr (.inl (.inr (.inl ())))
private def auxiliaryRaw : List (PlugSegment fragmentCut right) :=
  [.inl auxiliaryOutside,.inr (.inr (.inl (.inr true))),.inr (.inl ⟨.inr true,.inr ()⟩)]
private def auxiliaryPending (a : Context) :
    PendingRhsBlock fragmentCut right auxiliaryRaw (InitialOffsets.croAt 0 a) a where
  pre := [.inl auxiliaryOutside]
  last := auxiliaryOutside
  enter := .inr true
  middle := InitialOffsets.croAt 0 a
  inside := [.inr (.inl (.inr true)),.inl ⟨.inr true,.inr ()⟩]
  equation := rfl
  prefixPath := .single _ _
  prefixHead := rfl
  prefixLast := rfl
  arrival := rfl
  insideHead := rfl
  insideLabels := .cons (LabelledTurn.node (g:=right) (.inr true) _ _
    (.inverse (InitialOffsets.Event.apply_rel (.cro 0) a))) (.single _ _)

/-- The copied lambda BODY auxiliary is a genuine pending reader terminal.
The theorem trims its actual two RHS segments, retaining the same principal. -/
theorem actual_auxiliary_canonical_trim (a : Context) :
    ∃ old,ActionCanonicalBlocks site principal [.inl auxiliaryOutside] old ∧
      Labelling site.net old (InitialOffsets.croAt 0 a) (InitialOffsets.croAt 0 a) ∧
      old.head?=some (site.net.wire oldBody) ∧old.getLast?=some (site.net.wire oldBody) ∧
      auxiliaryRaw=[.inl auxiliaryOutside]++
        [.inr (.inr (.inl (.inr true))),.inr (.inl ⟨.inr true,.inr ()⟩)] ∧
      Traversal 0 (.op .cro) (.inl ()) (.inr ()) (InitialOffsets.croAt 0 a) a ∧
      accessWord site.reduce (auxiliaryRaw.map (plugEnd fragmentCut.label right.label))=
        accessWord site.net old :=
  (auxiliaryPending a).cro_aux_canonical_trim site principal auxiliaryOutside rfl true rfl

theorem actual_auxiliary_raw_labels (a : Context) :
    PlugLabelling fragmentCut right auxiliaryRaw (InitialOffsets.croAt 0 a) a :=
  (auxiliaryPending a).labelling fragmentCut right
end Lamping.Checks.UnaryCanonicalFixture
#print axioms Lamping.AG.PendingRhsBlock.cro_aux_canonical_trim
#print axioms Lamping.AG.PendingRhsBlock.bra_aux_canonical_trim
#print axioms Lamping.Checks.UnaryCanonicalFixture.actual_auxiliary_canonical_trim
#print axioms Lamping.Checks.UnaryCanonicalFixture.actual_auxiliary_raw_labels
namespace Lamping.Checks.PendingCanonicalOccurrenceConsumer
open AG Graph Lambda Lambda.Labelled
section
variable {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K → Label signature} {f : Op} {i j : Nat} {lt : i<j}
variable (site : PathSite (Schema.croAction f i j lt) kept (B:=B) (W:=W) (V:=V))

/-- A conditional signature consumer: real same-position fragments supply the
word equality internally. This is not a new reachable action fixture. -/
theorem same_position_cro_access_prefix
    {directions : B → Bool} (flow : FlowBalance site.net directions)
    (root : B) (positive : directions root=true) {current : LTerm}
    (matching : Matches site.net root current.erase) (principal : SiteActionPrincipal site)
    {position : Path} (source : OccurrenceFragment current site.net root position)
    (target : OccurrenceFragment current site.reduce root position)
    (q : Aux f) (finish : target.fragment.access.val.getLast?=
      some (site.reduce.wire (.inl ⟨.inr (.inl ()),.inr q⟩)))
    {a b : Context} (labels : Labelling site.reduce target.fragment.access.val a b) :
    ∃ pending : PendingRhsBlock
        (cutFragment site.net (pathPartition (Schema.croAction f i j lt) V) site.closed)
        (Schema.croAction f i j lt).right.net
        (target.fragment.access.val.map (plugEnd
          (cutFragment site.net (pathPartition (Schema.croAction f i j lt) V) site.closed).label
          (Schema.croAction f i j lt).right.net.label).invFun) a b,
      ActionCanonicalBlocks site principal pending.pre source.fragment.access.val ∧
      Labelling site.net source.fragment.access.val a pending.middle := by
  obtain ⟨pending,relation,oldLabels,_last,_split⟩ := site.cro_aux_canonical_access flow root positive
    matching principal source.fragment.access target.fragment.access
    (source.fragment.word.trans target.fragment.word.symm) q finish labels
  exact ⟨pending,relation,oldLabels⟩
end
end Lamping.Checks.PendingCanonicalOccurrenceConsumer
#print axioms Lamping.AG.PathSite.cro_aux_canonical_access
#print axioms Lamping.AG.PathSite.bra_aux_canonical_access
#print axioms Lamping.Checks.PendingCanonicalOccurrenceConsumer.same_position_cro_access_prefix
namespace Lamping.Checks.UnaryCanonicalFixture
open AG Graph
private def contextRaw : List (PlugSegment fragmentCut right) :=
  [.inl outsideBody,.inr (.inr (.inl (.inl ())))]
private def contextPending (a : Context) : PendingRhsBlock fragmentCut right contextRaw a a where
  pre := [.inl outsideBody]
  last := outsideBody
  enter := .inl ()
  middle := a
  inside := [.inr (.inl (.inl ()))]
  equation := rfl
  prefixPath := .single _ _
  prefixHead := rfl
  prefixLast := rfl
  arrival := rfl
  insideHead := rfl
  insideLabels := .single _ _

theorem actual_context_padding_is_whole : contextRaw++
    [.inr (.inl ⟨.inl (),.inr true⟩),.inr (.inl ⟨.inr true,.inl ()⟩),.inl outsideBody]=
      wholeRaw := rfl

/-- This real pending lambda context pads to the previously constructed
whole crossing; the accepted source-uniqueness theorem identifies its old path. -/
theorem actual_pending_context_padded_source (a : Context) :
    ActionCanonicalBlocks site principal wholeRaw crossing ∧
      Labelling site.net crossing a (InitialOffsets.croAt 0 a) ∧
      PlugExcursions fragmentCut right wholeRaw a (InitialOffsets.croAt 0 a) := by
  obtain ⟨old,relation,labels,_head,_last,whole⟩ :=
    (contextPending a).cro_lambda_canonical_completion site principal outsideBody rfl rfl
  change ActionCanonicalBlocks site principal wholeRaw old at relation
  change PlugExcursions fragmentCut right wholeRaw a (InitialOffsets.croAt 0 a) at whole
  have oldEq := relation.fixed_source_unique site wholeCanonical
  rw [oldEq] at relation labels
  exact ⟨relation,labels,whole⟩
end Lamping.Checks.UnaryCanonicalFixture
#print axioms Lamping.AG.PlugExcursions.overlap_join
#print axioms Lamping.AG.PendingRhsBlock.cro_lambda_canonical_completion
#print axioms Lamping.AG.PendingRhsBlock.bra_lambda_canonical_completion
#print axioms Lamping.Checks.UnaryCanonicalFixture.actual_context_padding_is_whole
#print axioms Lamping.Checks.UnaryCanonicalFixture.actual_pending_context_padded_source
namespace Lamping.Checks.LambdaCanonicalOccurrenceConsumer
open AG Graph Lambda Lambda.Labelled
section
variable {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K → Label signature} {i j : Nat} {lt : i<j}
variable (site : PathSite (Schema.croAction .lam i j lt) kept (B:=B) (W:=W) (V:=V))

/-- The real target access supplies its own assignment; same Position supplies
its word. This conditional consumer does not assert a reachable action fixture. -/
theorem same_position_cro_lambda_padding
    {directions : B → Bool} (flow : FlowBalance site.net directions)
    (root : B) (positive : directions root=true) {current : LTerm}
    (matching : Matches site.net root current.erase) (principal : SiteActionPrincipal site)
    {position : Path} (source : OccurrenceFragment current site.net root position)
    (target : OccurrenceFragment current site.reduce root position)
    (finish : target.fragment.access.val.getLast?=
      some (site.reduce.wire (.inl ⟨.inr (.inl ()),.inl ()⟩))) :
    ActionCanonicalBlocks site principal
      (target.fragment.access.val.map (plugEnd
        (cutFragment site.net (pathPartition (Schema.croAction .lam i j lt) V) site.closed).label
        (Schema.croAction .lam i j lt).right.net.label).invFun++
        [.inr (.inl ⟨.inl (),.inr true⟩),.inr (.inl ⟨.inr true,.inl ()⟩),
          .inl (.inr (.inl (.inr (.inr true))))])
      (source.fragment.access.val++[.inl ⟨.inr (.inr ()),.inr true⟩]) := by
  obtain ⟨a,b,labels⟩ := target.fragment.access.property.1.1
  exact site.cro_lambda_canonical_access flow root positive matching principal
    source.fragment.access target.fragment.access
    (source.fragment.word.trans target.fragment.word.symm) finish labels
end
end Lamping.Checks.LambdaCanonicalOccurrenceConsumer
#print axioms Lamping.AG.PathSite.cro_lambda_canonical_access
#print axioms Lamping.AG.PathSite.bra_lambda_canonical_access
#print axioms Lamping.Checks.LambdaCanonicalOccurrenceConsumer.same_position_cro_lambda_padding
namespace Lamping.Checks.FamilyRepresentation
open AG Graph Lambda Lambda.Labelled

/-- The actual encoded repeated-label term has no INIT requirement. Two
arbitrary legal occurrence selectors give the same physical parent seam. -/
theorem actual_noninit_parent_seams
    (first second : OccurrenceFragmentSelection term actualNet actualRoot) :
    (first argumentPosition).fragment.access.val.getLast?=
      (second argumentPosition).fragment.access.val.getLast? := by
  have matching := encode_closed_matches term.erase actual_closed 0
  let left := first argumentVariablePosition
  let right := second argumentVariablePosition
  have lrole : SourceDeparture identity .body
      (sourceEdge left.environment left.context left.term).fromPort := by
    rw [argument_variable_source left]
    exact .body
  have rrole : SourceDeparture identity .body
      (sourceEdge right.environment right.context right.term).fromPort := by
    rw [argument_variable_source right]
    exact .body
  exact SourceEdgeFragment.equal_piece_parent_seams matching left.fragment right.fragment lrole rrole
    (first argumentPosition).fragment.access (second argumentPosition).fragment.access
    (by rw [(first argumentPosition).fragment.word];rfl)
    (by rw [(second argumentPosition).fragment.word];rfl)
    (OccurrenceFragment.segments_unique matching left right)
end Lamping.Checks.FamilyRepresentation
namespace Lamping.Checks.UnaryCanonicalFixture
open AG Graph

/-- The specified singleton parent prefix forces the FIRST ordinal of the
repeated outside body endpoint, not an arbitrary occurrence of its value. -/
theorem actual_first_parent_prefix_ordinal (a : Context) :
    ∃ seam,ActionCanonicalBlocks site principal (Sum.inl outsideBody::wholeRaw.tail) crossing ∧
      PlugLabelling fragmentCut right (Sum.inl outsideBody::wholeRaw.tail) seam
        (InitialOffsets.croAt 0 a) :=
  wholeCanonical.unary_cut_at_actual_prefix site (by intro impossible;cases impossible)
    (.single outsideBody) (wholeLabels a) (.single (.inl outsideBody) a) rfl rfl outsideBody rfl

/-- The specified whole parent prefix forces the LAST ordinal of that same
endpoint. The exact new child suffix is empty, not a successful empty chain. -/
theorem actual_last_parent_prefix_ordinal (a : Context) :
    ∃ seam,ActionCanonicalBlocks site principal [Sum.inl outsideBody] [oldBody] ∧
      PlugLabelling fragmentCut right [Sum.inl outsideBody] seam (InitialOffsets.croAt 0 a) := by
  have result := wholeCanonical.unary_cut_at_actual_prefix site
    (by intro impossible;cases impossible) wholeCanonical (wholeLabels a) (wholeLabels a)
    (oldPiece:=[]) (newPiece:=[]) (by rw [List.append_nil]) (by rw [List.append_nil]) outsideBody rfl
  exact result
end Lamping.Checks.UnaryCanonicalFixture
#print axioms Lamping.AG.SourceEdgeFragment.equal_piece_parent_seams
#print axioms Lamping.AG.PlugLabelling.split_overlap
#print axioms Lamping.AG.ActionCanonicalBlocks.unary_cut_at_actual_prefix
#print axioms Lamping.Checks.FamilyRepresentation.actual_noninit_parent_seams
#print axioms Lamping.Checks.UnaryCanonicalFixture.actual_first_parent_prefix_ordinal
#print axioms Lamping.Checks.UnaryCanonicalFixture.actual_last_parent_prefix_ordinal
namespace Lamping.Checks.ReachableUnaryFixture
open AG Graph Lambda Lambda.Labelled
private def nodeRename : Bij (BetaKept⊕Empty) (Unit⊕(Unit⊕Unit)) where
  toFun
    | .inl (.inl _) => .inr (.inl ())
    | .inl (.inr (.inl _)) => .inr (.inr ())
    | .inl (.inr (.inr _)) => .inl ()
    | .inr e => nomatch e
  invFun
    | .inr (.inl _) => .inl (.inl ())
    | .inr (.inr _) => .inl (.inr (.inl ()))
    | .inl _ => .inl (.inr (.inr ()))
  left_inv := by rintro ((u|(v|w))|e);cases u;rfl;cases v;rfl;cases w;rfl;exact nomatch e
  right_inv := by rintro (u|(v|w));cases u;rfl;cases v;rfl;cases w;rfl
private def portRename : Bij
    (NodePort signature (BetaKept⊕Empty) actualBetaReduced.label)
    (NodePort signature (Unit⊕(Unit⊕Unit)) ContinuationLabel) where
  toFun
    | ⟨.inl (.inl _),p⟩ => ⟨.inr (.inl ()),p⟩
    | ⟨.inl (.inr (.inl _)),p⟩ => ⟨.inr (.inr ()),p⟩
    | ⟨.inl (.inr (.inr _)),p⟩ => ⟨.inl (),p⟩
    | ⟨.inr e,_⟩ => nomatch e
  invFun
    | ⟨.inr (.inl _),p⟩ => ⟨.inl (.inl ()),p⟩
    | ⟨.inr (.inr _),p⟩ => ⟨.inl (.inr (.inl ())),p⟩
    | ⟨.inl _,p⟩ => ⟨.inl (.inr (.inr ())),p⟩
  left_inv := by rintro ⟨((u|(v|w))|e),p⟩;cases u;rfl;cases v;rfl;cases w;rfl;exact nomatch e
  right_inv := by rintro ⟨(u|(v|w)),p⟩;cases u;rfl;cases v;rfl;cases w;rfl

def actualContinuationIso : NetIso actualBetaReduced actualContinuationSite.net where
  nodes := nodeRename
  vertices := continuationVertices
  labels := by rintro ((u|(v|w))|e);rfl;rfl;rfl;exact nomatch e
  ports := portRename
  port_node := by rintro ⟨((u|(v|w))|e),p⟩;rfl;rfl;rfl;exact nomatch e
  port_role := by rintro ⟨((u|(v|w))|e),p⟩;exact HEq.rfl;exact HEq.rfl;exact HEq.rfl;exact nomatch e
  ends := continuationEnds
  node_end := by rintro ⟨((u|(v|w))|e),p⟩;rfl;rfl;rfl;exact nomatch e
  boundary_end _ := rfl
  vertex_end _ _ := rfl
  wiring := continuation_wiring

theorem actual_source_matches : Matches actualContinuationSite.net (.inl ()) identity := by
  apply actualContinuationIso.matches
  exact SoundnessFirstHistoryEvaluation.actual_complete_beta_matches

theorem actual_reachable_source_step : GraphStep (.beta 0)
    (ActualNet.ofNet identityAppNet) (ActualNet.ofNet actualContinuationSite.net) :=
  .atSite betaKeptLabels actualBetaSite betaEncodingIso actualContinuationIso

theorem actual_target_matches : Matches actualControlReduced (.inl ()) identity := by
  obtain ⟨flow⟩ := actualBetaSite.reduce_flowBalance SoundnessBetaAncestor.actualFlow
  obtain ⟨balance⟩ := encode_indexed_balance identityApp 0
  obtain ⟨reducedBalance⟩ := actualBetaSite.reduce_indexed_balance (betaEncodingIso.indexed_balance balance)
  exact actualContinuationSite.action_matches_rootInputs (.cro .lam 0 1 (by decide))
    (actualContinuationIso.flowBalance flow) (.inl ()) rfl
    (actualContinuationIso.indexed_balance reducedBalance) rfl
    (actualContinuationIso.rootInputs SoundnessRootBetaInputs.actual_beta_rootInputs)
    (actualContinuationIso.transparency SoundnessBetaTransparency.actual_reduced_transparency)
    actual_source_matches

abbrev current : LTerm := SoundnessFirstHistoryEvaluation.developed
private theorem current_closed : Closed current.erase := by change 0<1;decide

theorem actual_source_lambda_access : ∃ access : RootAccess actualContinuationSite.net (.inl ()),
    accessWord actualContinuationSite.net access.val=[] ∧
      access.val.getLast?=some (actualContinuationSite.net.wire (.inl ⟨.inr (.inr ()),.inl ()⟩)) := by
  obtain ⟨⟨access,word,node,port,context,finish⟩⟩ :=
    actual_source_matches.physical_context_occurrence (current:=current) current_closed
      (position:=[]) (Or.inr ⟨current.label,.var (.atom 4) 0,rfl⟩)
  rcases node with u|(v|w)
  · rcases context with ⟨bad,_⟩|⟨bad,_⟩ <;> cases bad
  · rcases context with ⟨bad,_⟩|⟨bad,_⟩ <;> cases bad
  · cases w
    rcases context with ⟨bad,_⟩|⟨_,role⟩
    · cases bad
    · have same : port=.inl () := eq_of_heq role
      subst port
      exact ⟨access,word,finish⟩

theorem actual_target_lambda_access : ∃ access : RootAccess actualControlReduced (.inl ()),
    accessWord actualControlReduced access.val=[] ∧
      access.val.getLast?=some (actualControlReduced.wire (.inl ⟨.inr (.inl ()),.inl ()⟩)) := by
  obtain ⟨⟨access,word,node,port,context,finish⟩⟩ :=
    actual_target_matches.physical_context_occurrence (current:=current) current_closed
      (position:=[]) (Or.inr ⟨current.label,.var (.atom 4) 0,rfl⟩)
  rcases node with u|(v|branch)
  · rcases context with ⟨bad,_⟩|⟨bad,_⟩ <;> cases bad
  · cases v
    rcases context with ⟨bad,_⟩|⟨_,role⟩
    · cases bad
    · have same : port=.inl () := eq_of_heq role
      subst port
      exact ⟨access,word,finish⟩
  · rcases context with ⟨bad,_⟩|⟨bad,_⟩ <;> cases bad

/-- A real closed source reached by the actual I I beta step supplies the
higher lambda-context canonical padding theorem without matching oracles. -/
theorem actual_reachable_lambda_padding :
    ∃ (principal : SiteActionPrincipal actualContinuationSite)
      (source : RootAccess actualContinuationSite.net (.inl ()))
      (target : RootAccess actualControlReduced (.inl ())),
      accessWord actualContinuationSite.net source.val=[] ∧
      accessWord actualControlReduced target.val=[] ∧
      ActionCanonicalBlocks actualContinuationSite principal
        (target.val.map (plugEnd
          (cutFragment actualContinuationSite.net (pathPartition continuationSchema ContinuationV)
            actualContinuationSite.closed).label continuationSchema.right.net.label).invFun++
          [.inr (.inl ⟨.inl (),.inr true⟩),.inr (.inl ⟨.inr true,.inl ()⟩),
            .inl (.inr (.inl (.inr (.inr true))))])
        (source.val++[.inl ⟨.inr (.inr ()),.inr true⟩]) := by
  obtain ⟨source,sourceWord,_sourceFinish⟩ := actual_source_lambda_access
  obtain ⟨target,targetWord,targetFinish⟩ := actual_target_lambda_access
  obtain ⟨principal⟩ := actualContinuationSite.actionPrincipal_exists
  obtain ⟨a,b,labels⟩ := target.property.1.1
  obtain ⟨flow⟩ := actualBetaSite.reduce_flowBalance SoundnessBetaAncestor.actualFlow
  exact ⟨principal,source,target,sourceWord,targetWord,
    actualContinuationSite.cro_lambda_canonical_access (actualContinuationIso.flowBalance flow)
      (.inl ()) rfl actual_source_matches principal source target
      (sourceWord.trans targetWord.symm) targetFinish labels⟩

theorem actual_same_global_labels :
    History [[]] SoundnessFirstHistoryEvaluation.original current :=
  .cons (.root _ _ _ _) (.nil _)

theorem actual_two_rule_trace : GraphTrace (ActualNet.initial identityApp)
    (ActualNet.ofNet actualControlReduced) [Schema.beta 0,continuationSchema] :=
  .cons actual_reachable_source_step
    (.cons (.site continuationKept actualContinuationSite) (.refl _))
end Lamping.Checks.ReachableUnaryFixture
#print axioms Lamping.Checks.ReachableUnaryFixture.actualContinuationIso
#print axioms Lamping.Checks.ReachableUnaryFixture.actual_reachable_source_step
#print axioms Lamping.Checks.ReachableUnaryFixture.actual_source_matches
#print axioms Lamping.Checks.ReachableUnaryFixture.actual_target_matches
#print axioms Lamping.Checks.ReachableUnaryFixture.actual_source_lambda_access
#print axioms Lamping.Checks.ReachableUnaryFixture.actual_target_lambda_access
#print axioms Lamping.Checks.ReachableUnaryFixture.actual_reachable_lambda_padding
#print axioms Lamping.Checks.ReachableUnaryFixture.actual_same_global_labels
#print axioms Lamping.Checks.ReachableUnaryFixture.actual_two_rule_trace
namespace Lamping.Checks.ReachableKeptUnaryFixture
open AG Graph Lambda Lambda.Labelled
open ReachableUnaryFixture
private def advance (e : Endpoint actualControlReduced) : Endpoint actualControlReduced :=
  match actualControlReduced.wire e with
  | .inr (.inr (w,d)) => .inr (.inr (w,!d))
  | e => e
private def start : Endpoint actualControlReduced := .inl ⟨.inr (.inr false),.inl ()⟩
def route : TransparentCorridor actualControlReduced where
  first := ⟨.inr (.inr false),.inl ()⟩
  last := ⟨.inl (),.inl ()⟩
  edges := [start,advance start,advance (advance start)]
  start := rfl
  finish := rfl
  transparent := by
    intro e f member
    change (e,f)∈[(start,advance start),(advance start,advance (advance start))] at member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with h|h
    · cases h; exact ⟨_,true,rfl,rfl⟩
    · cases h; exact ⟨_,false,rfl,rfl⟩
abbrev schema : Schema := .croAction .cro 0 1 (by decide)
noncomputable def presentation := Classical.choice (physical_corridor_presentation actualControlReduced schema route
  (.inr (.inr false)) (.inl ()) (by intro h;cases h) rfl rfl (.inl ()) (.inl ()) HEq.rfl HEq.rfl rfl rfl)
noncomputable abbrev site := presentation.site
abbrev current : LTerm := ReachableUnaryFixture.current
private theorem closed : Closed current.erase := by change 0<1;decide
theorem actual_third_step : GraphStep schema (ActualNet.ofNet actualControlReduced) (ActualNet.ofNet site.reduce) :=
  presentation.graph_step
private theorem rootInputs : RootInputs actualControlReduced (.inl ()) := by
  obtain ⟨u,_,inputs,_⟩ := initial_trace_soundness identityApp ⟨Nat.zero_lt_succ 0,Nat.zero_lt_succ 0⟩
    (ActualNet.ofNet actualControlReduced) _ actual_two_rule_trace
  exact inputs
private theorem transparency : Transparency actualControlReduced (.inl ()) :=
  initial_trace_transparency identityApp ⟨Nat.zero_lt_succ 0,Nat.zero_lt_succ 0⟩ _ _ actual_two_rule_trace
private theorem flow : Nonempty (FlowBalance actualControlReduced initialBoundaryPolarity) := by
  exact initial_trace_flowBalance identityApp _ _ actual_two_rule_trace
private theorem balance : Nonempty (IndexedLevelBalance actualControlReduced (boundaryDepthAt 0)) :=
  initial_trace_indexed_balance identityApp _ _ actual_two_rule_trace

theorem source_matches : Matches site.net (.inl ()) current.erase :=
  presentation.sourceIso.matches actual_target_matches

theorem target_matches : Matches site.reduce (.inl ()) current.erase := by
  obtain ⟨f⟩ := flow
  obtain ⟨b⟩ := balance
  exact site.action_matches_rootInputs (.cro .cro 0 1 (by decide))
    (presentation.sourceIso.flowBalance f) (.inl ()) rfl
    (presentation.sourceIso.indexed_balance b) rfl
    (presentation.sourceIso.rootInputs rootInputs) (presentation.sourceIso.transparency transparency) source_matches

private theorem proper_kept (node : _) (shape : (site.reduce.label node).sort=.op .lam) :
    ∃ k,node=.inl k := by
  rcases node with k|node
  · exact ⟨k,rfl⟩
  · rcases node with tag|branch
    · cases tag;cases shape
    · cases branch <;> cases shape

private theorem fragment_finish {original : LTerm} {N B W : Type}
    [FiniteNames N] [FiniteNames B] [FiniteNames W]
    {g : Net signature N B W} {root : B} {edge : SourceEdge} {p : Path}
    (fragment : SourceEdgeFragment original g root edge p) :
    fragment.access.val.getLast?=some (g.wire fragment.toEndpoint) := by
  rw [fragment.literal]
  cases actual : fragment.segments with
  | nil => have h:=fragment.start;rw [actual] at h;cases h
  | cons e es => simpa only [List.getLast?_append,actual,List.getLast?_cons,Option.some_or] using fragment.finish

private theorem parent_kept : ∃(parent : RootAccess site.reduce (.inl ()))
    (port : NodePort signature presentation.Kept presentation.kept),
    accessWord site.reduce parent.val=[] ∧
    parent.val.getLast?=some (site.reduce.wire (.inl ⟨.inl port.1,port.2⟩)) := by
  obtain ⟨fragment⟩ := target_matches.base_source_edge_fragment (original:=current) closed (SourceSubterm.nil)
  have realizes : SourcePortRealizes current site.reduce (.inl ()) (.lamContext current.label) fragment.toEndpoint :=
    fragment.toRealizes
  have finish := fragment_finish fragment
  generalize endpointEq : fragment.toEndpoint=endpoint at realizes finish
  cases realizes with
  | departure lookup role => cases role
  | lamContext lookup access word shape role ending =>
    obtain ⟨k,nodeEq⟩ := proper_kept _ shape
    subst nodeEq
    exact ⟨fragment.access,⟨k,_⟩,fragment.word,finish⟩
private def bodyEdge : SourceEdge := sourceEdge [current.label] (.lamBody current.label) (.var (.atom 4) 0)
private theorem bodyOccurrence : SourceSubterm [] .external current [.body] [current.label]
    (.lamBody current.label) (.var (.atom 4) 0) := .body .nil
private theorem body_terminal_kept (fragment : SourceEdgeFragment current site.reduce (.inl ()) bodyEdge [.body]) :
    ∃port : NodePort signature presentation.Kept presentation.kept,
      fragment.access.val.getLast?=some (site.reduce.wire (.inl ⟨.inl port.1,port.2⟩)) := by
  have realizes : SourcePortRealizes current site.reduce (.inl ()) (.lamBind current.label) fragment.toEndpoint :=
    fragment.toRealizes
  have finish := fragment_finish fragment
  generalize endpointEq : fragment.toEndpoint=endpoint at realizes finish
  cases realizes with
  | departure lookup role => cases role
  | binding lookup parent word shape ctxRole bindRole ending =>
    obtain ⟨k,nodeEq⟩ := proper_kept _ shape
    subst nodeEq
    exact ⟨⟨k,_⟩,finish⟩

/-- A real third action, after the original beta/cro-lambda history. All
four pieces below are produced from actual Matches, not supplied as coverage. -/
theorem actual_kept_body_comparison :
    ∃(sourceFirst sourceSecond : SourceEdgeFragment current site.net (.inl ()) bodyEdge [.body])
      (targetFirst targetSecond : SourceEdgeFragment current site.reduce (.inl ()) bodyEdge [.body]),
      (targetFirst.segments=targetSecond.segments ↔sourceFirst.segments=sourceSecond.segments) := by
  obtain ⟨principal⟩ := site.actionPrincipal_exists
  obtain ⟨sourceFirst⟩ := source_matches.base_source_edge_fragment closed bodyOccurrence
  obtain ⟨sourceSecond⟩ := source_matches.base_source_edge_fragment closed bodyOccurrence
  obtain ⟨targetFirst⟩ := target_matches.base_source_edge_fragment closed bodyOccurrence
  obtain ⟨targetSecond⟩ := target_matches.base_source_edge_fragment closed bodyOccurrence
  obtain ⟨sourceParent,sourceWord,_⟩ := Matches.observation site.net source_matches
    (⟨[],by rfl⟩ : Position current.erase)
  obtain ⟨targetParent,parentPort,parentWord,parentEnd⟩ := parent_kept
  obtain ⟨leftEnd,leftFinish⟩ := body_terminal_kept targetFirst
  obtain ⟨rightEnd,rightFinish⟩ := body_terminal_kept targetSecond
  obtain ⟨f⟩ := flow
  refine ⟨sourceFirst,sourceSecond,targetFirst,targetSecond,?_⟩
  exact sourceFirst.unary_kept_piece_equality site (.cro .cro 0 1 (by decide))
    (by intro h;cases h) (presentation.sourceIso.flowBalance f) (.inl ()) rfl
    source_matches target_matches principal targetFirst sourceSecond targetSecond
    (show SourceDeparture current .body (.lamBody current.label) from .body)
    (show SourceDeparture current .body (.lamBody current.label) from .body) sourceParent sourceParent targetParent targetParent
    (by rw [sourceWord];rfl) (by rw [sourceWord];rfl) (by rw [parentWord];rfl) (by rw [parentWord];rfl)
    parentPort parentPort leftEnd rightEnd parentEnd parentEnd leftFinish rightFinish


theorem actual_three_rule_trace : GraphTrace (ActualNet.initial identityApp)
    (ActualNet.ofNet site.reduce) [.beta 0,continuationSchema,schema] :=
  actual_two_rule_trace.trans (.cons actual_third_step (.refl _))

/-- The literal piece-cut consumer uses the real parent and terminal, and
returns a genuine canonical piece with its actual seam assignment. -/
theorem actual_kept_body_cut : ∃principal : SiteActionPrincipal site,
    ∃(source : SourceEdgeFragment current site.net (.inl ()) bodyEdge [.body])
      (target : SourceEdgeFragment current site.reduce (.inl ()) bodyEdge [.body]), ∃pivot seam b,
      ActionCanonicalBlocks site principal
        (.inl pivot::target.segments.map
          (plugEnd (cutFragment site.net (pathPartition schema presentation.Inside) site.closed).label schema.right.net.label).invFun)
        (site.outsideEnd pivot::source.segments) ∧
      PlugLabelling (cutFragment site.net (pathPartition schema presentation.Inside) site.closed) schema.right.net
        (.inl pivot::target.segments.map
          (plugEnd (cutFragment site.net (pathPartition schema presentation.Inside) site.closed).label schema.right.net.label).invFun) seam b := by
  obtain ⟨principal⟩ := site.actionPrincipal_exists
  obtain ⟨source⟩ := source_matches.base_source_edge_fragment closed bodyOccurrence
  obtain ⟨target⟩ := target_matches.base_source_edge_fragment closed bodyOccurrence
  obtain ⟨sourceParent,sourceWord,_⟩ := Matches.observation site.net source_matches
    (⟨[],by rfl⟩ : Position current.erase)
  obtain ⟨targetParent,parentPort,parentWord,parentEnd⟩ := parent_kept
  obtain ⟨endPort,endFinish⟩ := body_terminal_kept target
  obtain ⟨a,b,labels⟩ := target.access.property.1.1
  obtain ⟨f⟩ := flow
  obtain ⟨pivot,seam,_,_,relation,pieceLabels⟩ := source.unary_kept_parent_cut site
    (.cro .cro 0 1 (by decide)) (by intro h;cases h)
    (presentation.sourceIso.flowBalance f) (.inl ()) rfl source_matches target_matches principal target
    (show SourceDeparture current .body (.lamBody current.label) from .body)
    sourceParent targetParent (by rw [sourceWord];rfl) (by rw [parentWord];rfl)
    parentPort.1 endPort.1 parentPort.2 endPort.2 parentEnd endFinish labels
  exact ⟨principal,source,target,pivot,seam,b,relation,pieceLabels⟩
end Lamping.Checks.ReachableKeptUnaryFixture
#print axioms Lamping.Checks.ReachableKeptUnaryFixture.actual_third_step
#print axioms Lamping.Checks.ReachableKeptUnaryFixture.source_matches
#print axioms Lamping.Checks.ReachableKeptUnaryFixture.target_matches
#print axioms Lamping.Checks.ReachableKeptUnaryFixture.actual_kept_body_comparison
#print axioms Lamping.Checks.ReachableKeptUnaryFixture.actual_three_rule_trace
#print axioms Lamping.Checks.ReachableKeptUnaryFixture.actual_kept_body_cut

#print axioms Lamping.AG.PathSite.action_kept_canonical_access
#print axioms Lamping.AG.SourceEdgeFragment.unary_kept_parent_cut
#print axioms Lamping.AG.SourceEdgeFragment.unary_kept_piece_equality

namespace Lamping.Checks.CopiedLambdaBodyPrefixConsumer
open AG Graph Lambda Lambda.Labelled
open ReachableUnaryFixture
local notation "cut" => cutFragment actualContinuationSite.net (pathPartition continuationSchema ContinuationV) actualContinuationSite.closed
local notation "rhs" => unaryRightCore Op.cro Op.lam (Bij.refl Unit) 0 0
private theorem closed : Closed current.erase := by change 0<1;decide
private theorem bodyOccurrence : SourceSubterm [] .external current [.body] [current.label]
    (.lamBody current.label) (.var (.atom 4) 0) := .body .nil

theorem actual_copied_lambda_body_prefix : ∃ fragment : SourceEdgeFragment current actualControlReduced (.inl ())
      (sourceEdge [current.label] (.lamBody current.label) (.var (.atom 4) 0)) [.body],
    ∃tail a b middle,fragment.segments.map (plugEnd (cut).label (rhs).label).invFun=
      .inr (.inl ⟨.inl (),.inr true⟩)::.inr (.inl ⟨.inr true,.inl ()⟩)::
        .inl (.inr (.inl (.inr (.inr true))))::tail ∧
      Traversal 0 (.op .cro) (.inr ()) (.inl ()) a middle ∧
      PlugLabelling cut rhs (.inl (.inr (.inl (.inr (.inr true))))::tail) middle b := by
  obtain ⟨parent,word,finish⟩ := actual_target_lambda_access
  obtain ⟨fragment⟩ := actual_target_matches.base_source_edge_fragment closed bodyOccurrence
  obtain ⟨a,b,labels⟩ := fragment.fragment_labels
  obtain ⟨tail,middle,literal,writer,suffix⟩ := unary_copied_lambda_body_fragment cut .cro
    (Bij.refl Unit) (Or.inl rfl) 0 0 (current:=current) actual_target_matches fragment
    (show SourceDeparture current .body (.lamBody current.label) from .body) parent
    (by change [.body]=accessWord actualControlReduced parent.val++[.body];rw [word];rfl) finish labels
  exact ⟨fragment,tail,a,b,middle,literal,writer,suffix⟩
end Lamping.Checks.CopiedLambdaBodyPrefixConsumer
#print axioms Lamping.AG.unary_copied_lambda_body_fragment
#print axioms Lamping.Checks.CopiedLambdaBodyPrefixConsumer.actual_copied_lambda_body_prefix
#print axioms Lamping.AG.unary_body_prefix
#print axioms Lamping.AG.unary_typed_body_prefix
#print axioms Lamping.AG.actual_lambda_child_head

namespace Lamping.Checks.CopiedLambdaParentCutConsumer
open AG Graph Lambda Lambda.Labelled
open ReachableUnaryFixture
local notation "cut" => cutFragment actualContinuationSite.net (pathPartition continuationSchema ContinuationV) actualContinuationSite.closed
local notation "rhs" => unaryRightCore Op.cro Op.lam (Bij.refl Unit) 0 0
private theorem closed : Closed current.erase := by change 0<1;decide
private theorem bodyOccurrence : SourceSubterm [] .external current [.body] [current.label]
    (.lamBody current.label) (.var (.atom 4) 0) := .body .nil
private theorem lambda_binding_port (node : Unit⊕(Unit⊕Bool)) (port : Port (actualControlReduced.label node).sort)
    (shape : (actualControlReduced.label node).sort=.op .lam) (role : HEq port lamBind) :
    (⟨node,port⟩ : NodePort signature _ actualControlReduced.label)=⟨.inr (.inl ()),.inr false⟩ := by
  rcases node with tag|(tag|branch)
  · cases tag;cases shape
  · cases tag
    have eq : port=lamBind := eq_of_heq role
    subst port
    rfl
  · cases branch <;> cases shape

private theorem binding_finish (fragment : SourceEdgeFragment current actualControlReduced (.inl ())
    (sourceEdge [current.label] (.lamBody current.label) (.var (.atom 4) 0)) [.body]) :
    fragment.access.val.getLast?=some (actualControlReduced.wire (.inl ⟨.inr (.inl ()),.inr false⟩)) := by
  have realizes : SourcePortRealizes current actualControlReduced (.inl ()) (.lamBind current.label) fragment.toEndpoint :=
    fragment.toRealizes
  have finish : fragment.access.val.getLast?=some (actualControlReduced.wire fragment.toEndpoint) := by
    rw [fragment.literal,List.getLast?_append,fragment.finish]
    rfl
  generalize endpointEq : fragment.toEndpoint=endpoint at realizes finish
  cases realizes with
  | departure lookup role => cases role
  | binding lookup parent word shape contextRole bindingRole ending =>
    have portEq := lambda_binding_port _ _ shape bindingRole
    rw [portEq] at finish
    exact finish

theorem actual_copied_parent_binding_cut : ∃principal : SiteActionPrincipal actualContinuationSite,
    ∃(source : SourceEdgeFragment current actualContinuationSite.net (.inl ())
      (sourceEdge [current.label] (.lamBody current.label) (.var (.atom 4) 0)) [.body])
      (target : SourceEdgeFragment current actualControlReduced (.inl ())
      (sourceEdge [current.label] (.lamBody current.label) (.var (.atom 4) 0)) [.body]),
    ∃tail oldTail seam output,
      source.segments=.inl ⟨.inr (.inr ()),.inr true⟩::oldTail ∧
      target.segments.map (plugEnd (cut).label (rhs).label).invFun=
        .inr (.inl ⟨.inl (),.inr true⟩)::.inr (.inl ⟨.inr true,.inl ()⟩)::
          .inl (.inr (.inl (.inr (.inr true))))::(tail++
            [.inr (.inr (.inl (.inr false))),.inr (.inl ⟨.inr false,.inr ()⟩)]) ∧
      ActionCanonicalBlocks actualContinuationSite principal (.inl (.inr (.inl (.inr (.inr true))))::tail) source.segments ∧
      PlugLabelling cut rhs (.inl (.inr (.inl (.inr (.inr true))))::tail) seam output := by
  obtain ⟨principal⟩ := actualContinuationSite.actionPrincipal_exists
  obtain ⟨sourceParent,sourceWord,sourceFinish⟩ := actual_source_lambda_access
  obtain ⟨targetParent,targetWord,targetFinish⟩ := actual_target_lambda_access
  obtain ⟨source⟩ := actual_source_matches.base_source_edge_fragment closed bodyOccurrence
  obtain ⟨target⟩ := actual_target_matches.base_source_edge_fragment closed bodyOccurrence
  obtain ⟨a,b,labels⟩ := target.access.property.1.1
  obtain ⟨flow⟩ := actualBetaSite.reduce_flowBalance SoundnessBetaAncestor.actualFlow
  obtain ⟨tail,oldTail,seam,output,sourcePiece,targetPiece,relation,pieceLabels⟩ :=
    source.cro_copied_binding_piece_cut actualContinuationSite (actualContinuationIso.flowBalance flow) (.inl ()) rfl (current:=current)
      actual_source_matches actual_target_matches principal target
      (show SourceDeparture current .body (.lamBody current.label) from .body) sourceParent targetParent
      (by rw [sourceWord];rfl) (by change [.body]=accessWord actualControlReduced targetParent.val++[.body];rw [targetWord];rfl) targetFinish (binding_finish target) labels
  exact ⟨principal,source,target,tail,oldTail,seam,output,sourcePiece,targetPiece,relation,pieceLabels⟩
end Lamping.Checks.CopiedLambdaParentCutConsumer
#print axioms Lamping.Checks.CopiedLambdaParentCutConsumer.actual_copied_parent_binding_cut
#print axioms Lamping.AG.Labelling.lambda_body_padding_parent
#print axioms Lamping.AG.PathSite.cro_lambda_padding_labels
#print axioms Lamping.AG.PathSite.bra_lambda_padding_labels
#print axioms Lamping.AG.SourceEdgeFragment.cro_copied_binding_piece_cut
#print axioms Lamping.AG.SourceEdgeFragment.bra_copied_binding_piece_cut

namespace Lamping.Checks.CopiedBindingComparisonConsumer
open AG Graph Lambda Lambda.Labelled
open ReachableUnaryFixture
local notation "cut" => cutFragment actualContinuationSite.net (pathPartition continuationSchema ContinuationV) actualContinuationSite.closed
local notation "rhs" => unaryRightCore Op.cro Op.lam (Bij.refl Unit) 0 0
private theorem closed : Closed current.erase := by change 0<1;decide
private theorem bodyOccurrence : SourceSubterm [] .external current [.body] [current.label]
    (.lamBody current.label) (.var (.atom 4) 0) := .body .nil
private theorem lambda_binding_port (node : Unit⊕(Unit⊕Bool)) (port : Port (actualControlReduced.label node).sort)
    (shape : (actualControlReduced.label node).sort=.op .lam) (role : HEq port lamBind) :
    (⟨node,port⟩ : NodePort signature _ actualControlReduced.label)=⟨.inr (.inl ()),.inr false⟩ := by
  rcases node with tag|(tag|branch)
  · cases tag;cases shape
  · cases tag
    have eq : port=lamBind := eq_of_heq role
    subst port
    rfl
  · cases branch <;> cases shape

private theorem binding_finish (fragment : SourceEdgeFragment current actualControlReduced (.inl ())
    (sourceEdge [current.label] (.lamBody current.label) (.var (.atom 4) 0)) [.body]) :
    fragment.access.val.getLast?=some (actualControlReduced.wire (.inl ⟨.inr (.inl ()),.inr false⟩)) := by
  have realizes : SourcePortRealizes current actualControlReduced (.inl ()) (.lamBind current.label) fragment.toEndpoint :=
    fragment.toRealizes
  have finish : fragment.access.val.getLast?=some (actualControlReduced.wire fragment.toEndpoint) := by
    rw [fragment.literal,List.getLast?_append,fragment.finish]
    rfl
  generalize endpointEq : fragment.toEndpoint=endpoint at realizes finish
  cases realizes with
  | departure lookup role => cases role
  | binding lookup parent word shape contextRole bindingRole ending =>
    have portEq := lambda_binding_port _ _ shape bindingRole
    rw [portEq] at finish
    exact finish

theorem actual_copied_binding_piece_equality :
    ∃(sourceFirst sourceSecond : SourceEdgeFragment current actualContinuationSite.net (.inl ())
      (sourceEdge [current.label] (.lamBody current.label) (.var (.atom 4) 0)) [.body])
      (targetFirst targetSecond : SourceEdgeFragment current actualControlReduced (.inl ())
      (sourceEdge [current.label] (.lamBody current.label) (.var (.atom 4) 0)) [.body]),
      (targetFirst.segments=targetSecond.segments ↔sourceFirst.segments=sourceSecond.segments) := by
  obtain ⟨principal⟩ := actualContinuationSite.actionPrincipal_exists
  obtain ⟨sourceParent,sourceWord,_sourceFinish⟩ := actual_source_lambda_access
  obtain ⟨targetParent,targetWord,targetFinish⟩ := actual_target_lambda_access
  obtain ⟨sourceFirst⟩ := actual_source_matches.base_source_edge_fragment closed bodyOccurrence
  obtain ⟨sourceSecond⟩ := actual_source_matches.base_source_edge_fragment closed bodyOccurrence
  obtain ⟨targetFirst⟩ := actual_target_matches.base_source_edge_fragment closed bodyOccurrence
  obtain ⟨targetSecond⟩ := actual_target_matches.base_source_edge_fragment closed bodyOccurrence
  obtain ⟨flow⟩ := actualBetaSite.reduce_flowBalance SoundnessBetaAncestor.actualFlow
  refine ⟨sourceFirst,sourceSecond,targetFirst,targetSecond,?_⟩
  exact sourceFirst.cro_copied_binding_piece_equality actualContinuationSite (actualContinuationIso.flowBalance flow)
    (.inl ()) rfl (current:=current) actual_source_matches actual_target_matches principal
    targetFirst sourceSecond targetSecond
    (show SourceDeparture current .body (.lamBody current.label) from .body)
    (show SourceDeparture current .body (.lamBody current.label) from .body)
    sourceParent sourceParent targetParent targetParent
    (by rw [sourceWord];rfl) (by rw [sourceWord];rfl)
    (by change [.body]=accessWord actualControlReduced targetParent.val++[.body];rw [targetWord];rfl)
    (by change [.body]=accessWord actualControlReduced targetParent.val++[.body];rw [targetWord];rfl)
    targetFinish targetFinish (binding_finish targetFirst) (binding_finish targetSecond)
end Lamping.Checks.CopiedBindingComparisonConsumer
#print axioms Lamping.AG.SourceEdgeFragment.cro_copied_binding_piece_equality
#print axioms Lamping.AG.SourceEdgeFragment.bra_copied_binding_piece_equality
#print axioms Lamping.Checks.CopiedBindingComparisonConsumer.actual_copied_binding_piece_equality