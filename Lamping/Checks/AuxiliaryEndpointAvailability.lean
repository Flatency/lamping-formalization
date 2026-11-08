import Lamping.Lamping.AuxiliaryEndpointAvailability
import Lamping.Checks.AuxiliaryNodeHistoryOrigins
namespace Lamping.Checks.AuxiliaryEndpointAvailabilityChecks
open Lambda Lambda.Labelled AG
open NodeLabelSuffixOriginsChecks AuxiliaryNodeHistoryOriginsChecks

def currentInner : SyntaxIncidence.ProperPosition target :=
  ⟨[.arg],Or.inl ⟨currentArgument.label,.lam (.atom 7) (.var (.atom 8) 0),
    .lam (.atom 9) (.var (.atom 10) 0),rfl⟩⟩
def oldArgument : SyntaxIncidence.ProperPosition source :=
  ⟨[.arg,.arg],Or.inl ⟨.atom 6,.lam (.atom 7) (.var (.atom 8) 0),
    .lam (.atom 9) (.var (.atom 10) 0),rfl⟩⟩

theorem current_target_endpoint : SyntaxIncidence.Target target [.arg] (some currentInner) := Or.inl rfl
theorem old_target_endpoint : SyntaxIncidence.Target source [.arg,.arg] (some oldArgument) := Or.inl rfl

theorem actual_vertex_availability : ∃es,EndpointChain source (some oldArgument) es :=
  endpoint_available_at_beta_preimage actualStep redex_lookup
    (BetaVertexPreimage.proper actualOrigin)
    (show EndpointChain target (some currentInner) [[.arg,.fn]] from actual_target_endpoint_chain)

-- The general theorem supplies this result. Source/Target uniqueness and
-- real chain uniqueness identify the two actual old lists, not label matching.
theorem actual_created_availability :
    ∃es fs,EndpointChain source (some oldInner) es ∧
      EndpointChain source (some oldArgument) fs ∧
      es=[[.arg,.fn]] ∧fs=[[.arg,.arg,.fn]] := by
  obtain ⟨oldFrom,oldTo,es,fs,fromSpec,toSpec,fromChain,toChain⟩ :=
    old_edge_endpoint_availability actualStep redex_lookup actualOrigin actual_lookup
      target_source_endpoint current_target_endpoint
      (show EndpointChain target (some currentOuter) [[.fn]] from actual_source_endpoint_chain)
      (show EndpointChain target (some currentInner) [[.arg,.fn]] from actual_target_endpoint_chain)
  have fromEq := SyntaxIncidence.Source.unique fromSpec old_source_endpoint
  have toEq := SyntaxIncidence.Target.unique toSpec old_target_endpoint
  have fromActual : EndpointChain source (some oldInner) es := fromEq ▸ fromChain
  have toActual : EndpointChain source (some oldArgument) fs := toEq ▸ toChain
  exact ⟨es,fs,fromActual,toActual,EndpointChain.unique fromActual old_inner_chain,
    EndpointChain.unique toActual (PrerequisiteChain.redex_app (by rfl))⟩

-- Genuine uncreated FUNCTION edge, with both endpoints already successful.
def currentFunction : SyntaxIncidence.ProperPosition target :=
  ⟨[.fn],Or.inr ⟨.atom 1,.var (.atom 2) 0,rfl⟩⟩
def oldFunction : SyntaxIncidence.ProperPosition source :=
  ⟨[.fn],Or.inr ⟨.atom 1,.var (.atom 2) 0,rfl⟩⟩
def functionOrigin : BetaNodePreimage (.var (.atom 5) 0) argumentTerm [.arg] [.fn] [.fn] :=
  .context (by rintro ⟨rest,impossible⟩;cases impossible)

theorem actual_uncreated_availability :
    ∃oldFrom oldTo es fs,SyntaxIncidence.Source source [.fn] oldFrom ∧
      SyntaxIncidence.Target source [.fn] oldTo ∧
      EndpointChain source oldFrom es ∧EndpointChain source oldTo fs :=
  old_edge_endpoint_availability actualStep redex_lookup functionOrigin (current:=.lam (.atom 1) (.var (.atom 2) 0)) rfl
    (fromVertex:=some currentOuter) (toVertex:=some currentFunction)
    ⟨.fn,target,.appFn (.atom 0),rfl,rfl,.fn⟩ (Or.inl rfl)
    (show EndpointChain target (some currentOuter) [[.fn]] from actual_source_endpoint_chain)
    (by change PrerequisiteChain target ([]++[.fn]) [[]++[.fn]];exact PrerequisiteChain.redex_lam (by rfl))

theorem external_never_successful (es : List Path) : ¬EndpointChain target none es := by
  intro impossible;exact impossible
#print axioms initial
#print axioms actualHistory
#print axioms actual_vertex_availability
#print axioms actual_created_availability
#print axioms actual_uncreated_availability
#print axioms no_created_source_incidence_map
#print axioms external_never_successful
end Lamping.Checks.AuxiliaryEndpointAvailabilityChecks
