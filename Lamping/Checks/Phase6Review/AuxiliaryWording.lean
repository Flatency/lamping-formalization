import Lamping.Lambda.PrerequisiteChains
namespace Lamping.Checks.Phase6Review.AuxiliaryWording
open Lambda Lambda.Labelled

def original : LTerm := initLabels (.app (.lam (.var 0)) (.lam (.var 0)))
def argumentEdge : SourceEdge := ⟨.atom 3,.appArg (.atom 0),.lamContext (.atom 3)⟩

def LiteralPrintedOr (edge : SourceEdge) : Prop :=
  (¬∃ origin,edge.fromPort=.appFn origin) ∨ (¬∃ origin,edge.toPort=.lamContext origin)
def EdgeEligible (edge : SourceEdge) : Prop :=
  (∃ origin,edge.fromPort=.appFn origin) ∨ (∃ origin,edge.toPort=.lamContext origin)
def CandidateAnd (edge : SourceEdge) : Prop :=
  (¬∃ origin,edge.fromPort=.appFn origin) ∧ (¬∃ origin,edge.toPort=.lamContext origin)

theorem actual_closed : Closed original.erase := by change (0<1) ∧ 0<1;decide

theorem actual_argument_chain : PrerequisiteChain original [.arg] [[.arg],[.fn]] :=
  .lam (parent:=[]) (step:=.arg) rfl (by decide) (.redex_app rfl)

theorem actual_source_edge : argumentEdge∈sourceEdges [] .external original := by decide

theorem printed_or_on_actual_chain_edge :
    PrerequisiteChain original [.arg] [[.arg],[.fn]] ∧
    ([.arg] : Path)∈[[.arg],[.fn]] ∧
    argumentEdge∈sourceEdges [] .external original ∧
    argumentEdge.fromPort=.appArg (.atom 0) ∧
    argumentEdge.toPort=.lamContext (.atom 3) ∧ LiteralPrintedOr argumentEdge := by
  refine ⟨actual_argument_chain,by simp,actual_source_edge,rfl,rfl,Or.inl ?_⟩
  rintro ⟨origin,impossible⟩
  cases impossible

theorem literal_never_aux_fails_on_argument :
    ¬(PrerequisiteChain original [.arg] [[.arg],[.fn]] → ¬LiteralPrintedOr argumentEdge) := by
  intro never
  exact never actual_argument_chain printed_or_on_actual_chain_edge.2.2.2.2.2

/-- Only a logical candidate: this does not change any production definition
or approve an erratum to AG's printed auxiliary wording. -/
theorem candidate_and_is_eligible_complement (edge : SourceEdge) :
    CandidateAnd edge ↔ ¬EdgeEligible edge := by
  simp only [CandidateAnd,EdgeEligible,not_or]

theorem candidate_does_not_mark_argument_edge : ¬CandidateAnd argumentEdge := by
  intro both
  exact both.2 ⟨.atom 3,rfl⟩

#print axioms actual_argument_chain
#print axioms actual_source_edge
#print axioms printed_or_on_actual_chain_edge
#print axioms literal_never_aux_fails_on_argument
#print axioms candidate_and_is_eligible_complement
theorem actual_init_closed_chain_conflict :
    INIT original ∧ Closed original.erase ∧
    PrerequisiteChain original [.arg] [[.arg],[.fn]] ∧
    argumentEdge∈sourceEdges [] .external original ∧
    LiteralPrintedOr argumentEdge := by
  exact ⟨init_is_INIT _,actual_closed,actual_argument_chain,actual_source_edge,
    printed_or_on_actual_chain_edge.2.2.2.2.2⟩
#print axioms actual_init_closed_chain_conflict
end Lamping.Checks.Phase6Review.AuxiliaryWording

