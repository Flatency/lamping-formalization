import Lamping.Lamping.ChainReadPredicateIso
import Lamping.Checks.SafeReadSourceEndpointIso
namespace Lamping.Checks.ChainReadPredicateIsoChecks
open Lambda Lambda.Labelled AG
namespace Distinct
open SafeReadSourceEndpointIsoChecks

theorem actual_distinct_selected_preimage :
    ∃edge node,edge∈[left++[.fn]] ∧target.subterm edge=some node ∧
      node.label=leaf.label ∧edge≠right++[.fn] := by
  obtain ⟨iso⟩ := currentIso
  obtain ⟨edge,node,member,lookup,same⟩ := iso.read_label_preimage
    (edge:=right++[.fn]) (node:=leaf) (by simp) rfl
  have equal:=List.mem_singleton.mp member
  exact ⟨edge,node,member,lookup,same,equal ▸ (by decide)⟩

theorem actual_safe_read_transfer (edge : Path) (member : edge∈[right++[.fn]])
    (node : LTerm) (lookup : target.subterm edge=some node) :
    node.label.OuterBarsSafe (fun x=>x≠Label.atom 7) := by
  obtain ⟨iso⟩ := currentIso
  exact (iso.read_predicate_iff (fun label=>label.OuterBarsSafe (fun x=>x≠Label.atom 7))).mp
    leftReadSafe edge member node lookup
end Distinct

namespace Marked
abbrev I : Term := WrappedSuccessfulChains.I
abbrev source : LTerm := initLabels (.app (.app I I) I)
abbrev argument : LTerm := .lam (.atom 4) (.var (.atom 5) 0)
abbrev result : LTerm := LTerm.contract (.atom 1) (.atom 2) (.var (.atom 3) 0) argument
abbrev target : LTerm := .app (.atom 0) result (.lam (.atom 6) (.var (.atom 7) 0))
def step : StepAt [.fn] source target := .fn (.root _ _ _ _)
def history : History [[.fn]] source target := .cons step (.nil _)
theorem closed : Closed source.erase := by change (0<1 ∧0<1) ∧0<1;decide
theorem targetClosed : Closed target.erase := history.closed closed
theorem currentMarked : ¬result.label.OuterBarsSafe (fun x=>x≠Label.atom 2) :=
  step.created_label_not_safe (by rfl) (current:=result) rfl (Or.inl rfl)

/-- Two genuine successful starts may use the same selected edge graph.
Only their label properties are compared, with no reading direction claim. -/
theorem actual_marked_read_property_transfer :
    INIT source ∧History [[.fn]] source target ∧
    PrerequisiteChain target [] [[.fn]] ∧
    PrerequisiteChain target [.fn] [[.fn]] ∧
    ¬(∀edge∈([[.fn]] : List Path),∀node,target.subterm edge=some node →
      node.label.OuterBarsSafe (fun x=>x≠Label.atom 2)) ∧
    ((∀edge∈([[.fn]] : List Path),∀node,target.subterm edge=some node →
      node.label.OuterBarsSafe (fun x=>x≠Label.atom 2)) ↔
     (∀edge∈([[.fn]] : List Path),∀node,target.subterm edge=some node →
      node.label.OuterBarsSafe (fun x=>x≠Label.atom 2))) := by
  refine ⟨init_is_INIT _,history,.redex_app rfl,?_,?_,?_⟩
  · change PrerequisiteChain target ([]++[.fn]) [[]++[.fn]]
    exact .redex_lam rfl
  · intro all
    exact currentMarked (all [.fn] (by simp) result rfl)
  · exact (ChainIncidenceIso.refl (chainSyntaxIncidence target targetClosed [[.fn]])).read_predicate_iff _
end Marked

#print axioms ChainIncidenceIso.read_predicate_iff
#print axioms Distinct.actual_distinct_selected_preimage
#print axioms Distinct.actual_safe_read_transfer
#print axioms Marked.actual_marked_read_property_transfer
end Lamping.Checks.ChainReadPredicateIsoChecks
