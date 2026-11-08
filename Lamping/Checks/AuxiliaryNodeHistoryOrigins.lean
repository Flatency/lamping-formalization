import Lamping.Lambda.AuxiliaryNodeHistoryOrigins
import Lamping.Checks.NodeLabelSuffixOrigins
import Lamping.Lambda.BetaIncidencePreimages
namespace Lamping.Checks.AuxiliaryNodeHistoryOriginsChecks
open Lambda Lambda.Labelled
open NodeLabelSuffixOriginsChecks

theorem actual_created_aux_origin : ∃old,
    source.subterm [.arg,.arg]=some old ∧AuxiliaryAt source [.arg,.arg] :=
  actualStep.auxiliary_node_origin redex_lookup actualOrigin actual_lookup actual_auxiliary

-- Two actual steps, with different degrees allowed: no uniform/freshness
-- assumption is smuggled into the generic operational ancestry theorem.
abbrev final : LTerm := WrappedSuccessfulChains.contractRoot target
def secondStep : StepAt [] target final := .root _ _ _ _
def twoLabels : History [[.arg],[]] source final :=
  .cons actualStep (.cons secondStep (.nil _))
def trace : BetaNodeHistoryPreimage twoLabels [] [.arg,.arg] := by
  apply BetaNodeHistoryPreimage.one (step:=actualStep) redex_lookup actualOrigin
  exact BetaNodeHistoryPreimage.one (step:=secondStep)
    (show target.subterm []=some (.app (.atom 0) (.lam (.atom 1) (.var (.atom 2) 0)) currentArgument) from rfl)
    (BetaNodePreimage.copied (q:=[]) (relative:=[]) (old:=currentArgument) (by rfl) (by rfl)) (.nil _ _)

theorem final_auxiliary : AuxiliaryAt final [] := by
  constructor
  · rintro ⟨parent,stamp,fn,arg,split,lookup⟩
    have lengths:=congrArg List.length split
    simp at lengths
  · rintro ⟨stamp,body,lookup⟩
    cases lookup

theorem actual_history_aux_origin : ∃old,
    source.subterm [.arg,.arg]=some old ∧AuxiliaryAt source [.arg,.arg] :=
  trace.auxiliary_source (current:=final) rfl final_auxiliary

-- The edge origin does NOT map the created edge's SOURCE incidence.
-- In the target, ARG starts at outer APP[]; its old ARG/ARG starts at
-- the old beta APP[arg]. Both are genuine proper syntax occurrences.
def currentOuter : SyntaxIncidence.ProperPosition target :=
  ⟨[],Or.inl ⟨.atom 0,.lam (.atom 1) (.var (.atom 2) 0),currentArgument,rfl⟩⟩
def oldInner : SyntaxIncidence.ProperPosition source :=
  ⟨[.arg],Or.inl ⟨.atom 3,.lam (.atom 4) (.var (.atom 5) 0),argumentTerm,rfl⟩⟩

theorem target_source_endpoint : SyntaxIncidence.Source target [.arg] (some currentOuter) :=
  ⟨.arg,target,.appArg (.atom 0),rfl,rfl,.arg⟩
theorem old_source_endpoint : SyntaxIncidence.Source source [.arg,.arg] (some oldInner) :=
  ⟨.arg,.app (.atom 3) (.lam (.atom 4) (.var (.atom 5) 0)) argumentTerm,
    .appArg (.atom 3),rfl,rfl,.arg⟩

theorem no_created_source_incidence_map :
    ¬BetaVertexPreimage (.var (.atom 5) 0) argumentTerm [.arg] source target
      (some currentOuter) (some oldInner) := by
  intro alleged
  cases alleged with
  | proper origin =>
    have outside : BetaNodePreimage (.var (.atom 5) 0) argumentTerm [.arg] [] [] :=
      .context (by rintro ⟨rest,impossible⟩;cases impossible)
    have same := origin.unique outside
    cases same

-- The negative incidence boundary is not caused by missing successful
-- endpoint chains, and uses the same original INIT and actual beta history.
def old_inner_chain : PrerequisiteChain source [.arg] [[.arg,.fn]] := .redex_app redex_lookup
#print axioms initial
#print axioms actualHistory
#print axioms actual_created_aux_origin
#print axioms trace
#print axioms actual_history_aux_origin
#print axioms target_source_endpoint
#print axioms old_source_endpoint
#print axioms no_created_source_incidence_map
#print axioms actual_source_endpoint_chain
#print axioms actual_target_endpoint_chain
#print axioms old_inner_chain
end Lamping.Checks.AuxiliaryNodeHistoryOriginsChecks
