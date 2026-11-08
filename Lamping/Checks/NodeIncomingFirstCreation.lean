import Lamping.Lambda.UncreatedSourceHistory
import Lamping.Checks.UniformOldCreatedIncomingLabels
namespace Lamping.Checks.NodeIncomingFirstCreationChecks
open Lambda Lambda.Labelled
namespace Distinct
open UniformOldCreatedIncomingLabelsChecks.Distinct
abbrev preLabels : History [left] source middle := .cons firstStep (.nil _)

def prefixUncreated : UncreatedNodeHistoryPreimage preLabels oldRight oldRight :=
  .one (step:=firstStep) (by rfl)
    (.context (by rintro ⟨rest,impossible⟩;cases impossible))
    (by intro created;rcases betaCreatedIncoming_iff.mp created with impossible |⟨q,occurs,impossible⟩ <;> cases impossible) (.nil _ _)

def rightFirst : NodeIncomingFirstCreation labels right oldRight [left] right [] :=
  .later (step:=firstStep) (by rfl)
    (.context (by rintro ⟨rest,impossible⟩;cases impossible))
    (by intro created;rcases betaCreatedIncoming_iff.mp created with impossible |⟨q,occurs,impossible⟩ <;> cases impossible)
    (.here (step:=secondStep) (by rfl)
      (.copied (q:=[]) (relative:=[]) (old:=oldArgument) (by rfl) (by rfl))
      (Or.inl rfl) (.nil _ _))

def leftFirst : NodeIncomingFirstCreation labels left oldLeft [] left [right] :=
  .here (step:=firstStep) (by rfl)
    (.copied (q:=[]) (relative:=[]) (old:=oldArgument) (by rfl) (by rfl))
    (Or.inl rfl)
    (.one (step:=secondStep) (by rfl)
      (.context (by rintro ⟨rest,impossible⟩;cases impossible)) (.nil _ _))

-- The computed partition cannot stop at an all-uncreated answer on this
-- real marked lineage: the original label9 is safe, so source_label refutes it.
theorem automatic_right_creation : ∃pre site post,
    NodeIncomingFirstCreation labels right oldRight pre site post := by
  obtain ⟨old,lookup,partition⟩ := rightTrace.incoming_partition_at_lookup (current:=leftNode) (by rfl)
  rcases partition with all |first
  · obtain ⟨original,atOriginal,same⟩ := all.source_label (current:=leftNode) (by rfl)
    have fixed : original=oldArgument := Option.some.inj (atOriginal.symm.trans (by rfl))
    subst original
    have safe : oldArgument.label.OuterBarsSafe (fun x=>x≠Label.atom 7) := by trivial
    exact False.elim (marked (same ▸ safe))
  · exact first

theorem nonempty_before_actual_split :
    [left,right]=[left]++right::[] ∧
    ∃before after bp ap body argument beta alpha,
      ∃earlierLabels : History [left] source before,∃_step : StepAt right before after,
      ∃suffix : History [] after target,
        before.subterm right=some (.app beta (.lam alpha body) argument) ∧
        UncreatedNodeHistoryPreimage earlierLabels bp oldRight ∧
        BetaNodePreimage body argument right ap bp ∧BetaCreatedIncoming body right ap ∧
        BetaNodeHistoryPreimage suffix right ap := rightFirst.split

-- The first beta elsewhere creates a degree7 marker in the intermediate
-- WHOLE term, yet THIS oldRight incoming lineage is genuinely uncreated.
def middleParent : SyntaxIncidence.ProperPosition middle :=
  ⟨right,Or.inl ⟨.atom 6,.lam (.atom 7) (.var (.atom 8) 0),oldArgument,rfl⟩⟩
def sourceParent : SyntaxIncidence.ProperPosition source :=
  ⟨right,Or.inl ⟨.atom 6,.lam (.atom 7) (.var (.atom 8) 0),oldArgument,rfl⟩⟩
theorem midSource : SyntaxIncidence.Source middle oldRight (some middleParent) :=
  ⟨.arg,.app (.atom 6) (.lam (.atom 7) (.var (.atom 8) 0)) oldArgument,.appArg (.atom 6),rfl,rfl,.arg⟩
theorem oldSource : SyntaxIncidence.Source source oldRight (some sourceParent) :=
  ⟨.arg,.app (.atom 6) (.lam (.atom 7) (.var (.atom 8) 0)) oldArgument,.appArg (.atom 6),rfl,rfl,.arg⟩

theorem actual_source_history :
    ∃old,source.subterm oldRight=some old ∧old.label=oldArgument.label ∧
      BetaVertexHistoryPreimage preLabels (some middleParent) (some sourceParent) := by
  obtain ⟨old,vertex,lookup,same,endpoint,trace⟩ :=
    prefixUncreated.source_history (current:=oldArgument) (by rfl) midSource
  have vertexEq:=SyntaxIncidence.Source.unique endpoint oldSource
  exact ⟨old,lookup,same,vertexEq ▸ trace⟩

theorem actual_local_label : ∃old,source.subterm oldRight=some old ∧old.label=oldArgument.label :=
  prefixUncreated.source_label (current:=oldArgument) (by rfl)

def rootUncreated : UncreatedNodeHistoryPreimage preLabels [] [] :=
  .one (step:=firstStep) (by rfl)
    (.context (by rintro ⟨rest,impossible⟩;cases impossible))
    (by intro created;rcases betaCreatedIncoming_iff.mp created with impossible |⟨q,occurs,impossible⟩ <;> cases impossible) (.nil _ _)

theorem boundary_none_stays_none : ∃old,source.subterm []=some old ∧
    BetaVertexHistoryPreimage preLabels none none := by
  obtain ⟨old,vertex,lookup,same,endpoint,trace⟩ :=
    rootUncreated.source_history (current:=middle) (by rfl) (vertex:=none) (by rfl)
  have vertexEq:=SyntaxIncidence.Source.unique endpoint (show SyntaxIncidence.Source source [] none from rfl)
  exact ⟨old,lookup,vertexEq ▸ trace⟩

#print axioms initial
#print axioms globalHistory
#print axioms automatic_right_creation
#print axioms nonempty_before_actual_split
#print axioms actual_source_history
#print axioms actual_local_label
#print axioms boundary_none_stays_none
#print axioms leftFirst
#print axioms unsafe_middle
end Distinct
namespace Retained
open NodeLabelSuffixOriginsChecks
abbrev labels : History [[]] retainedSource retainedTarget := .cons retainedStep (.nil _)
def body_first : NodeIncomingFirstCreation labels [] [.fn,.body] [] [] [] :=
  .here (step:=retainedStep) (by rfl) retainedOrigin (Or.inl rfl) (.nil _ _)
#print axioms body_first
end Retained
namespace Overlap
open NodeLabelSuffixOriginsChecks
def root_copy_first : NodeIncomingFirstCreation actualHistory [.arg] [.arg,.arg] [] [.arg] [] :=
  .here (step:=actualStep) redex_lookup actualOrigin (Or.inl rfl) (.nil _ _)
#print axioms root_copy_first
#print axioms actual_overlap_word
end Overlap
end Lamping.Checks.NodeIncomingFirstCreationChecks
