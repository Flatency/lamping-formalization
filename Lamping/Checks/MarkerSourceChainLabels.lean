import Lamping.Lambda.MarkerSourceChainLabels
import Lamping.Checks.ActualUnsafeMarkerLeaves
import Lamping.Checks.DirectedMarkerLeafTails
namespace Lamping.Checks.MarkerSourceChainLabelsChecks
open Lambda Lambda.Labelled AG
namespace Nonterminal
open ActualUnsafeMarkerLeavesChecks.Nonterminal

/-- The actual degree-marked NONterminal cut producer is consumed directly.
Both current chains are the same genuine chain; no distinct-chain claim. -/
theorem actual_cut_source_chains :
    ∃ leftStart rightStart leftEdges rightEdges,
      PrerequisiteChain source leftStart leftEdges ∧PrerequisiteChain source rightStart rightEdges ∧
      leftEdges.map source.labelAt=rightEdges.map source.labelAt := by
  obtain ⟨left,right,lb,rb,le,re,la,ra,direction,_,_⟩ := actual_nonterminal_leaves
  have before : left.before.map current.labelAt=right.before.map current.labelAt := by rw [lb,rb]
  have nodes : left.node=right.node := by
    apply Option.some.inj
    have l:=left.lookup;have r:=right.lookup
    rw [le] at l;rw [re] at r
    exact l.symm.trans r
  have rightSpine : DirectedMarkerSpine F source (.atom 4) left.forward [[.arg]] current
      (right.before.map current.labelAt) right.edge := by
    rw [direction];exact right.spine
  obtain ⟨ls,rs,_,labels⟩ := left.spine.compare_source_chain_outputs rightSpine selected
    (initial.outerBarsSafe _) left.lookup right.lookup before (by rw [nodes])
  exact ⟨ls.start,rs.start,ls.edges,rs.edges,ls.chain,rs.chain,labels⟩

/-- The first unsafe edge has a true remaining FN edge; this is not the
terminal opposite-sign exception. -/
theorem actual_nonempty_tail :
    INIT source ∧History [[.arg]] source current ∧
    PrerequisiteChain current [.arg] [[.arg],[.fn]] ∧
    ¬degreeReadSafe (.atom 4) (current.labelAt [.arg]) :=
  ⟨initial,labels,chain,marked⟩
end Nonterminal

namespace Distinct
open UniformOldCreatedIncomingLabelsChecks.Distinct

def leftSpine : DirectedMarkerSpine F source (.atom 7) false [left,right] target [] left :=
  old.directed_marker_spine labels selected source_safe (start:=left) (before:=[]) .refl
    ⟨Or.inr ⟨_,_,rfl,rfl⟩,rfl⟩ rfl marked (by intro e member;cases member)

def rightSpine : DirectedMarkerSpine F source (.atom 7) false [left,right] target [] right :=
  old.directed_marker_spine labels selected source_safe (start:=right) (before:=[]) .refl
    SelectedOldOtherLastOriginsChecks.actual_reading rfl marked (by intro e member;cases member)

/-- Two distinct CURRENT marked occurrences, with the same real nonINIT OLD
source and nonempty prefix history. Output source chains are derived, not given. -/
theorem actual_distinct_current_source_chains :
    ∃ ls rs : MarkerSourceChain F source (.atom 7) false [] (leftNode.label.readLetters false),
      ls.firstNode.label=rs.firstNode.label ∧ls.edges.map source.labelAt=rs.edges.map source.labelAt :=
  leftSpine.compare_source_chain_outputs rightSpine selected source_safe rfl rfl rfl rfl

theorem actual_original_init_and_prior :
    INIT original ∧History [[]] original source ∧History [left,right] source target ∧
    left≠right ∧target.subterm left=some leftNode ∧target.subterm right=some leftNode :=
  ⟨initial,globalHistory,labels,by decide,rfl,rfl⟩
end Distinct

namespace Terminal
open DirectedReadingDecompositionChecks
/-- The terminal two directions have different complete words. The comparison
API needs the same actual sign and cannot identify these two words. -/
theorem opposite_sign_words :
    PrerequisiteReadsDirected target [] [.fn] true ∧
    PrerequisiteReadsDirected target [.fn] [.fn] false ∧
    result.label.readLetters true≠result.label.readLetters false :=
  ⟨⟨Or.inl ⟨_,_,_,rfl,rfl⟩,rfl⟩,⟨Or.inr ⟨_,_,rfl,rfl⟩,rfl⟩,by decide⟩
end Terminal

#print axioms Nonterminal.actual_cut_source_chains
#print axioms Nonterminal.actual_nonempty_tail
#print axioms Distinct.leftSpine
#print axioms Distinct.rightSpine
#print axioms Distinct.actual_distinct_current_source_chains
#print axioms Distinct.actual_original_init_and_prior
#print axioms Terminal.opposite_sign_words
end Lamping.Checks.MarkerSourceChainLabelsChecks
