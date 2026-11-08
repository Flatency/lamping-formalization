import Lamping.Lamping.MarkerSourceChainRepresentation
import Lamping.Lamping.InitialJointRepresentation
import Lamping.Checks.MarkerSourceChainLabels
namespace Lamping.Checks.MarkerSourceChainRepresentationChecks
open Graph Lambda Lambda.Labelled AG
namespace Nonterminal
open ActualUnsafeMarkerLeavesChecks.Nonterminal

private theorem actual_source_outputs :
    ∃ forward beforeLabels word, ∃ left right : MarkerSourceChain F source (.atom 4) forward beforeLabels word,
      left.edges.map source.labelAt=right.edges.map source.labelAt := by
  obtain ⟨left,right,lb,rb,le,re,la,ra,direction,_,_⟩ := actual_nonterminal_leaves
  have before : left.before.map current.labelAt=right.before.map current.labelAt := by rw [lb,rb]
  have nodes : left.node=right.node := by
    apply Option.some.inj
    have l:=left.lookup;have r:=right.lookup
    rw [le] at l;rw [re] at r
    exact l.symm.trans r
  have rightSpine : DirectedMarkerSpine F source (.atom 4) left.forward [[.arg]] current
      (left.before.map current.labelAt) right.edge := by
    rw [before,direction];exact right.spine
  have rightLookup : current.subterm right.edge=some left.node :=
    right.lookup.trans (congrArg some nodes.symm)
  obtain ⟨ls,rs,_,labels⟩ := left.spine.compare_source_chain_outputs rightSpine selected
    (initial.outerBarsSafe _) left.lookup rightLookup rfl rfl
  exact ⟨left.forward,_,_,ls,rs,labels⟩

/-- Source REP is produced by the actual canonical initial encoding.
The degree-marked nonterminal cut produces both source chains internally. -/
theorem actual_initial_source_selected_blocks :
    ∃ forward beforeLabels word, ∃ left right : MarkerSourceChain F source (.atom 4) forward beforeLabels word,
    ∃ selection : OccurrenceFragmentSelection source (encode 0 source.erase).net (.inl ()),
      JointRepresentation sourceClosed selection ∧SameChainRepresentation selection left.chain right.chain ∧
      ∃ lp rp : Position source.erase,
        lp.val=left.selectedName++[.fn] ∧rp.val=right.selectedName++[.fn] ∧
        (selection lp).fragment.segments=(selection rp).fragment.segments := by
  obtain ⟨forward,beforeLabels,word,left,right,_⟩ := actual_source_outputs
  obtain ⟨selection,joint⟩ := encode_initial_joint_realization source sourceClosed initial 0
  have whole := marker_source_chain_representation left right (.nil source) initial sourceClosed selected
    rfl rfl selection joint.1
  obtain ⟨lp,rp,lv,rv,_ls,_rs,pieces⟩ := marker_source_selected_fragments left right (.nil source)
    initial sourceClosed selected rfl rfl selection joint.1
  exact ⟨forward,beforeLabels,word,left,right,selection,joint,whole,lp,rp,lv,rv,pieces⟩
end Nonterminal

namespace Distinct
open UniformOldCreatedIncomingLabelsChecks.Distinct

theorem originalClosed : Closed original.erase := by change (0<1 ∧0<1) ∧(0<2 ∧0<2);decide
theorem sourceClosed : Closed source.erase := globalHistory.closed originalClosed

/-- A real nonempty original history is used, with no reinitialization of
its nonINIT relative source and no supplied source-chain iso. -/
theorem actual_noninit_source_iso :
    ∃ left right : MarkerSourceChain F source (.atom 7) false [] (leftNode.label.readLetters false),
      ChainIncidenceIsomorphic (chainSyntaxIncidence source sourceClosed left.edges)
        (chainSyntaxIncidence source sourceClosed right.edges) := by
  obtain ⟨left,right,_first,_labels⟩ := MarkerSourceChainLabelsChecks.Distinct.actual_distinct_current_source_chains
  exact ⟨left,right,marker_source_chain_iso left right globalHistory initial sourceClosed selected rfl rfl⟩

/-- The nonINIT source REP remains a conditional IH. The actual distinct
CURRENT occurrences and two OLD event producer are not a proof of that IH. -/
theorem actual_noninit_source_blocks
    {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
    {g : Net signature N B W} {root : B}
    (selection : OccurrenceFragmentSelection source g root)
    (representation : ChainRepresentationInvariant sourceClosed selection) :
    ∃ left right : MarkerSourceChain F source (.atom 7) false [] (leftNode.label.readLetters false),
      SameChainRepresentation selection left.chain right.chain ∧
      ∃ lp rp : Position source.erase,
        lp.val=left.selectedName++[.fn] ∧rp.val=right.selectedName++[.fn] ∧
        (selection lp).fragment.segments=(selection rp).fragment.segments := by
  obtain ⟨left,right,_first,_labels⟩ := MarkerSourceChainLabelsChecks.Distinct.actual_distinct_current_source_chains
  have whole := marker_source_chain_representation left right globalHistory initial sourceClosed selected
    rfl rfl selection representation
  obtain ⟨lp,rp,lv,rv,_ls,_rs,pieces⟩ := marker_source_selected_fragments left right globalHistory
    initial sourceClosed selected rfl rfl selection representation
  exact ⟨left,right,whole,lp,rp,lv,rv,pieces⟩

/-- This records the two distinct CURRENT positions and the SAME original
INIT history; no source coordinates are identified by their labels. -/
theorem actual_original_history : INIT original ∧History [[]] original source ∧History [left,right] source target ∧
    left≠right ∧target.subterm left=some leftNode ∧target.subterm right=some leftNode :=
  MarkerSourceChainLabelsChecks.Distinct.actual_original_init_and_prior
end Distinct
#print axioms Nonterminal.actual_initial_source_selected_blocks
#print axioms Distinct.originalClosed
#print axioms Distinct.sourceClosed
#print axioms Distinct.actual_noninit_source_iso
#print axioms Distinct.actual_noninit_source_blocks
#print axioms Distinct.actual_original_history
end Lamping.Checks.MarkerSourceChainRepresentationChecks
