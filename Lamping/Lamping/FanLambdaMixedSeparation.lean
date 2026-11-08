import Lamping.Lamping.FanBodyFragmentReflection
import Lamping.Lamping.FragmentParentSeparation
import Lamping.Lamping.FragmentTerminalSeparation
namespace Lamping.AG
open Graph Lambda Lambda.Labelled
section
variable {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K→Label signature} {i j : Nat} {lt : i<j}
variable (site : PathSite (.fanAction .lam i j lt) kept (B:=B) (W:=W) (V:=V))
/-- The OLD copied-parent finish is the passive lambda context, obtained
from the whole OLD access and SAME principal, never the fan-aux prefix end. -/
theorem SourceEdgeFragment.fan_lambda_copied_parent_vs_kept_parent
    {directions : B→Bool} (flow : FlowBalance site.net directions)
    (root : B) (positive : directions root=true) {current : LTerm}
    (sourceMatches : Matches site.net root current.erase) (targetMatches : Matches site.reduce root current.erase)
    (principal : SiteActionPrincipal site)
    (sourceCopy : SourceEdgeFragment current site.net root copyEdge p)
    (targetCopy : SourceEdgeFragment current site.reduce root copyEdge p)
    (sourceKept : SourceEdgeFragment current site.net root keptEdge q)
    (targetKept : SourceEdgeFragment current site.reduce root keptEdge q)
    (copyRole : SourceDeparture copyTerm .body copyEdge.fromPort)
    (keptRole : SourceDeparture keptTerm keptStep keptEdge.fromPort)
    (sourceCopyParent sourceKeptParent : RootAccess site.net root)
    (targetCopyParent targetKeptParent : RootAccess site.reduce root)
    (sourceCopyWord : p=accessWord site.net sourceCopyParent.val++[.body])
    (sourceKeptWord : q=accessWord site.net sourceKeptParent.val++[keptStep])
    (targetCopyWord : p=accessWord site.reduce targetCopyParent.val++[.body])
    (targetKeptWord : q=accessWord site.reduce targetKeptParent.val++[keptStep])
    (branch : Bool)
    (copyFinish : targetCopyParent.val.getLast?=some (site.reduce.wire (.inl ⟨.inr (.inl branch),.inl ()⟩)))
    (node : K) (port : Port (kept node).sort)
    (keptFinish : targetKeptParent.val.getLast?=some (site.reduce.wire (.inl ⟨.inl node,port⟩))) :
    sourceCopy.segments≠sourceKept.segments ∧targetCopy.segments≠targetKept.segments := by
  obtain ⟨a,b,copyLabels⟩ := targetCopyParent.property.1.1
  obtain ⟨_pending,oldPre,_contexts,_relation,_labels,wholeSplit,_prefixLast,_raw⟩ :=
    site.fan_lambda_context_canonical_trim flow root positive sourceMatches principal sourceCopyParent targetCopyParent
      (List.append_cancel_right (sourceCopyWord.symm.trans targetCopyWord)) branch copyFinish copyLabels
  have oldCopyFinish : sourceCopyParent.val.getLast?=some
      (site.net.wire (.inl ⟨.inr (.inr ()),.inl ()⟩)) := by
    rw [wholeSplit,List.getLast?_append,principal.last,Option.some_or]
  obtain ⟨c,d,keptLabels⟩ := targetKeptParent.property.1.1
  obtain ⟨_keptRelation,_keptLabels,oldKeptFinish⟩ := site.action_kept_canonical_access (.fan .lam i j lt)
    flow root positive sourceMatches principal sourceKeptParent targetKeptParent
    (List.append_cancel_right (sourceKeptWord.symm.trans targetKeptWord)) node port keptFinish keptLabels
  exact ⟨SourceEdgeFragment.ne_of_parent_nodes sourceMatches sourceCopy sourceKept copyRole keptRole
      sourceCopyParent sourceKeptParent sourceCopyWord sourceKeptWord (.inr (.inr ())) (.inl node)
      (.inl ()) port oldCopyFinish oldKeptFinish (by intro h;cases h),
    SourceEdgeFragment.ne_of_parent_nodes targetMatches targetCopy targetKept copyRole keptRole
      targetCopyParent targetKeptParent targetCopyWord targetKeptWord (.inr (.inl branch)) (.inl node)
      (.inl ()) port copyFinish keptFinish (by intro h;cases h)⟩

/-- Terminal separation has no parent restriction. Each OLD finish is
reflected from its own actual whole labelled access before comparing nodes. -/
theorem SourceEdgeFragment.fan_lambda_copied_context_vs_kept_terminal
    {directions : B→Bool} (flow : FlowBalance site.net directions)
    (root : B) (positive : directions root=true) {current : LTerm}
    (sourceMatches : Matches site.net root current.erase)
    (principal : SiteActionPrincipal site)
    (sourceCopy : SourceEdgeFragment current site.net root copyEdge p)
    (targetCopy : SourceEdgeFragment current site.reduce root copyEdge p)
    (sourceKept : SourceEdgeFragment current site.net root keptEdge q)
    (targetKept : SourceEdgeFragment current site.reduce root keptEdge q)
    (branch : Bool)
    (copyFinish : targetCopy.access.val.getLast?=some (site.reduce.wire (.inl ⟨.inr (.inl branch),.inl ()⟩)))
    (node : K) (port : Port (kept node).sort)
    (keptFinish : targetKept.access.val.getLast?=some (site.reduce.wire (.inl ⟨.inl node,port⟩))) :
    sourceCopy.segments≠sourceKept.segments ∧targetCopy.segments≠targetKept.segments := by
  obtain ⟨a,b,copyLabels⟩ := targetCopy.access.property.1.1
  obtain ⟨_pending,oldPre,_contexts,_relation,_labels,wholeSplit,_prefixLast,_raw⟩ :=
    site.fan_lambda_context_canonical_trim flow root positive sourceMatches principal sourceCopy.access targetCopy.access
      (sourceCopy.word.trans targetCopy.word.symm) branch copyFinish copyLabels
  have oldCopyFinish : sourceCopy.access.val.getLast?=some
      (site.net.wire (.inl ⟨.inr (.inr ()),.inl ()⟩)) := by
    rw [wholeSplit,List.getLast?_append,principal.last,Option.some_or]
  obtain ⟨c,d,keptLabels⟩ := targetKept.access.property.1.1
  obtain ⟨_keptRelation,_keptLabels,oldKeptFinish⟩ := site.action_kept_canonical_access (.fan .lam i j lt)
    flow root positive sourceMatches principal sourceKept.access targetKept.access
    (sourceKept.word.trans targetKept.word.symm) node port keptFinish keptLabels
  exact ⟨sourceCopy.ne_of_terminal_nodes sourceKept (.inr (.inr ())) (.inl node)
      (.inl ()) port oldCopyFinish oldKeptFinish (by intro h;cases h),
    targetCopy.ne_of_terminal_nodes targetKept (.inr (.inl branch)) (.inl node)
      (.inl ()) port copyFinish keptFinish (by intro h;cases h)⟩

theorem PathSite.fan_lambda_mixed_parent_slot_exclusion
    {directions : B→Bool} (flow : FlowBalance site.net directions)
    (root : B) (positive : directions root=true) {current : LTerm}
    (sourceMatches : Matches site.net root current.erase) (targetMatches : Matches site.reduce root current.erase)
    (principal : SiteActionPrincipal site)
    (leftPosition rightPosition : Position current.erase)
    (sourceCopy : OccurrenceFragment current site.net root leftPosition.val)
    (targetCopy : OccurrenceFragment current site.reduce root leftPosition.val)
    (sourceKept : OccurrenceFragment current site.net root rightPosition.val)
    (targetKept : OccurrenceFragment current site.reduce root rightPosition.val)
    (copyRole : SourceDeparture copyTerm .body (sourceEdge sourceCopy.environment sourceCopy.context sourceCopy.term).fromPort)
    (keptRole : SourceDeparture keptTerm keptStep (sourceEdge sourceKept.environment sourceKept.context sourceKept.term).fromPort)
    (sourceCopyParent sourceKeptParent : RootAccess site.net root)
    (targetCopyParent targetKeptParent : RootAccess site.reduce root)
    (sourceCopyWord : leftPosition.val=accessWord site.net sourceCopyParent.val++[.body])
    (sourceKeptWord : rightPosition.val=accessWord site.net sourceKeptParent.val++[keptStep])
    (targetCopyWord : leftPosition.val=accessWord site.reduce targetCopyParent.val++[.body])
    (targetKeptWord : rightPosition.val=accessWord site.reduce targetKeptParent.val++[keptStep])
    (branch : Bool)
    (copyFinish : targetCopyParent.val.getLast?=some (site.reduce.wire (.inl ⟨.inr (.inl branch),.inl ()⟩)))
    (node : K) (port : Port (kept node).sort)
    (keptFinish : targetKeptParent.val.getLast?=some (site.reduce.wire (.inl ⟨.inl node,port⟩)))
    (sourceSelection : OccurrenceFragmentSelection current site.net root)
    (targetSelection : OccurrenceFragmentSelection current site.reduce root)
    (first : PrerequisiteChain current start left) (second : PrerequisiteChain current finish right)
    {n : Nat} (leftSlot : left[n]?=some leftPosition.val) (rightSlot : right[n]?=some rightPosition.val) :
    ¬SameChainRepresentation sourceSelection first second ∧¬SameChainRepresentation targetSelection first second := by
  have sourceSlot : SameChainRepresentation sourceSelection first second →
      sourceCopy.fragment.segments=sourceKept.fragment.segments := by
    intro physical
    exact (OccurrenceFragment.segments_unique sourceMatches (sourceSelection leftPosition) sourceCopy).symm.trans
      ((same_chain_representation_slot sourceSelection first second physical leftPosition rightPosition leftSlot rightSlot).trans
        (OccurrenceFragment.segments_unique sourceMatches (sourceSelection rightPosition) sourceKept))
  have targetSlot : SameChainRepresentation targetSelection first second →
      targetCopy.fragment.segments=targetKept.fragment.segments := by
    intro physical
    exact (OccurrenceFragment.segments_unique targetMatches (targetSelection leftPosition) targetCopy).symm.trans
      ((same_chain_representation_slot targetSelection first second physical leftPosition rightPosition leftSlot rightSlot).trans
        (OccurrenceFragment.segments_unique targetMatches (targetSelection rightPosition) targetKept))
  rcases sourceCopy with ⟨lsub,lenv,lctx,locc,lsource⟩
  rcases targetCopy with ⟨_,_,_,ltocc,ltarget⟩
  obtain ⟨rfl,rfl,rfl⟩ := locc.same_occurrence ltocc
  rcases sourceKept with ⟨rsub,renv,rctx,rocc,rsource⟩
  rcases targetKept with ⟨_,_,_,rtocc,rtarget⟩
  obtain ⟨rfl,rfl,rfl⟩ := rocc.same_occurrence rtocc
  have separated := lsource.fan_lambda_copied_parent_vs_kept_parent site flow root positive
    sourceMatches targetMatches principal ltarget rsource rtarget copyRole keptRole
    sourceCopyParent sourceKeptParent targetCopyParent targetKeptParent
    sourceCopyWord sourceKeptWord targetCopyWord targetKeptWord branch copyFinish node port keptFinish
  exact ⟨fun physical=>separated.1 (sourceSlot physical),fun physical=>separated.2 (targetSlot physical)⟩

theorem PathSite.fan_lambda_mixed_terminal_slot_exclusion
    {directions : B→Bool} (flow : FlowBalance site.net directions)
    (root : B) (positive : directions root=true) {current : LTerm}
    (sourceMatches : Matches site.net root current.erase) (targetMatches : Matches site.reduce root current.erase)
    (principal : SiteActionPrincipal site)
    (leftPosition rightPosition : Position current.erase)
    (sourceCopy : OccurrenceFragment current site.net root leftPosition.val)
    (targetCopy : OccurrenceFragment current site.reduce root leftPosition.val)
    (sourceKept : OccurrenceFragment current site.net root rightPosition.val)
    (targetKept : OccurrenceFragment current site.reduce root rightPosition.val)
    (branch : Bool)
    (copyFinish : targetCopy.fragment.access.val.getLast?=some (site.reduce.wire (.inl ⟨.inr (.inl branch),.inl ()⟩)))
    (node : K) (port : Port (kept node).sort)
    (keptFinish : targetKept.fragment.access.val.getLast?=some (site.reduce.wire (.inl ⟨.inl node,port⟩)))
    (sourceSelection : OccurrenceFragmentSelection current site.net root)
    (targetSelection : OccurrenceFragmentSelection current site.reduce root)
    (first : PrerequisiteChain current start left) (second : PrerequisiteChain current finish right)
    {n : Nat} (leftSlot : left[n]?=some leftPosition.val) (rightSlot : right[n]?=some rightPosition.val) :
    ¬SameChainRepresentation sourceSelection first second ∧¬SameChainRepresentation targetSelection first second := by
  have sourceSlot : SameChainRepresentation sourceSelection first second →
      sourceCopy.fragment.segments=sourceKept.fragment.segments := by
    intro physical
    exact (OccurrenceFragment.segments_unique sourceMatches (sourceSelection leftPosition) sourceCopy).symm.trans
      ((same_chain_representation_slot sourceSelection first second physical leftPosition rightPosition leftSlot rightSlot).trans
        (OccurrenceFragment.segments_unique sourceMatches (sourceSelection rightPosition) sourceKept))
  have targetSlot : SameChainRepresentation targetSelection first second →
      targetCopy.fragment.segments=targetKept.fragment.segments := by
    intro physical
    exact (OccurrenceFragment.segments_unique targetMatches (targetSelection leftPosition) targetCopy).symm.trans
      ((same_chain_representation_slot targetSelection first second physical leftPosition rightPosition leftSlot rightSlot).trans
        (OccurrenceFragment.segments_unique targetMatches (targetSelection rightPosition) targetKept))
  rcases sourceCopy with ⟨lsub,lenv,lctx,locc,lsource⟩
  rcases targetCopy with ⟨_,_,_,ltocc,ltarget⟩
  obtain ⟨rfl,rfl,rfl⟩ := locc.same_occurrence ltocc
  rcases sourceKept with ⟨rsub,renv,rctx,rocc,rsource⟩
  rcases targetKept with ⟨_,_,_,rtocc,rtarget⟩
  obtain ⟨rfl,rfl,rfl⟩ := rocc.same_occurrence rtocc
  have separated := lsource.fan_lambda_copied_context_vs_kept_terminal site flow root positive
    sourceMatches principal ltarget rsource rtarget branch copyFinish node port keptFinish
  exact ⟨fun physical=>separated.1 (sourceSlot physical),fun physical=>separated.2 (targetSlot physical)⟩
end
end Lamping.AG
#print axioms Lamping.AG.SourceEdgeFragment.fan_lambda_copied_parent_vs_kept_parent
#print axioms Lamping.AG.SourceEdgeFragment.fan_lambda_copied_context_vs_kept_terminal

#print axioms Lamping.AG.PathSite.fan_lambda_mixed_parent_slot_exclusion
#print axioms Lamping.AG.PathSite.fan_lambda_mixed_terminal_slot_exclusion
