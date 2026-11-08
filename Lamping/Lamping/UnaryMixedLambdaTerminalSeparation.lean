import Lamping.Lamping.ActionCopiedBindingFragmentCuts
import Lamping.Lamping.ActionPendingCanonicalAccess
import Lamping.Lamping.ActionKeptFragmentComparison
import Lamping.Lamping.FragmentTerminalSeparation
namespace Lamping.AG
open Graph Lambda Lambda.Labelled
section
variable {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K → Label signature} {i j : Nat} {lt : i<j}
variable (site : PathSite (Schema.croAction Op.lam i j lt) kept (B:=B) (W:=W) (V:=V))

/-- Actual copied-versus-kept terminal separation, without parent restrictions.
Both OLD finishes follow internally from the SAME fragment accesses. -/
theorem SourceEdgeFragment.cro_copied_lambda_context_terminal_vs_kept_terminal
    {directions : B → Bool} (flow : FlowBalance site.net directions)
    (root : B) (positive : directions root=true) {current : LTerm}
    (sourceMatches : Matches site.net root current.erase)
    (principal : SiteActionPrincipal site)
    (source : SourceEdgeFragment current site.net root edge position)
    (target : SourceEdgeFragment current site.reduce root edge position)
    (otherSource : SourceEdgeFragment current site.net root otherEdge otherPosition)
    (otherTarget : SourceEdgeFragment current site.reduce root otherEdge otherPosition)
    (copiedFinish : target.access.val.getLast?=some (site.reduce.wire (.inl ⟨.inr (.inl ()),(.inl ())⟩)))
    (keptNode : K) (keptPort : Port (kept keptNode).sort)
    (keptFinish : otherTarget.access.val.getLast?=some (site.reduce.wire (.inl ⟨.inl keptNode,keptPort⟩))) :
    source.segments≠otherSource.segments ∧target.segments≠otherTarget.segments ∧
      (target.segments=otherTarget.segments ↔source.segments=otherSource.segments) := by
  obtain ⟨a,b,parentLabels⟩ := target.access.property.1.1
  have parentWord : accessWord site.net source.access.val=accessWord site.reduce target.access.val :=
    source.word.trans target.word.symm
  obtain ⟨_padding,oldCopiedFinish,_paddedLabels⟩ :=
    site.cro_lambda_padding_labels flow root positive sourceMatches principal
      source.access target.access parentWord copiedFinish parentLabels
  obtain ⟨c,d,otherLabels⟩ := otherTarget.access.property.1.1
  have otherWord : accessWord site.net otherSource.access.val=accessWord site.reduce otherTarget.access.val :=
    otherSource.word.trans otherTarget.word.symm
  obtain ⟨_otherRelation,_otherOldLabels,oldKeptFinish⟩ := site.action_kept_canonical_access
    (.cro .lam i j lt) flow root positive sourceMatches principal otherSource.access otherTarget.access
      otherWord keptNode keptPort keptFinish otherLabels
  have oldDifferent : source.segments≠otherSource.segments :=
    source.ne_of_terminal_nodes otherSource (.inr (.inr ())) (.inl keptNode) (.inl ()) keptPort
      oldCopiedFinish oldKeptFinish (by intro impossible;cases impossible)
  have newDifferent : target.segments≠otherTarget.segments :=
    target.ne_of_terminal_nodes otherTarget (.inr (.inl ())) (.inl keptNode) (.inl ()) keptPort
      copiedFinish keptFinish (by intro impossible;cases impossible)
  exact ⟨oldDifferent,newDifferent,⟨fun same=>(newDifferent same).elim,fun same=>(oldDifferent same).elim⟩⟩
end
#print axioms SourceEdgeFragment.cro_copied_lambda_context_terminal_vs_kept_terminal
section
variable {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K → Label signature} {i j : Nat} {lt : i<j}
variable (site : PathSite (Schema.braAction Op.lam i j lt) kept (B:=B) (W:=W) (V:=V))

/-- Actual copied-versus-kept terminal separation, without parent restrictions.
Both OLD finishes follow internally from the SAME fragment accesses. -/
theorem SourceEdgeFragment.bra_copied_lambda_context_terminal_vs_kept_terminal
    {directions : B → Bool} (flow : FlowBalance site.net directions)
    (root : B) (positive : directions root=true) {current : LTerm}
    (sourceMatches : Matches site.net root current.erase)
    (principal : SiteActionPrincipal site)
    (source : SourceEdgeFragment current site.net root edge position)
    (target : SourceEdgeFragment current site.reduce root edge position)
    (otherSource : SourceEdgeFragment current site.net root otherEdge otherPosition)
    (otherTarget : SourceEdgeFragment current site.reduce root otherEdge otherPosition)
    (copiedFinish : target.access.val.getLast?=some (site.reduce.wire (.inl ⟨.inr (.inl ()),(.inl ())⟩)))
    (keptNode : K) (keptPort : Port (kept keptNode).sort)
    (keptFinish : otherTarget.access.val.getLast?=some (site.reduce.wire (.inl ⟨.inl keptNode,keptPort⟩))) :
    source.segments≠otherSource.segments ∧target.segments≠otherTarget.segments ∧
      (target.segments=otherTarget.segments ↔source.segments=otherSource.segments) := by
  obtain ⟨a,b,parentLabels⟩ := target.access.property.1.1
  have parentWord : accessWord site.net source.access.val=accessWord site.reduce target.access.val :=
    source.word.trans target.word.symm
  obtain ⟨_padding,oldCopiedFinish,_paddedLabels⟩ :=
    site.bra_lambda_padding_labels flow root positive sourceMatches principal
      source.access target.access parentWord copiedFinish parentLabels
  obtain ⟨c,d,otherLabels⟩ := otherTarget.access.property.1.1
  have otherWord : accessWord site.net otherSource.access.val=accessWord site.reduce otherTarget.access.val :=
    otherSource.word.trans otherTarget.word.symm
  obtain ⟨_otherRelation,_otherOldLabels,oldKeptFinish⟩ := site.action_kept_canonical_access
    (.bra .lam i j lt) flow root positive sourceMatches principal otherSource.access otherTarget.access
      otherWord keptNode keptPort keptFinish otherLabels
  have oldDifferent : source.segments≠otherSource.segments :=
    source.ne_of_terminal_nodes otherSource (.inr (.inr ())) (.inl keptNode) (.inl ()) keptPort
      oldCopiedFinish oldKeptFinish (by intro impossible;cases impossible)
  have newDifferent : target.segments≠otherTarget.segments :=
    target.ne_of_terminal_nodes otherTarget (.inr (.inl ())) (.inl keptNode) (.inl ()) keptPort
      copiedFinish keptFinish (by intro impossible;cases impossible)
  exact ⟨oldDifferent,newDifferent,⟨fun same=>(newDifferent same).elim,fun same=>(oldDifferent same).elim⟩⟩
end
#print axioms SourceEdgeFragment.bra_copied_lambda_context_terminal_vs_kept_terminal

section
variable {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K → Label signature} {i j : Nat} {lt : i<j}
variable (site : PathSite (Schema.croAction Op.lam i j lt) kept (B:=B) (W:=W) (V:=V))

/-- Actual copied-versus-kept terminal separation, without parent restrictions.
Both OLD finishes follow internally from the SAME fragment accesses. -/
theorem SourceEdgeFragment.cro_copied_lambda_binding_terminal_vs_kept_terminal
    {directions : B → Bool} (flow : FlowBalance site.net directions)
    (root : B) (positive : directions root=true) {current : LTerm}
    (sourceMatches : Matches site.net root current.erase)
    (principal : SiteActionPrincipal site)
    (source : SourceEdgeFragment current site.net root edge position)
    (target : SourceEdgeFragment current site.reduce root edge position)
    (otherSource : SourceEdgeFragment current site.net root otherEdge otherPosition)
    (otherTarget : SourceEdgeFragment current site.reduce root otherEdge otherPosition)
    (copiedFinish : target.access.val.getLast?=some (site.reduce.wire (.inl ⟨.inr (.inl ()),lamBind⟩)))
    (keptNode : K) (keptPort : Port (kept keptNode).sort)
    (keptFinish : otherTarget.access.val.getLast?=some (site.reduce.wire (.inl ⟨.inl keptNode,keptPort⟩))) :
    source.segments≠otherSource.segments ∧target.segments≠otherTarget.segments ∧
      (target.segments=otherTarget.segments ↔source.segments=otherSource.segments) := by
  obtain ⟨a,b,parentLabels⟩ := target.access.property.1.1
  have parentWord : accessWord site.net source.access.val=accessWord site.reduce target.access.val :=
    source.word.trans target.word.symm
  obtain ⟨pending,_relation,_oldLabels,oldCopiedFinish,_shape⟩ :=
    site.cro_aux_canonical_access flow root positive sourceMatches principal
      source.access target.access parentWord false copiedFinish parentLabels
  obtain ⟨c,d,otherLabels⟩ := otherTarget.access.property.1.1
  have otherWord : accessWord site.net otherSource.access.val=accessWord site.reduce otherTarget.access.val :=
    otherSource.word.trans otherTarget.word.symm
  obtain ⟨_otherRelation,_otherOldLabels,oldKeptFinish⟩ := site.action_kept_canonical_access
    (.cro .lam i j lt) flow root positive sourceMatches principal otherSource.access otherTarget.access
      otherWord keptNode keptPort keptFinish otherLabels
  have oldDifferent : source.segments≠otherSource.segments :=
    source.ne_of_terminal_nodes otherSource (.inr (.inr ())) (.inl keptNode) lamBind keptPort
      oldCopiedFinish oldKeptFinish (by intro impossible;cases impossible)
  have newDifferent : target.segments≠otherTarget.segments :=
    target.ne_of_terminal_nodes otherTarget (.inr (.inl ())) (.inl keptNode) lamBind keptPort
      copiedFinish keptFinish (by intro impossible;cases impossible)
  exact ⟨oldDifferent,newDifferent,⟨fun same=>(newDifferent same).elim,fun same=>(oldDifferent same).elim⟩⟩
end
#print axioms SourceEdgeFragment.cro_copied_lambda_binding_terminal_vs_kept_terminal
section
variable {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K → Label signature} {i j : Nat} {lt : i<j}
variable (site : PathSite (Schema.braAction Op.lam i j lt) kept (B:=B) (W:=W) (V:=V))

/-- Actual copied-versus-kept terminal separation, without parent restrictions.
Both OLD finishes follow internally from the SAME fragment accesses. -/
theorem SourceEdgeFragment.bra_copied_lambda_binding_terminal_vs_kept_terminal
    {directions : B → Bool} (flow : FlowBalance site.net directions)
    (root : B) (positive : directions root=true) {current : LTerm}
    (sourceMatches : Matches site.net root current.erase)
    (principal : SiteActionPrincipal site)
    (source : SourceEdgeFragment current site.net root edge position)
    (target : SourceEdgeFragment current site.reduce root edge position)
    (otherSource : SourceEdgeFragment current site.net root otherEdge otherPosition)
    (otherTarget : SourceEdgeFragment current site.reduce root otherEdge otherPosition)
    (copiedFinish : target.access.val.getLast?=some (site.reduce.wire (.inl ⟨.inr (.inl ()),lamBind⟩)))
    (keptNode : K) (keptPort : Port (kept keptNode).sort)
    (keptFinish : otherTarget.access.val.getLast?=some (site.reduce.wire (.inl ⟨.inl keptNode,keptPort⟩))) :
    source.segments≠otherSource.segments ∧target.segments≠otherTarget.segments ∧
      (target.segments=otherTarget.segments ↔source.segments=otherSource.segments) := by
  obtain ⟨a,b,parentLabels⟩ := target.access.property.1.1
  have parentWord : accessWord site.net source.access.val=accessWord site.reduce target.access.val :=
    source.word.trans target.word.symm
  obtain ⟨pending,_relation,_oldLabels,oldCopiedFinish,_shape⟩ :=
    site.bra_aux_canonical_access flow root positive sourceMatches principal
      source.access target.access parentWord false copiedFinish parentLabels
  obtain ⟨c,d,otherLabels⟩ := otherTarget.access.property.1.1
  have otherWord : accessWord site.net otherSource.access.val=accessWord site.reduce otherTarget.access.val :=
    otherSource.word.trans otherTarget.word.symm
  obtain ⟨_otherRelation,_otherOldLabels,oldKeptFinish⟩ := site.action_kept_canonical_access
    (.bra .lam i j lt) flow root positive sourceMatches principal otherSource.access otherTarget.access
      otherWord keptNode keptPort keptFinish otherLabels
  have oldDifferent : source.segments≠otherSource.segments :=
    source.ne_of_terminal_nodes otherSource (.inr (.inr ())) (.inl keptNode) lamBind keptPort
      oldCopiedFinish oldKeptFinish (by intro impossible;cases impossible)
  have newDifferent : target.segments≠otherTarget.segments :=
    target.ne_of_terminal_nodes otherTarget (.inr (.inl ())) (.inl keptNode) lamBind keptPort
      copiedFinish keptFinish (by intro impossible;cases impossible)
  exact ⟨oldDifferent,newDifferent,⟨fun same=>(newDifferent same).elim,fun same=>(oldDifferent same).elim⟩⟩
end
#print axioms SourceEdgeFragment.bra_copied_lambda_binding_terminal_vs_kept_terminal

section
variable {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K → Label signature} {i j : Nat} {lt : i<j}
variable (site : PathSite (Schema.croAction Op.lam i j lt) kept (B:=B) (W:=W) (V:=V))
/-- Actual context and binding ports of the same selected/copied lambda differ
on both sides; each OLD finish is derived from its own actual access. -/
theorem SourceEdgeFragment.cro_copied_lambda_context_vs_binding
    {directions : B → Bool} (flow : FlowBalance site.net directions)
    (root : B) (positive : directions root=true) {current : LTerm}
    (sourceMatches : Matches site.net root current.erase) (principal : SiteActionPrincipal site)
    (source : SourceEdgeFragment current site.net root edge position)
    (target : SourceEdgeFragment current site.reduce root edge position)
    (otherSource : SourceEdgeFragment current site.net root otherEdge otherPosition)
    (otherTarget : SourceEdgeFragment current site.reduce root otherEdge otherPosition)
    (contextFinish : target.access.val.getLast?=some (site.reduce.wire (.inl ⟨.inr (.inl ()),.inl ()⟩)))
    (bindingFinish : otherTarget.access.val.getLast?=some (site.reduce.wire (.inl ⟨.inr (.inl ()),lamBind⟩))) :
    source.segments≠otherSource.segments ∧target.segments≠otherTarget.segments ∧
      (target.segments=otherTarget.segments ↔source.segments=otherSource.segments) := by
  obtain ⟨a,b,labels⟩ := target.access.property.1.1
  obtain ⟨_padding,oldContext,_paddedLabels⟩ := site.cro_lambda_padding_labels flow root positive sourceMatches
    principal source.access target.access (source.word.trans target.word.symm) contextFinish labels
  obtain ⟨c,d,otherLabels⟩ := otherTarget.access.property.1.1
  obtain ⟨_pending,_relation,_labels,oldBinding,_shape⟩ := site.cro_aux_canonical_access flow root positive sourceMatches
    principal otherSource.access otherTarget.access (otherSource.word.trans otherTarget.word.symm) false bindingFinish otherLabels
  have oldDifferent : source.segments≠otherSource.segments :=
    source.ne_of_terminal_ports otherSource ⟨.inr (.inr ()),.inl ()⟩ ⟨.inr (.inr ()),lamBind⟩
      oldContext oldBinding (by intro same;cases same)
  have newDifferent : target.segments≠otherTarget.segments :=
    target.ne_of_terminal_ports otherTarget ⟨.inr (.inl ()),.inl ()⟩ ⟨.inr (.inl ()),lamBind⟩
      contextFinish bindingFinish (by intro same;cases same)
  exact ⟨oldDifferent,newDifferent,⟨fun same=>(newDifferent same).elim,fun same=>(oldDifferent same).elim⟩⟩
end
#print axioms SourceEdgeFragment.cro_copied_lambda_context_vs_binding
section
variable {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K → Label signature} {i j : Nat} {lt : i<j}
variable (site : PathSite (Schema.braAction Op.lam i j lt) kept (B:=B) (W:=W) (V:=V))
/-- Actual context and binding ports of the same selected/copied lambda differ
on both sides; each OLD finish is derived from its own actual access. -/
theorem SourceEdgeFragment.bra_copied_lambda_context_vs_binding
    {directions : B → Bool} (flow : FlowBalance site.net directions)
    (root : B) (positive : directions root=true) {current : LTerm}
    (sourceMatches : Matches site.net root current.erase) (principal : SiteActionPrincipal site)
    (source : SourceEdgeFragment current site.net root edge position)
    (target : SourceEdgeFragment current site.reduce root edge position)
    (otherSource : SourceEdgeFragment current site.net root otherEdge otherPosition)
    (otherTarget : SourceEdgeFragment current site.reduce root otherEdge otherPosition)
    (contextFinish : target.access.val.getLast?=some (site.reduce.wire (.inl ⟨.inr (.inl ()),.inl ()⟩)))
    (bindingFinish : otherTarget.access.val.getLast?=some (site.reduce.wire (.inl ⟨.inr (.inl ()),lamBind⟩))) :
    source.segments≠otherSource.segments ∧target.segments≠otherTarget.segments ∧
      (target.segments=otherTarget.segments ↔source.segments=otherSource.segments) := by
  obtain ⟨a,b,labels⟩ := target.access.property.1.1
  obtain ⟨_padding,oldContext,_paddedLabels⟩ := site.bra_lambda_padding_labels flow root positive sourceMatches
    principal source.access target.access (source.word.trans target.word.symm) contextFinish labels
  obtain ⟨c,d,otherLabels⟩ := otherTarget.access.property.1.1
  obtain ⟨_pending,_relation,_labels,oldBinding,_shape⟩ := site.bra_aux_canonical_access flow root positive sourceMatches
    principal otherSource.access otherTarget.access (otherSource.word.trans otherTarget.word.symm) false bindingFinish otherLabels
  have oldDifferent : source.segments≠otherSource.segments :=
    source.ne_of_terminal_ports otherSource ⟨.inr (.inr ()),.inl ()⟩ ⟨.inr (.inr ()),lamBind⟩
      oldContext oldBinding (by intro same;cases same)
  have newDifferent : target.segments≠otherTarget.segments :=
    target.ne_of_terminal_ports otherTarget ⟨.inr (.inl ()),.inl ()⟩ ⟨.inr (.inl ()),lamBind⟩
      contextFinish bindingFinish (by intro same;cases same)
  exact ⟨oldDifferent,newDifferent,⟨fun same=>(newDifferent same).elim,fun same=>(oldDifferent same).elim⟩⟩
end
#print axioms SourceEdgeFragment.bra_copied_lambda_context_vs_binding
end Lamping.AG
