import Lamping.Lambda.MarkerSourceChainLabels
import Lamping.Lamping.ActualChainLabelConverse
import Lamping.Lamping.FanLambdaSlotSynchronization
namespace Lamping.AG
open Graph Lambda Lambda.Labelled

/-- The source is the actual generated relative OLD source. Its prefix
history, rather than the current OLD schedule, provides the INIT provenance. -/
theorem marker_source_chain_iso
    (left : MarkerSourceChain F source degree forward leftBefore leftWord)
    (right : MarkerSourceChain F source degree forward rightBefore rightWord)
    (prefixHistory : History prior original source) (initial : INIT original)
    (closed : Closed source.erase)
    (selected : ∀name∈F,source.degreeAt name=some degree)
    (sameBefore : leftBefore=rightBefore) (sameWord : leftWord=rightWord) :
    ChainIncidenceIsomorphic (chainSyntaxIncidence source closed left.edges)
      (chainSyntaxIncidence source closed right.edges) :=
  actual_chain_iso_of_labels prefixHistory initial closed left.chain right.chain
    (left.compare_chain_labels right selected sameBefore sameWord)

section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable {g : Net signature N B W} {root : B}

/-- A genuine source REP induction hypothesis is consumed; actual source
REP truth is not asserted. The SAME selection supplies both whole images. -/
theorem marker_source_chain_representation
    (left : MarkerSourceChain F source degree forward leftBefore leftWord)
    (right : MarkerSourceChain F source degree forward rightBefore rightWord)
    (prefixHistory : History prior original source) (initial : INIT original)
    (closed : Closed source.erase)
    (selected : ∀name∈F,source.degreeAt name=some degree)
    (sameBefore : leftBefore=rightBefore) (sameWord : leftWord=rightWord)
    (selection : OccurrenceFragmentSelection source g root)
    (representation : ChainRepresentationInvariant closed selection) :
    SameChainRepresentation selection left.chain right.chain :=
  (representation left.chain right.chain).mpr
    (marker_source_chain_iso left right prefixHistory initial closed selected sameBefore sameWord)

/-- Real selected FUNCTION positions and their common last ordinal are
constructed internally. Full labels never identify CURRENT coordinates. -/
theorem marker_source_selected_fragments
    (left : MarkerSourceChain F source degree forward leftBefore leftWord)
    (right : MarkerSourceChain F source degree forward rightBefore rightWord)
    (prefixHistory : History prior original source) (initial : INIT original)
    (closed : Closed source.erase)
    (selected : ∀name∈F,source.degreeAt name=some degree)
    (sameBefore : leftBefore=rightBefore) (sameWord : leftWord=rightWord)
    (selection : OccurrenceFragmentSelection source g root)
    (representation : ChainRepresentationInvariant closed selection) :
    ∃ leftPosition rightPosition : Position source.erase,
      leftPosition.val=left.selectedName++[.fn] ∧rightPosition.val=right.selectedName++[.fn] ∧
      left.edges[left.before.length+1]?=some leftPosition.val ∧
      right.edges[left.before.length+1]?=some rightPosition.val ∧
      (selection leftPosition).fragment.segments=(selection rightPosition).fragment.segments := by
  obtain ⟨lb,lbody,larg,atLeft⟩ := LTerm.degreeAt_redex (selected _ left.selected)
  obtain ⟨rb,rbody,rarg,atRight⟩ := LTerm.degreeAt_redex (selected _ right.selected)
  have leftLookup : source.subterm (left.selectedName++[.fn])=some (.lam degree lbody) := by
    rw [LTerm.subterm_append,atLeft];rfl
  have rightLookup : source.subterm (right.selectedName++[.fn])=some (.lam degree rbody) := by
    rw [LTerm.subterm_append,atRight];rfl
  let lp : Position source.erase := ⟨left.selectedName++[.fn],by rw [←LTerm.erase_subterm,leftLookup];rfl⟩
  let rp : Position source.erase := ⟨right.selectedName++[.fn],by rw [←LTerm.erase_subterm,rightLookup];rfl⟩
  have beforeLabels := left.before_eq.symm.trans (sameBefore.trans right.before_eq)
  have beforeLength : left.before.length=right.before.length := by
    simpa only [List.length_map] using congrArg List.length beforeLabels
  have ls : left.edges[left.before.length+1]?=some lp.val := by
    change (left.before++[left.first,left.selectedName++[.fn]])[left.before.length+1]?=_
    rw [List.getElem?_append_right (by omega)]
    simp only [Nat.add_sub_cancel_left,List.getElem?_cons_succ,List.getElem?_cons_zero]
    rfl
  have rs : right.edges[left.before.length+1]?=some rp.val := by
    rw [beforeLength]
    change (right.before++[right.first,right.selectedName++[.fn]])[right.before.length+1]?=_
    rw [List.getElem?_append_right (by omega)]
    simp only [Nat.add_sub_cancel_left,List.getElem?_cons_succ,List.getElem?_cons_zero]
    rfl
  have physical := marker_source_chain_representation left right prefixHistory initial closed selected
    sameBefore sameWord selection representation
  exact ⟨lp,rp,rfl,rfl,ls,rs,same_chain_representation_slot selection left.chain right.chain physical lp rp ls rs⟩
end
#print axioms marker_source_chain_iso
#print axioms marker_source_chain_representation
#print axioms marker_source_selected_fragments
end Lamping.AG
