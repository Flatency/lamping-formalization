import Lamping.Lamping.ActualSpineAfterAlignment
import Lamping.Checks.DirectedMarkerSpineIncidence
import Lamping.Checks.BackwardOtherLastFarSources
namespace Lamping.Checks.ActualSpineAfterAlignmentChecks
open Lambda Lambda.Labelled AG SyntaxIncidence
namespace EmptyCopy
open UniformOldCreatedIncomingLabelsChecks.Distinct
abbrev event := SelectedOldOtherLastOriginsChecks.event
abbrev origin := SelectedOldOtherLastOriginsChecks.readingOrigin
abbrev reading := SelectedOldOtherLastOriginsChecks.actual_reading
abbrev remaining := BackwardOtherLastFarSourcesChecks.EmptyCopy.remaining
abbrev ownLast := SelectedOldOtherLastOriginsChecks.ownLastTrace

theorem sourceClosed : Closed source.erase := globalHistory.closed (by
  change Closed bare
  simp [Closed,Scoped])

def spine : DirectedMarkerSpine F source (.atom 7) false [left,right] target [] right :=
  .safe event reading rfl origin (.refl (p:=right++[.arg])) rfl
    (by intro e h;cases h) (by rfl : middle.subterm (right++[.arg])=some oldArgument)
    (by trivial) rfl rfl ownLast

def cut : ActualUnsafeMarkerCut F [left,right] source target (.atom 7) right [right,[.arg],[.fn]] where
  before := []
  edge := right
  after := [[.arg],[.fn]]
  reader := right
  node := leftNode
  forward := false
  split := rfl
  segment := .refl
  remaining := remaining
  reading := reading
  lookup := rfl
  safeBefore := by intro e h;cases h
  marked := marked
  spine := spine
  leaf := spine.leaf_output rfl

def currentParent : ProperPosition target := ⟨[.arg],Or.inr ⟨_,_,rfl⟩⟩
def middleParent : ProperPosition middle := ⟨[.arg],Or.inr ⟨_,_,rfl⟩⟩
def originalParent : ProperPosition source := ⟨[.arg],Or.inr ⟨_,_,rfl⟩⟩

theorem currentSource : Source target right (some currentParent) := ⟨.body,_,_,rfl,rfl,.body⟩
def middleChain : EndpointChain middle (some middleParent) [[.arg],[.fn]] :=
  .lam (parent:=[]) (step:=.arg) rfl (by decide) (.redex_app rfl)
def originalChain : EndpointChain source (some originalParent) [[.arg],[.fn]] :=
  .lam (parent:=[]) (step:=.arg) rfl (by decide) (.redex_app rfl)

def parentOrigin : BetaVertexPreimage event.body event.argument right middle target (some currentParent) (some middleParent) :=
  .proper (.context (by rintro ⟨rest,eq⟩;change [.arg]=[.arg,.body]++rest at eq;have size:=congrArg List.length eq;simp at size))
def earlierParentOrigin : BetaVertexPreimage (.var (.atom 8) 0) oldArgument left source middle (some middleParent) (some originalParent) :=
  .proper (.context (by rintro ⟨rest,eq⟩;cases eq))

def earlierParentTrace : BetaVertexHistoryPreimage event.labels (some middleParent) (some originalParent) :=
  .proper (.one (step:=firstStep) (by rfl)
    (.context (by rintro ⟨rest,eq⟩;cases eq)) (.nil _ _))

theorem actual_cut_alignment : ∃ leaf snapshot,
    ∃g : SpineIncidenceProvenance F source (.atom 7) false cut.spine cut.lookup leaf snapshot,
      Target target [.arg] (snapshot.far false) ∧
      EndpointChain target (snapshot.far false) [[.arg],[.fn]] ∧
      g.SpineFarAlignment [[.arg],[.fn]] ∧
      snapshot.far false=some currentParent := by
  obtain ⟨leaf,snapshot,⟨g⟩⟩ := cut.spine.incidence_leaf_output sourceClosed cut.lookup
  obtain ⟨next,shape,toNext,chain,length,alignment⟩ := cut.spine_after_alignment (by decide) g
  have farEq : snapshot.far false=some currentParent := Source.unique snapshot.fromSpec currentSource
  have nextEq : next=[.arg] := by
    rcases shape with ⟨_,_,_,_,impossible,_⟩ | ⟨parent,child,_,_,eq,_,_,_,same⟩
    · have size:=congrArg List.length impossible;change right.length=right.length+1 at size;omega
    · have equal : parent++[child]=[.arg]++[.body] := eq.symm
      have size:=congrArg List.length equal
      have sameParent:=List.append_inj_left equal (by simpa using size)
      exact same.trans sameParent
  exact ⟨leaf,snapshot,g,nextEq ▸ toNext,chain,alignment,farEq⟩

theorem actual_expanded_far_original_chain :
    ∃leaf snapshot,
      ∃g : SpineIncidenceProvenance F source (.atom 7) false cut.spine cut.lookup leaf snapshot,
        g.SpineFarAlignment [[.arg],[.fn]] ∧
        ∃oldNear oldFar es ds,
          IncidenceChase middle oldNear es ds oldFar ∧
          CreatedReadingExpansion event.body right (right++[.arg]) (right++[.fn,.body]) false es ds ∧
          BetaVertexPreimage event.body event.argument right middle target (snapshot.far false) oldFar ∧
          oldFar=some middleParent ∧EndpointChain middle oldFar [[.arg],[.fn]] ∧
          EndpointChain source (some originalParent) [[.arg],[.fn]] ∧
          BetaVertexHistoryPreimage event.labels (some middleParent) (some originalParent) := by
  obtain ⟨leaf,snapshot,g,toNext,chain,aligned,farEq⟩ := actual_cut_alignment
  obtain ⟨oldNear,oldFar,es,ds,nearTarget,nearOrigin,chase,farOrigin,final,expansion⟩ :=
    origin.incidence_expansion event.turn event.redex reading rfl snapshot.toSpec snapshot.fromSpec
  have oldEq : oldFar=some middleParent := by
    have actualOrigin := farOrigin
    change BetaVertexPreimage event.body event.argument right middle target (snapshot.far false) oldFar at actualOrigin
    rw [farEq] at actualOrigin
    exact actualOrigin.unique parentOrigin
  obtain ⟨oldEdges,oldChain⟩ := endpoint_available_at_beta_preimage event.turn event.redex farOrigin chain
  have exactEdges : oldEdges=[[.arg],[.fn]] := by
    rw [oldEq] at oldChain
    exact oldChain.unique middleChain
  subst oldEdges
  -- The older actual context step locks the expanded FAR at the same ARG
  -- parent; it is not the BODY variable's selected binder.
  have reflected : ∃oldEdges,EndpointChain source (some originalParent) oldEdges := by
    have atMiddle : EndpointChain middle (some middleParent) [[.arg],[.fn]] := oldEq ▸ oldChain
    exact endpoint_available_at_beta_preimage firstStep (by rfl) earlierParentOrigin atMiddle
  obtain ⟨sourceEdges,sourceChain⟩ := reflected
  have sourceEq := sourceChain.unique originalChain
  subst sourceEdges
  exact ⟨leaf,snapshot,g,aligned,oldNear,oldFar,es,ds,chase,expansion,farOrigin,oldEq,oldChain,sourceChain,earlierParentTrace⟩

theorem true_triple_last_selected_singleton :
    let selected : ProperPosition source := BackwardOtherLastFarSourcesChecks.EmptyCopy.sourceBinder
    Source source (right++[.fn,.body]) (some selected) ∧
    EndpointChain source (some selected) [right++[.fn]] ∧
    originalParent.val≠selected.val := by
  refine ⟨BackwardOtherLastFarSourcesChecks.EmptyCopy.originalSource,.redex_lam (p:=right) (by rfl),by decide⟩

theorem same_initial_older_prefix_overlap : INIT original ∧History [[],left,right] original target ∧
    ¬middle.OuterBarsSafe (fun x=>x≠Label.atom 7) ∧cut.after≠[] ∧
    cut.after.length<[right,[.arg],[.fn]].length :=
  ⟨initial,globalHistory.append labels,unsafe_middle,by decide,cut.after_length_lt⟩

end EmptyCopy
namespace Inherited
open PairedCurrentChainSourceLabelsChecks.NoninitialDistinct
open DirectedMarkerSpineIncidenceChecks.DistinctInherited

def cut : ActualUnsafeMarkerCut F [[.fn],[.arg]] source current (.atom 6) leftStart leftEdges where
  before := []
  edge := leftStart
  after := [[.fn,.fn]]
  reader := leftStart
  node := newArgument
  forward := false
  split := rfl
  segment := .refl
  remaining := leftChain
  reading := ⟨Or.inr ⟨_,_,rfl,rfl⟩,rfl⟩
  lookup := rfl
  safeBefore := by intro e h;cases h
  marked := firstMarked
  spine := inheritedSpine
  leaf := inheritedSpine.leaf_output rfl

def currentParent : ProperPosition current := ⟨[.fn],Or.inl ⟨_,_,_,rfl⟩⟩
def middleParent : ProperPosition middle := ⟨[.fn],Or.inl ⟨_,_,_,rfl⟩⟩
def parentOrigin : BetaVertexPreimage lastEvent.body lastEvent.argument [.arg] middle current
    (some currentParent) (some middleParent) :=
  .proper (.context (by rintro ⟨rest,eq⟩;cases eq))
def exactMiddleChain : EndpointChain middle (some middleParent) [[.fn,.fn]] := .redex_app rfl

theorem actual_inherited_nonempty_after : ∃leaf snapshot,
    ∃g : SpineIncidenceProvenance F source (.atom 6) false cut.spine cut.lookup leaf snapshot,
      g.SpineFarAlignment [[.fn,.fn]] ∧
      snapshot.far false=some currentParent ∧
      EndpointChain current (snapshot.far false) [[.fn,.fn]] ∧
      EndpointChain middle (some middleParent) [[.fn,.fn]] ∧
      g.afterSites=leaf.after ∧History leaf.after leaf.target current := by
  obtain ⟨leaf,snapshot,⟨g⟩⟩ := cut.spine.incidence_leaf_output sourceClosed cut.lookup
  obtain ⟨next,shape,toNext,chain,length,aligned⟩ := cut.spine_after_alignment (by decide) g
  have actualSource : Source current leftStart (some currentParent) := ⟨.arg,_,_,rfl,rfl,.arg⟩
  have farEq : snapshot.far false=some currentParent := Source.unique snapshot.fromSpec actualSource
  have atParent : EndpointChain current (some currentParent) [[.fn,.fn]] := farEq ▸ chain
  obtain ⟨oldEdges,oldChain⟩ := endpoint_available_at_beta_preimage lastEvent.turn lastEvent.redex parentOrigin atParent
  have listEq := oldChain.unique exactMiddleChain
  subst oldEdges
  exact ⟨leaf,snapshot,g,aligned,farEq,chain,oldChain,g.afterSites_eq,g.actual_suffix⟩

theorem same_noninitial_actual_history : INIT original ∧History [[],[.fn],[.arg]] original current ∧
    leftStart≠rightStart ∧¬middle.OuterBarsSafe (fun x=>x≠Label.atom 6) ∧
    cut.after≠[] :=
  ⟨initial,prefixHistory.append labels,by decide,unsafeMiddle,by decide⟩
end Inherited

namespace MarkedTerminal
open DirectedMarkerSpineIncidenceChecks.Nested

/-- Nonempty marker continuation tests the marked recursive branch. The
actual successful chain is terminal; it does not have a nonempty AFTER. -/
theorem forward_marked_alignment : ∃leaf snapshot,
    ∃g : SpineIncidenceProvenance family sourceWrapped (.atom 10) true forwardSpine
      (by rfl : targetForward.subterm [.fn]=some UniformOldNodeLabelSuffixChecks.target) leaf snapshot,
      leaf.continuation≠[] ∧g.SpineFarAlignment [[.fn]] ∧
      PrerequisiteChain targetForward [] ([.fn]::([] : List Path)) := by
  obtain ⟨leaf,snapshot,⟨g⟩,nonempty⟩ := forward_nonempty
  let vertex : ProperPosition targetForward := ⟨[.fn],Or.inr ⟨_,_,rfl⟩⟩
  have toVertex : Target targetForward [.fn] (some vertex) := Or.inl rfl
  have farEq : snapshot.far true=some vertex := Target.unique snapshot.toSpec toVertex
  have chain : EndpointChain targetForward (snapshot.far true) [[.fn]] := by
    rw [farEq];exact PrerequisiteChain.redex_lam (p:=[]) rfl
  exact ⟨leaf,snapshot,g,nonempty,g.align_successful_far chain,.redex_app rfl⟩

theorem reverse_marked_alignment : ∃leaf snapshot,
    ∃g : SpineIncidenceProvenance family sourceWrapped (.atom 10) false reverseSpine
      (by rfl : targetReverse.subterm [.fn]=some reverseResult) leaf snapshot,
      leaf.continuation≠[] ∧g.SpineFarAlignment [[.fn]] ∧
      PrerequisiteChain targetReverse [.fn] ([.fn]::([] : List Path)) := by
  obtain ⟨leaf,snapshot,⟨g⟩,nonempty⟩ := reverse_nonempty
  let vertex : ProperPosition targetReverse := ⟨[],Or.inl ⟨_,_,_,rfl⟩⟩
  have fromVertex : Source targetReverse [.fn] (some vertex) := ⟨.fn,_,_,rfl,rfl,.fn⟩
  have farEq : snapshot.far false=some vertex := Source.unique snapshot.fromSpec fromVertex
  have chain : EndpointChain targetReverse (snapshot.far false) [[.fn]] := by
    rw [farEq];exact PrerequisiteChain.redex_app rfl
  exact ⟨leaf,snapshot,g,nonempty,g.align_successful_far chain,.redex_lam (p:=[]) rfl⟩
end MarkedTerminal

#print axioms PrerequisiteChain.after_snapshot
#print axioms BetaIncomingReadingOrigin.first_far_singleton
#print axioms SpineIncidenceProvenance.align_successful_far
#print axioms ActualUnsafeMarkerCut.align_after_snapshot
#print axioms ActualUnsafeMarkerCut.spine_after_alignment
#print axioms EmptyCopy.earlierParentTrace
#print axioms EmptyCopy.actual_cut_alignment
#print axioms EmptyCopy.actual_expanded_far_original_chain
#print axioms EmptyCopy.true_triple_last_selected_singleton
#print axioms EmptyCopy.same_initial_older_prefix_overlap
#print axioms Inherited.actual_inherited_nonempty_after
#print axioms Inherited.same_noninitial_actual_history
#print axioms MarkedTerminal.forward_marked_alignment
#print axioms MarkedTerminal.reverse_marked_alignment
end Lamping.Checks.ActualSpineAfterAlignmentChecks
