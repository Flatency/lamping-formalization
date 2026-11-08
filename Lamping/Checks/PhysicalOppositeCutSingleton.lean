import Lamping.Lamping.PhysicalOppositeCutSingleton
import Lamping.Checks.FunctionWrappedReachable
import Lamping.Lamping.LabelledGraphEvents
import Lamping.Lamping.InitialJointRepresentation

namespace Lamping.Checks.PhysicalOppositeCutSingleton
open AG Graph Lambda Lambda.Labelled
open FunctionWrappedReachable WrappedSuccessfulChains

private abbrev node : LTerm := .lam functionLabel
  (.app (.atom 5) (.var (.atom 6) 0) (.lam (.atom 7) (.var (.atom 8) 0)))

private theorem sourceInitial : INIT FunctionWrappedReachable.original := init_is_INIT _
private theorem sourceClosed : Closed FunctionWrappedReachable.original.erase := WrappedSuccessfulChains.sourceClosed
private theorem atNode : FunctionWrappedReachable.current.subterm [.fn]=some node := rfl
private theorem chosen (p : Path) (inside : p∈([[.fn]] : List Path)) :
    FunctionWrappedReachable.original.degreeAt p=some (.atom 2) := by
  have equal := List.mem_singleton.mp inside
  subst p
  rfl
private theorem marked : ¬node.label.OuterBarsSafe (fun d=>d≠.atom 2) := by
  intro safe
  exact safe.1 rfl

private def complete : Marked.CompleteOldDevelopment
    (concrete.site.betaSyntaxFiber (.inl ()) FunctionWrappedReachable.original.erase)
    FunctionWrappedReachable.original.erase [[.fn]] endpoint :=
  (Marked.completeOld_iff _ _).mpr ⟨relative,by simp [endpoint,Marked.Normal]⟩

private def old : Marked.RelativeOldHistory [[.fn]] [[.fn]]
    (Marked.mark [[.fn]] FunctionWrappedReachable.original.erase) endpoint := by
  have actual := complete.1
  change Marked.RelativeOldHistory (concrete.site.betaSyntaxFiber (.inl ()) term) [[.fn]]
    (Marked.mark (concrete.site.betaSyntaxFiber (.inl ()) term) term) endpoint at actual
  rw [actual_fiber] at actual
  exact actual

private def leftRead : PrerequisiteReadsDirected FunctionWrappedReachable.current [] [.fn] true :=
  ⟨Or.inl ⟨_,_,_,rfl,rfl⟩,rfl⟩
private def rightRead : PrerequisiteReadsDirected FunctionWrappedReachable.current [.fn] [.fn] false :=
  ⟨Or.inr ⟨_,_,rfl,rfl⟩,rfl⟩

private def leftCut : ActualUnsafeMarkerCut [[.fn]] [[.fn]] FunctionWrappedReachable.original
    FunctionWrappedReachable.current (.atom 2) [] [[.fn]] where
  before := []
  edge := [.fn]
  after := []
  reader := []
  node := node
  forward := true
  split := rfl
  segment := .refl
  remaining := .redex_app rfl
  reading := leftRead
  lookup := atNode
  safeBefore := by intro e inside;cases inside
  marked := marked
  spine := old.directed_marker_spine actualHistory chosen (sourceInitial.outerBarsSafe _)
    .refl leftRead atNode marked (by intro e inside;cases inside)
  leaf := (old.directed_marker_spine actualHistory chosen (sourceInitial.outerBarsSafe _)
    .refl leftRead atNode marked (by intro e inside;cases inside)).leaf_output atNode

private def rightCut : ActualUnsafeMarkerCut [[.fn]] [[.fn]] FunctionWrappedReachable.original
    FunctionWrappedReachable.current (.atom 2) [.fn] [[.fn]] where
  before := []
  edge := [.fn]
  after := []
  reader := [.fn]
  node := node
  forward := false
  split := rfl
  segment := .refl
  remaining := .redex_lam (p:=[]) rfl
  reading := rightRead
  lookup := atNode
  safeBefore := by intro e inside;cases inside
  marked := marked
  spine := old.directed_marker_spine actualHistory chosen (sourceInitial.outerBarsSafe _)
    .refl rightRead atNode marked (by intro e inside;cases inside)
  leaf := (old.directed_marker_spine actualHistory chosen (sourceInitial.outerBarsSafe _)
    .refl rightRead atNode marked (by intro e inside;cases inside)).leaf_output atNode

/-- Same real initial graph, actual beta event and its marked target;
the selector is supplied internally on that target graph, never re-encoded. -/
theorem actual_closed_beta_opposite_singletons :
    INIT FunctionWrappedReachable.original ∧Closed FunctionWrappedReachable.original.erase ∧
    GraphStep (.beta 0) (ActualNet.initial term) (ActualNet.ofNet concrete.site.reduce) ∧
    ∃ raw : ParallelHistory FunctionWrappedReachable.original.erase FunctionWrappedReachable.current.erase,
      LabelledGraphEvent (.beta 0) (ActualNet.initial term) (ActualNet.ofNet concrete.site.reduce)
        (.inl ()) FunctionWrappedReachable.original FunctionWrappedReachable.current raw ∧
      History [[.fn]] FunctionWrappedReachable.original FunctionWrappedReachable.current ∧
      ∃ selection : OccurrenceFragmentSelection FunctionWrappedReachable.current concrete.site.reduce (.inl ()),
        SameChainRepresentation selection leftCut.remaining rightCut.remaining ∧
        leftCut.forward≠rightCut.forward ∧leftCut.before=[] ∧rightCut.before=[] ∧
        leftCut.after=[] ∧rightCut.after=[] := by
  let raw : ParallelHistory FunctionWrappedReachable.original.erase FunctionWrappedReachable.current.erase :=
    .single ⟨[[.fn]],endpoint,complete,rfl⟩
  have event : LabelledGraphEvent (.beta 0) (ActualNet.initial term) (ActualNet.ofNet concrete.site.reduce)
      (.inl ()) FunctionWrappedReachable.original FunctionWrappedReachable.current raw :=
    .beta concrete.kept concrete.site concrete.sourceIso (.refl _) complete actualHistory rfl
  obtain ⟨selection⟩ := beta_matches.occurrence_fragment_selection (actualHistory.closed sourceClosed)
  let leftParent : PrerequisiteChain FunctionWrappedReachable.current [] [[.fn]] := .redex_app rfl
  let rightParent : PrerequisiteChain FunctionWrappedReachable.current [.fn] [[.fn]] := .redex_lam (p:=[]) rfl
  have physical : SameChainRepresentation selection leftParent rightParent := rfl
  have opposite : leftCut.forward≠rightCut.forward := by change true≠false;decide
  obtain ⟨_leftLength,_rightLength,lb,rb,la,ra⟩ := actual_physical_parent_opposite_cut_singleton
    beta_matches sourceClosed actualHistory selection leftParent rightParent
      physical leftCut rightCut rfl opposite
  exact ⟨sourceInitial,sourceClosed,actual_beta_step,raw,event,actualHistory,selection,physical,opposite,lb,rb,la,ra⟩

#print axioms actual_closed_beta_opposite_singletons
end Lamping.Checks.PhysicalOppositeCutSingleton
