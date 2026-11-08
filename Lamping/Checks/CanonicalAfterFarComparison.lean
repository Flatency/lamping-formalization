import Lamping.Lamping.CanonicalAfterFarComparison
import Lamping.Checks.ActualSpineAfterAlignment
import Lamping.Checks.ForwardFarChainComparison
namespace Lamping.Checks.CanonicalAfterFarComparisonChecks
open Graph Lambda Lambda.Labelled AG SyntaxIncidence
namespace EmptyCopy
open UniformOldCreatedIncomingLabelsChecks.Distinct
open ActualSpineAfterAlignmentChecks.EmptyCopy

def ownParentTrace : BetaNodeHistoryPreimage labels [.arg] [.arg] :=
  .one (step:=firstStep) (by rfl)
    (.context (by rintro ⟨rest,eq⟩;cases eq))
    (.one (step:=secondStep) (by rfl)
      (.context (by rintro ⟨rest,eq⟩;change [.arg]=[.arg,.body]++rest at eq;have size:=congrArg List.length eq;simp at size)) (.nil _ _))

private theorem exact_original
    (snapshot : IncomingIncidenceSnapshot target cut.edge)
    (far : snapshot.far false=some currentParent)
    (output : CanonicalAfterFarOutput labels cut snapshot) :
    output.currentProper.val=[.arg] ∧output.sourceProper.val=[.arg] ∧
      output.sourceEdges=[[.arg],[.fn]] := by
  have vertexEq : output.currentProper=currentParent := Option.some.inj (output.farEq.symm.trans far)
  have currentEq : output.currentProper.val=[.arg] := congrArg Subtype.val vertexEq
  have trace : BetaNodeHistoryPreimage labels [.arg] output.sourceProper.val := by
    exact Eq.mp (congrArg (fun p : Path => BetaNodeHistoryPreimage labels p output.sourceProper.val) currentEq) output.nodeTrace
  have sourceEq := trace.unique ownParentTrace
  have actualChain : PrerequisiteChain source [.arg] output.sourceEdges := by
    exact Eq.mp (congrArg (fun p : Path => PrerequisiteChain source p output.sourceEdges) sourceEq) output.sourceChain
  exact ⟨currentEq,sourceEq,actualChain.unique originalChain⟩

private theorem tail_safe (e : Path) (member : e∈cut.after) : degreeReadSafe (.atom 7) (target.labelAt e) := by
  change e∈([[.arg],[.fn]] : List Path) at member
  rcases List.mem_cons.mp member with rfl | member
  · intro label eq
    have same := Option.some.inj eq
    subst label
    exact source_safe.2.2.1
  · have same:=List.mem_singleton.mp member
    subst e
    intro label eq
    have same := Option.some.inj eq
    subst label
    exact source_safe.2.1.1

private theorem no_tail_cut
    (tailCut : ActualUnsafeMarkerCut F [left,right] source target (.atom 7) start cut.after) : False := by
  have member : tailCut.edge∈cut.after := by
    exact Eq.mp (congrArg (fun xs : List Path => tailCut.edge∈xs) tailCut.split.symm)
      (List.mem_append_right _ List.mem_cons_self)
  exact tailCut.marked (tail_safe _ member _ (by simp only [LTerm.labelAt,tailCut.lookup,Option.map_some]))

theorem canonical_matches_actual_parent_history
    (snapshot : IncomingIncidenceSnapshot target cut.edge)
    (far : snapshot.far false=some currentParent)
    (output : CanonicalAfterFarOutput labels cut snapshot) :
    some originalParent=some output.sourceProper := by
  have currentEq : output.currentProper=currentParent := Option.some.inj (output.farEq.symm.trans far)
  have actual : BetaVertexHistoryPreimage labels (some output.currentProper) (some originalParent) :=
    Eq.mp (congrArg (fun v : ProperPosition target => BetaVertexHistoryPreimage labels (some v) (some originalParent)) currentEq.symm)
      (BetaVertexHistoryPreimage.proper ownParentTrace)
  exact output.vertex_unique actual

/-- The generic NEW comparison, not merely availability, gives the entire
original chain at the actual ARG parent after a nonempty older prefix. -/
theorem actual_q0_full_source_vectors : ∃leaf snapshot,
    ∃g : SpineIncidenceProvenance F source (.atom 7) false cut.spine cut.lookup leaf snapshot,
      ∃left right : CanonicalAfterFarOutput labels cut snapshot,
        g.SpineFarAlignment cut.after ∧CanonicalFarFullComparison sourceClosed left right ∧
        left.currentProper.val=[.arg] ∧left.sourceProper.val=[.arg] ∧
        right.currentProper.val=[.arg] ∧right.sourceProper.val=[.arg] ∧
        left.sourceEdges=[[.arg],[.fn]] ∧right.sourceEdges=[[.arg],[.fn]] ∧
        BetaVertexHistoryPreimage labels (some left.currentProper) (some left.sourceProper) := by
  obtain ⟨leaf,snapshot,g,_,_,aligned,far⟩ := actual_cut_alignment
  obtain ⟨l,r,result⟩ := canonical_after_far_comparison initial globalHistory sourceClosed old labels selected source_safe
    cut cut (by decide) (by decide) snapshot snapshot (ChainIncidenceIso.refl _)
  have good : CanonicalFarFullComparison sourceClosed l r := by
    rcases result with safe | same | opposite
    · exact safe.2
    · obtain ⟨lc,_,_⟩:=same;exact False.elim (no_tail_cut lc)
    · obtain ⟨lc,_,_⟩:=opposite;exact False.elim (no_tail_cut lc)
  obtain ⟨lc,lo,le⟩ := exact_original snapshot far l
  obtain ⟨rc,ro,re⟩ := exact_original snapshot far r
  exact ⟨leaf,snapshot,g,l,r,aligned,good,lc,lo,rc,ro,le,re,l.vertexTrace⟩

/-- Canonical FAR is parent ARG, whereas the actual triple LAST Source is
selected right.fn. No trace or label equates these coordinates. -/
theorem triple_last_remains_distinct :
    originalParent.val≠BackwardOtherLastFarSourcesChecks.EmptyCopy.sourceBinder.val ∧
    INIT original ∧History [[],left,right] original target :=
  ⟨by decide,initial,globalHistory.append labels⟩
end EmptyCopy
namespace TwoCopies
open ForwardFarChainComparisonChecks.TwoCopies
abbrev leftNode : LTerm := argument.prepend ((Label.atom 4).concat (Label.atom 1).under)
abbrev rightNode : LTerm := argument.prepend ((Label.atom 8).concat (Label.atom 1).under)

theorem leftMarked : ¬leftNode.label.OuterBarsSafe (fun x=>x≠Label.atom 1) :=
  event.turn.created_label_not_safe event.redex (by rfl : target.subterm [.fn,.fn]=some leftNode)
    (by decide)
theorem rightMarked : ¬rightNode.label.OuterBarsSafe (fun x=>x≠Label.atom 1) :=
  event.turn.created_label_not_safe event.redex (by rfl : target.subterm [.arg,.fn]=some rightNode)
    (by decide)

def leftSpine : DirectedMarkerSpine F source (.atom 1) true [[]] target [] [.fn,.fn] :=
  event.final_old.directed_marker_spine event.final_history selected (initial.outerBarsSafe _) .refl
    leftReading rfl leftMarked (by intro e h;cases h)
def rightSpine : DirectedMarkerSpine F source (.atom 1) true [[]] target [] [.arg,.fn] :=
  event.final_old.directed_marker_spine event.final_history selected (initial.outerBarsSafe _) .refl
    rightReading rfl rightMarked (by intro e h;cases h)

def leftCut : ActualUnsafeMarkerCut F [[]] source target (.atom 1) [.fn] [[.fn,.fn],[.fn,.fn,.fn]] where
  before:=[]
  edge:=[.fn,.fn]
  after:=[[.fn,.fn,.fn]]
  reader:=[.fn]
  node:=leftNode
  forward:=true
  split:=rfl
  segment:=.refl
  remaining:=leftRemaining
  reading:=leftReading
  lookup:=rfl
  safeBefore:=by intro e h;cases h
  marked:=leftMarked
  spine:=leftSpine
  leaf:=leftSpine.leaf_output rfl

def rightCut : ActualUnsafeMarkerCut F [[]] source target (.atom 1) [.arg] [[.arg,.fn],[.arg,.fn,.fn]] where
  before:=[]
  edge:=[.arg,.fn]
  after:=[[.arg,.fn,.fn]]
  reader:=[.arg]
  node:=rightNode
  forward:=true
  split:=rfl
  segment:=.refl
  remaining:=rightRemaining
  reading:=rightReading
  lookup:=rfl
  safeBefore:=by intro e h;cases h
  marked:=rightMarked
  spine:=rightSpine
  leaf:=rightSpine.leaf_output rfl

def leftProper : ProperPosition target := ⟨[.fn,.fn],Or.inl ⟨_,_,_,rfl⟩⟩
def rightProper : ProperPosition target := ⟨[.arg,.fn],Or.inl ⟨_,_,_,rfl⟩⟩

def leftOwnTrace : BetaNodeHistoryPreimage event.final_history leftProper.val [.arg] := by
  apply BetaNodeHistoryPreimage.one (step:=event.turn) event.redex
  · simpa only [List.nil_append,List.append_nil] using
      (BetaNodePreimage.copied (body:=body) (argument:=argument) (site:=[]) (q:=[.fn,.fn]) (relative:=[]) (old:=argument) rfl rfl)
  · exact .nil _ _
def rightOwnTrace : BetaNodeHistoryPreimage event.final_history rightProper.val [.arg] := by
  apply BetaNodeHistoryPreimage.one (step:=event.turn) event.redex
  · simpa only [List.nil_append,List.append_nil] using
      (BetaNodePreimage.copied (body:=body) (argument:=argument) (site:=[]) (q:=[.arg,.fn]) (relative:=[]) (old:=argument) rfl rfl)
  · exact .nil _ _

private theorem exact_origin
    {parentCut : ActualUnsafeMarkerCut F [[]] source target (.atom 1) start edges}
    {snapshot : IncomingIncidenceSnapshot target parentCut.edge}
    (output : CanonicalAfterFarOutput event.final_history parentCut snapshot)
    (vertex : ProperPosition target)
    (farEq : snapshot.far parentCut.forward=some vertex)
    (known : BetaNodeHistoryPreimage event.final_history vertex.val [.arg]) :
    output.currentProper.val=vertex.val ∧output.sourceProper.val=[.arg] ∧output.sourceEdges=[[.arg,.fn]] := by
  have currentEq := congrArg Subtype.val (Option.some.inj (output.farEq.symm.trans farEq))
  have trace : BetaNodeHistoryPreimage event.final_history vertex.val output.sourceProper.val :=
    Eq.mp (congrArg (fun p : Path => BetaNodeHistoryPreimage event.final_history p output.sourceProper.val) currentEq) output.nodeTrace
  have sourceEq := trace.unique known
  have actualChain : PrerequisiteChain source [.arg] output.sourceEdges :=
    Eq.mp (congrArg (fun p : Path => PrerequisiteChain source p output.sourceEdges) sourceEq) output.sourceChain
  exact ⟨currentEq,sourceEq,actualChain.unique sourceTail⟩

private theorem no_left_tail_cut
    (tailCut : ActualUnsafeMarkerCut F [[]] source target (.atom 1) start leftCut.after) : False := by
  have member : tailCut.edge∈leftCut.after :=
    Eq.mp (congrArg (fun xs : List Path => tailCut.edge∈xs) tailCut.split.symm)
      (List.mem_append_right _ List.mem_cons_self)
  have chosen := List.mem_singleton.mp member
  have atNode : target.subterm tailCut.edge=some (.lam (.atom 12) (.var (.atom 13) 0)) := by rw [chosen];rfl
  have same := Option.some.inj (tailCut.lookup.symm.trans atNode)
  apply tailCut.marked
  rw [same]
  trivial

/-- Different CURRENT proper FAR APPs in ONE actual nonINIT reduct. Both
OWN traces, positions and full old-chain vectors are derived by the NEW top. -/
theorem actual_two_distinct_canonical_fars : ∃leftSnapshot rightSnapshot,
    ∃left : CanonicalAfterFarOutput event.final_history leftCut leftSnapshot,
      ∃right : CanonicalAfterFarOutput event.final_history rightCut rightSnapshot,
        CanonicalFarFullComparison closed left right ∧
        left.currentProper.val=[.fn,.fn] ∧right.currentProper.val=[.arg,.fn] ∧
        left.currentProper.val≠right.currentProper.val ∧
        left.sourceProper.val=[.arg] ∧right.sourceProper.val=[.arg] ∧
        left.sourceEdges=[[.arg,.fn]] ∧right.sourceEdges=[[.arg,.fn]] := by
  obtain ⟨_leftLeaf,leftSnapshot,_leftGeometry⟩ := leftSpine.incidence_leaf_output closed leftCut.lookup
  obtain ⟨_rightLeaf,rightSnapshot,_rightGeometry⟩ := rightSpine.incidence_leaf_output closed rightCut.lookup
  have currentIso := actual_chain_iso_of_labels event.final_history initial targetClosed leftTail rightTail rfl
  obtain ⟨left,right,result⟩ := canonical_after_far_comparison initial (.nil source) closed event.final_old event.final_history
    selected (initial.outerBarsSafe _) leftCut rightCut (by decide) (by decide) leftSnapshot rightSnapshot (Classical.choice currentIso)
  have good : CanonicalFarFullComparison closed left right := by
    rcases result with safe | same | opposite
    · exact safe.2
    · obtain ⟨lc,_,_⟩ := same;exact False.elim (no_left_tail_cut lc)
    · obtain ⟨lc,_,_⟩ := opposite;exact False.elim (no_left_tail_cut lc)
  have leftFar : leftSnapshot.far true=some leftProper := Target.unique leftSnapshot.toSpec (Or.inl rfl)
  have rightFar : rightSnapshot.far true=some rightProper := Target.unique rightSnapshot.toSpec (Or.inl rfl)
  obtain ⟨lc,lo,le⟩ := exact_origin left leftProper leftFar leftOwnTrace
  obtain ⟨rc,ro,re⟩ := exact_origin right rightProper rightFar rightOwnTrace
  exact ⟨leftSnapshot,rightSnapshot,left,right,good,lc,rc,by rw [lc,rc];decide,lo,ro,le,re⟩

theorem same_initial_noninitial_current : INIT source ∧History [[]] source target ∧¬INIT target :=
  ⟨initial,event.final_history,root_contract_not_INIT _ _ _ _⟩
end TwoCopies

namespace TerminalBoundary
open DirectedReadingDecompositionChecks
open PairedCurrentChainSourceLabelsChecks.Terminal

/-- An actual previously proved terminal exception remains a boundary of
this new comparator. This is not claimed to be a nonempty parent-AFTER
fixture or a counterexample to the new trichotomy. -/
theorem actual_terminal_opposite_not_full_source_match :
    (∃left : ActualUnsafeMarkerCut [[.fn]] [[.fn]] source target (.atom 2) [] [[.fn]],
      ∃right : ActualUnsafeMarkerCut [[.fn]] [[.fn]] source target (.atom 2) [.fn] [[.fn]],
        left.after=[] ∧right.after=[] ∧left.forward≠right.forward) ∧
    (¬∃es fs,PrerequisiteChain source [] es ∧PrerequisiteChain source [.fn,.arg] fs ∧
      es.map source.labelAt=fs.map source.labelAt) :=
  ⟨actual_opposite_terminal_exception,no_complete_old_label_match⟩
end TerminalBoundary

#print axioms ActualUnsafeMarkerCut.canonical_far_output
#print axioms CanonicalAfterFarOutput.vertex_unique
#print axioms canonical_after_far_comparison
#print axioms EmptyCopy.ownParentTrace
#print axioms EmptyCopy.canonical_matches_actual_parent_history
#print axioms EmptyCopy.actual_q0_full_source_vectors
#print axioms EmptyCopy.triple_last_remains_distinct
#print axioms TwoCopies.actual_two_distinct_canonical_fars
#print axioms TwoCopies.same_initial_noninitial_current
#print axioms TerminalBoundary.actual_terminal_opposite_not_full_source_match
end Lamping.Checks.CanonicalAfterFarComparisonChecks


