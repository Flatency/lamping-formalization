import Lamping.Lamping.TerminalHeadSuppliers
import Lamping.Checks.NormalFalseCanonicalOriginalComparison
import Lamping.Checks.PairedMarkerSpineReannotation
import Lamping.Checks.ActualUnsafeMarkerLeaves
import Lamping.Checks.SingleUnsafeCopyFunctionAppInputs

namespace Lamping.Checks.TerminalHeadSuppliersChecks
open Graph Lambda Lambda.Labelled AG

namespace Larger
open NormalFalseCanonicalOriginalComparisonChecks.Terminal
abbrev F : List Path := [[]]
abbrev degree : Label := .atom 1
abbrev node : LTerm := .lam (((Label.atom 3).concat degree.under).concat (.atom 6)) (.var (.atom 7) 0)
abbrev edges : List Path := [[.arg],[.fn]]

theorem initial : INIT original := init_is_INIT _
theorem sourceClosed : Closed original.erase := by
  change (0<1 ∧0<2) ∧0<1
  decide
theorem targetClosed : Closed current.erase := actualHistory.closed sourceClosed
def old : Marked.RelativeOldHistory F [[]] (Marked.mark F original.erase)
    (.app [] (.lam (.var 0)) (.lam (.var 0))) :=
  .cons (.redRoot _ _ _) (by decide) (.nil _)
theorem selected (p : Path) (member : p∈F) : original.degreeAt p=some degree := by
  have same := List.mem_singleton.mp member
  subst p
  rfl

def leftChain : PrerequisiteChain current [.arg] edges :=
  .lam (parent:=[]) (step:=.arg) rfl (by decide) (.redex_app (p:=[]) rfl)
def rightChain : PrerequisiteChain current [.arg,.body] edges :=
  .var (parent:=[.arg]) (rest:=[]) rfl rfl rfl rfl leftChain
def leftPrefix : PrerequisitePrefix current [.arg] [[.arg]] [] :=
  .lam (parent:=[]) (step:=.arg) rfl (by decide) .refl
def rightPrefix : PrerequisitePrefix current [.arg,.body] [[.arg]] [] :=
  .var (parent:=[.arg]) (rest:=[]) rfl rfl rfl rfl leftPrefix
theorem reading : PrerequisiteReadsDirected current [] [.fn] true := ⟨Or.inl ⟨_,_,_,rfl,rfl⟩,rfl⟩
theorem lookup : current.subterm [.fn]=some node := rfl
theorem marked : ¬node.label.OuterBarsSafe (fun d=>d≠degree) := by
  intro safe
  change (degree≠degree) ∧True at safe
  exact safe.1 rfl
theorem beforeSafe (e : Path) (member : e∈([[.arg]] : List Path)) :
    degreeReadSafe degree (current.labelAt e) := by
  have same := List.mem_singleton.mp member
  subst e
  intro label equal
  have actual : label=Label.atom 4 := Option.some.inj equal.symm
  subst label
  trivial
private theorem beforeLookupSafe (e : Path) (member : e∈([[.arg]] : List Path))
    (t : LTerm) (atNode : current.subterm e=some t) : t.label.OuterBarsSafe (fun d=>d≠degree) :=
  beforeSafe e member t.label (by simp only [LTerm.labelAt,atNode,Option.map_some])

def leftSpine : DirectedMarkerSpine F original degree true [[]] current
    ([[.arg]].map current.labelAt) [.fn] :=
  old.directed_marker_spine actualHistory selected (initial.outerBarsSafe _)
    leftPrefix reading lookup marked beforeLookupSafe
def rightSpine : DirectedMarkerSpine F original degree true [[]] current
    ([[.arg]].map current.labelAt) [.fn] :=
  old.directed_marker_spine actualHistory selected (initial.outerBarsSafe _)
    rightPrefix reading lookup marked beforeLookupSafe

def leftCut : ActualUnsafeMarkerCut F [[]] original current degree [.arg] edges where
  before := [[.arg]]
  edge := [.fn]
  after := []
  reader := []
  node := node
  forward := true
  split := rfl
  segment := leftPrefix
  remaining := .redex_app (p:=[]) rfl
  reading := reading
  lookup := lookup
  safeBefore := beforeSafe
  marked := marked
  spine := leftSpine
  leaf := leftSpine.leaf_output lookup
def rightCut : ActualUnsafeMarkerCut F [[]] original current degree [.arg,.body] edges where
  before := [[.arg]]
  edge := [.fn]
  after := []
  reader := []
  node := node
  forward := true
  split := rfl
  segment := rightPrefix
  remaining := .redex_app (p:=[]) rfl
  reading := reading
  lookup := lookup
  safeBefore := beforeSafe
  marked := marked
  spine := rightSpine
  leaf := rightSpine.leaf_output lookup

/-- Former HAND candidate, now all facts are kernel data: original INIT,
root OLD, before1/after0, distinct starts and a real zero-edge binder jump. -/
theorem actual_larger_terminal_context :
    INIT original ∧Closed original.erase ∧History [[]] original current ∧
    Marked.RelativeOldHistory F [[]] (Marked.mark F original.erase)
      (.app [] (.lam (.var 0)) (.lam (.var 0))) ∧
    original.degreeAt []=some degree ∧
    current.labelAt [.arg]=some (.atom 4) ∧
    current.labelAt [.fn]=some node.label ∧
    ¬node.label.OuterBarsSafe (fun d=>d≠degree) ∧
    PrerequisiteChain current [.arg] edges ∧PrerequisiteChain current [.arg,.body] edges ∧
    ([.arg] : Path)≠[.arg,.body] ∧leftCut.before.length=1 ∧rightCut.before.length=1 ∧
    leftCut.after=[] ∧rightCut.after=[] ∧edges.length=2 :=
  ⟨initial,sourceClosed,actualHistory,old,rfl,rfl,rfl,marked,leftChain,rightChain,
    by decide,rfl,rfl,rfl,rfl,rfl⟩

theorem actual_singleton_supply :
    ∃_lc : PrerequisiteChain current leftCut.reader [leftCut.edge],
    ∃_rc : PrerequisiteChain current rightCut.reader [rightCut.edge],
      current.labelAt leftCut.edge=current.labelAt rightCut.edge ∧
      ChainIncidenceIsomorphic (chainSyntaxIncidence current targetClosed [leftCut.edge])
        (chainSyntaxIncidence current targetClosed [rightCut.edge]) :=
  actual_terminal_cut_singletons initial actualHistory targetClosed leftCut rightCut rfl rfl (.refl _)

theorem actual_strict_current_physical
    {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
    {g : Net signature N B W} {root : B}
    (selection : OccurrenceFragmentSelection current g root)
    (ih : ChainForwardBelow targetClosed selection 2) :
    ∃lc : PrerequisiteChain current leftCut.reader [leftCut.edge],
    ∃rc : PrerequisiteChain current rightCut.reader [rightCut.edge],
      SameChainRepresentation selection lc rc :=
  actual_terminal_cut_physical_below initial actualHistory targetClosed selection leftCut rightCut
    rfl rfl (.refl _) (by decide) ih

/-- SAME physical edge/selector/localHistory and literal reduced seam.
Only a strictly-shorter CURRENT IH is supplied, never target REP. -/
theorem actual_given_parent_evaluated_heads
    {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
    {kept : K→Graph.Label signature} {i : Nat}
    (site : PathSite (.beta i) kept (B:=B) (W:=W) (V:=V)) {root : B}
    {localTarget : LTerm} {edge : BetaEdge site.net}
    {selection : SourceEdgeSelection (initLabels original.erase) site.net root}
    {targetSelection : OccurrenceFragmentSelection current site.reduce root}
    (geometry : SiteBetaGeometry site edge)
    (left : EvaluatedChainResiduals site (localTarget:=localTarget) edge selection targetSelection leftChain)
    (right : EvaluatedChainResiduals site (localTarget:=localTarget) edge selection targetSelection rightChain)
    (ih : ChainForwardBelow targetClosed targetSelection 2) :
    selection.evalLabel edge (left.node ⟨[.fn],by decide⟩).label=
      selection.evalLabel edge (right.node ⟨[.fn],by decide⟩).label := by
  obtain ⟨lc,rc,same⟩ := actual_strict_current_physical targetSelection ih
  let lm : {p : Path // p∈edges} := ⟨[.fn],by decide⟩
  let rm : {p : Path // p∈edges} := ⟨[.fn],by decide⟩
  have pieces := same_chain_representation_slot (n:=0) targetSelection lc rc same
    (actualChainPosition leftChain lm) (actualChainPosition rightChain rm) (by rfl) (by rfl)
  have other := right.residual rm
  rw [←pieces] at other
  exact (left.residual lm).source_unique site geometry other
end Larger

namespace RootOverlap
open DirectedReadingDecompositionChecks
open PairedCurrentChainSourceLabelsChecks.Terminal

theorem actual_opposite_collapses :
    ∃left : ActualUnsafeMarkerCut [[.fn]] [[.fn]] source target (.atom 2) [] [[.fn]],
    ∃right : ActualUnsafeMarkerCut [[.fn]] [[.fn]] source target (.atom 2) [.fn] [[.fn]],
      left.forward=true ∧right.forward=false ∧left.before=[] ∧right.before=[] ∧
      left.after=[] ∧right.after=[] := by
  obtain ⟨left,right,_lt,_rt,ld,rd,_leaves⟩ := ActualUnsafeMarkerLeavesChecks.Terminal.actual_terminal_leaves
  have opposite : left.forward≠right.forward := by rw [ld,rd];decide
  obtain ⟨_one,_other,lb,rb,la,ra⟩ := actual_parent_opposite_cut_singleton initial history currentClosed
    left right (.refl _) opposite
  exact ⟨left,right,ld,rd,lb,rb,la,ra⟩

theorem actual_own_lambda_source_chains :
    ∃es fs,PrerequisiteChain source [.fn,.arg] es ∧PrerequisiteChain source [.fn,.arg] fs ∧
      es=[[.fn,.arg],[.fn,.fn]] ∧fs=[[.fn,.arg],[.fn,.fn]] ∧
      es.map source.labelAt=fs.map source.labelAt ∧
      ChainIncidenceIsomorphic (chainSyntaxIncidence source closed es) (chainSyntaxIncidence source closed fs) := by
  obtain ⟨es,fs,lc,rc,same,iso⟩ := actual_redex_lambda_origin_chain_comparison
    initial (.nil source) old history selected sourceSafe closed
    (lp:=[]) (rp:=[]) (by rfl) (by rfl) rfl lamTrace lamTrace
  exact ⟨es,fs,lc,rc,lc.unique oldLam,rc.unique oldLam,same,iso⟩

theorem retained_original_start_negative :
    ¬∃es fs,PrerequisiteChain source [] es ∧PrerequisiteChain source [.fn,.arg] fs ∧
      es.map source.labelAt=fs.map source.labelAt := no_complete_old_label_match
end RootOverlap

namespace CP53
open SingleUnsafeCopyFunctionAppInputsChecks

theorem actual_distinct_lambda_origins :
    ∃oldLeft oldRight,
      BetaNodeHistoryPreimage event.final_history (leftHead++[.fn]) oldLeft ∧
      BetaNodeHistoryPreimage event.final_history (rightHead++[.fn]) oldRight ∧
      leftHead++[.fn]≠rightHead++[.fn] ∧
      ∃es fs,PrerequisiteChain source oldLeft es ∧PrerequisiteChain source oldRight fs ∧
        es.map source.labelAt=fs.map source.labelAt ∧
        ChainIncidenceIsomorphic (chainSyntaxIncidence source sourceClosed es)
          (chainSyntaxIncidence source sourceClosed fs) := by
  have ll : target.subterm (leftHead++[.fn])=some (.lam (.atom 17) (.app (.atom 18) (.var (.atom 19) 0) (.var (.atom 20) 0))) := rfl
  have rl : target.subterm (rightHead++[.fn])=some (.lam (.atom 17) (.app (.atom 18) (.var (.atom 19) 0) (.var (.atom 20) 0))) := rfl
  obtain ⟨oldLeft,_ln,_atL,lt⟩ := event.final_history.node_preimage_from_lookup ll
  obtain ⟨oldRight,_rn,_atR,rt⟩ := event.final_history.node_preimage_from_lookup rl
  have chains := actual_redex_lambda_origin_chain_comparison initial prefixHistory event.final_old
    event.final_history selected sourceSafe sourceClosed (lp:=leftHead) (rp:=rightHead)
    (by rfl) (by rfl) rfl lt rt
  exact ⟨oldLeft,oldRight,lt,rt,by decide,chains⟩
end CP53

namespace Nested
open UniformOldNodeLabelSuffixChecks
open DirectedMarkerSpineIncidenceChecks.Nested

theorem forward_multiple_frame_lambda_origin :
    ∃leaf snapshot,
    ∃g : SpineIncidenceProvenance family sourceWrapped (.atom 10) true forwardSpine
      (by rfl : targetForward.subterm [.fn]=some target) leaf snapshot,
      2≤g.creationFrames.length ∧leaf.after≠[] ∧
      ∃oldPosition,BetaNodeHistoryPreimage labelsForward [.fn] oldPosition ∧
      ∃es fs,PrerequisiteChain sourceWrapped oldPosition es ∧PrerequisiteChain sourceWrapped oldPosition fs ∧
        es.map sourceWrapped.labelAt=fs.map sourceWrapped.labelAt ∧
        ChainIncidenceIsomorphic (chainSyntaxIncidence sourceWrapped sourceClosed es)
          (chainSyntaxIncidence sourceWrapped sourceClosed fs) := by
  obtain ⟨leaf,snapshot,g,multiple,after,_⟩ := PairedMarkerSpineReannotationChecks.Nested.forward_multiple_frames
  obtain ⟨a,l,b,arg,redex⟩ : ∃a l b arg,targetForward.subterm []=some (.app a (.lam l b) arg) := ⟨_,_,_,_,rfl⟩
  have lookup : targetForward.subterm [.fn]=some (.lam l b) := by
    change targetForward.subterm (([] : Path)++[.fn])=_
    rw [LTerm.subterm_append,redex]
    rfl
  obtain ⟨oldPosition,_node,_atNode,trace⟩ := labelsForward.node_preimage_from_lookup lookup
  have result := actual_redex_lambda_origin_chain_comparison initial globalPrefix oldForward labelsForward
    selected sourceSafe sourceClosed (lp:=[]) (rp:=[]) redex redex rfl trace trace
  exact ⟨leaf,snapshot,g,multiple,after,oldPosition,trace,result⟩

theorem reverse_multiple_frame_lambda_origin :
    ∃leaf snapshot,
    ∃g : SpineIncidenceProvenance family sourceWrapped (.atom 10) false reverseSpine
      (by rfl : targetReverse.subterm [.fn]=some reverseResult) leaf snapshot,
      2≤g.creationFrames.length ∧leaf.after≠[] ∧
      ∃oldPosition,BetaNodeHistoryPreimage labelsReverse [.fn] oldPosition ∧
      ∃es fs,PrerequisiteChain sourceWrapped oldPosition es ∧PrerequisiteChain sourceWrapped oldPosition fs ∧
        es.map sourceWrapped.labelAt=fs.map sourceWrapped.labelAt ∧
        ChainIncidenceIsomorphic (chainSyntaxIncidence sourceWrapped sourceClosed es)
          (chainSyntaxIncidence sourceWrapped sourceClosed fs) := by
  obtain ⟨leaf,snapshot,g,multiple,after,_⟩ := PairedMarkerSpineReannotationChecks.Nested.reverse_multiple_frames
  obtain ⟨a,l,b,arg,redex⟩ : ∃a l b arg,targetReverse.subterm []=some (.app a (.lam l b) arg) := ⟨_,_,_,_,rfl⟩
  have lookup : targetReverse.subterm [.fn]=some (.lam l b) := by
    change targetReverse.subterm (([] : Path)++[.fn])=_
    rw [LTerm.subterm_append,redex]
    rfl
  obtain ⟨oldPosition,_node,_atNode,trace⟩ := labelsReverse.node_preimage_from_lookup lookup
  have result := actual_redex_lambda_origin_chain_comparison initial globalPrefix oldReverse labelsReverse
    selected sourceSafe sourceClosed (lp:=[]) (rp:=[]) redex redex rfl trace trace
  exact ⟨leaf,snapshot,g,multiple,after,oldPosition,trace,result⟩
end Nested

#print axioms actual_terminal_cut_singletons
#print axioms actual_terminal_cut_physical_below
#print axioms actual_parent_opposite_cut_singleton
#print axioms actual_redex_lambda_origin_chain_comparison
#print axioms Larger.actual_larger_terminal_context
#print axioms Larger.actual_singleton_supply
#print axioms Larger.actual_strict_current_physical
#print axioms Larger.actual_given_parent_evaluated_heads
#print axioms RootOverlap.actual_opposite_collapses
#print axioms RootOverlap.actual_own_lambda_source_chains
#print axioms RootOverlap.retained_original_start_negative
#print axioms CP53.actual_distinct_lambda_origins
#print axioms Nested.forward_multiple_frame_lambda_origin
#print axioms Nested.reverse_multiple_frame_lambda_origin
end Lamping.Checks.TerminalHeadSuppliersChecks
