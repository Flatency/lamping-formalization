import Lamping.Lamping.BoundedAfterPhysicalComparison
import Lamping.Checks.FanSuccessfulReachable
import Lamping.Checks.ActualSpineAfterAlignment

namespace Lamping.Checks.BoundedAfterPhysicalComparisonChecks
open AG Graph Lambda Lambda.Labelled

private theorem cut_at_unsafe_head
    {source target : LTerm} {head : Path} {tail : List Path}
    (cut : ActualUnsafeMarkerCut F ps source target degree start (head::tail))
    (notSafe : ¬degreeReadSafe degree (target.labelAt head)) :
    cut.before=[] ∧cut.edge=head ∧cut.after=tail := by
  cases beforeEq : cut.before with
  | nil =>
    have split := cut.split
    rw [beforeEq,List.nil_append] at split
    have parts := List.cons.inj split
    exact ⟨rfl,parts.1.symm,parts.2.symm⟩
  | cons first rest =>
    have split := cut.split
    rw [beforeEq,List.cons_append] at split
    have firstEq := (List.cons.inj split).1
    have inside : head∈cut.before := by rw [beforeEq,firstEq];exact List.mem_cons_self
    exact False.elim (notSafe (cut.safeBefore head inside))

private theorem below_one
    {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
    {g : Net signature N B W} {root : B} {target : LTerm}
    (closed : Closed target.erase) (selection : OccurrenceFragmentSelection target g root) :
    ChainForwardBelow closed selection 1 := by
  intro p q es fs first second smaller iso
  have empty : es=[] := List.length_eq_zero_iff.mp (by omega)
  exact False.elim (first.nonempty empty)

namespace Physical
open FanSuccessfulChains
noncomputable abbrev site := FanSuccessfulReachable.concrete.site

def old : Marked.RelativeOldHistory [[.fn]] [[.fn]] (Marked.mark [[.fn]] original.erase)
    FanSuccessfulReachable.endpoint :=
  .cons (.appL (.redRoot _ _ _)) (by decide) (.nil _)

theorem selected (p : Path) (inside : p∈([[.fn]] : List Path)) : original.degreeAt p=some (.atom 2) := by
  have same := List.mem_singleton.mp inside
  subst p
  rfl

theorem rightUnsafe : ¬degreeReadSafe (.atom 2) (current.labelAt right) := by
  intro safe
  have bars := safe rightLabel rfl
  change ((Label.atom 2)≠Label.atom 2) ∧True at bars
  exact bars.1 rfl

theorem rootUnsafe : ¬degreeReadSafe (.atom 2) (current.labelAt [.fn]) := by
  intro safe
  have bars := safe functionLabel rfl
  change ((Label.atom 2)≠Label.atom 2) ∧True at bars
  exact bars.1 rfl

/-- A real physical beta site with a marked, nonempty CURRENT AFTER. The
universal bounded IH remains explicit; source Joint does not supply it.
The NEW high theorem internally cuts the parent and consumes that exact IH. -/
theorem actual_nonempty_after_evaluators
    (targetSelection : OccurrenceFragmentSelection current site.reduce (.inl ()))
    (ih : ChainForwardBelow targetClosed targetSelection 4) :
    ∃localTarget,History [[.fn]] (initLabels original.erase) localTarget ∧
      ∃edge : BetaEdge site.net,∃selection : SourceEdgeSelection (initLabels original.erase) site.net (.inl ()),
        SiteBetaGeometry site edge ∧
        ∃left : ActualUnsafeMarkerCut [[.fn]] [[.fn]] original current (.atom 2) right rightEdges,
          ∃rightCut : ActualUnsafeMarkerCut [[.fn]] [[.fn]] original current (.atom 2) right rightEdges,
            ∃out : BoundedAfterPhysicalOutput site (localTarget:=localTarget) left rightCut edge selection targetSelection,
              left.after=[[.fn,.body,.fn],xVar,[.fn]] ∧rightCut.after=[[.fn,.body,.fn],xVar,[.fn]] ∧
              (out.leftEvaluation.blocks site).length=3 := by
  have matching := FanSuccessfulReachable.concrete.sourceIso.matches
    (encode_closed_matches FanSuccessfulReachable.term FanSuccessfulReachable.closed 0)
  have inputs := FanSuccessfulReachable.concrete.sourceIso.rootInputs
    (encode_closed_independence FanSuccessfulReachable.term FanSuccessfulReachable.closed 0).rootInputs
  obtain ⟨originalFlow⟩ := encode_flowBalance FanSuccessfulReachable.term 0
  have flow := FanSuccessfulReachable.concrete.sourceIso.flowBalance originalFlow
  obtain ⟨originalBalance⟩ := encode_indexed_balance FanSuccessfulReachable.term 0
  have balance := FanSuccessfulReachable.concrete.sourceIso.indexed_balance originalBalance
  have transparency := FanSuccessfulReachable.concrete.sourceIso.transparency
    (encode_closed_transparency FanSuccessfulReachable.term FanSuccessfulReachable.closed 0)
  obtain ⟨localTarget,labels,edge,selection,geometry,result⟩ :=
    site.beta_bounded_actual_after_comparison sourceClosed matching inputs flow rfl balance rfl transparency
      FanSuccessfulReachable.relative (by simp [FanSuccessfulReachable.endpoint,Marked.Normal]) actualHistory
      initial (.nil original) old selected (initial.outerBarsSafe _) targetSelection right_lambda_chain right_lambda_chain
      (.refl _) ih
  rcases result with safe|terminal|nonempty
  · exact False.elim (rightUnsafe (safe.1 right List.mem_cons_self))
  · obtain ⟨left,rightCut,leftEmpty,_rightEmpty⟩ := terminal
    obtain ⟨_before,_head,after⟩ := cut_at_unsafe_head left rightUnsafe
    rw [after] at leftEmpty
    cases leftEmpty
  · obtain ⟨left,rightCut,⟨out⟩⟩ := nonempty
    obtain ⟨_before,_head,after⟩ := cut_at_unsafe_head left rightUnsafe
    obtain ⟨_otherBefore,_otherHead,otherAfter⟩ := cut_at_unsafe_head rightCut rightUnsafe
    refine ⟨localTarget,labels,edge,selection,geometry,left,rightCut,out,after,otherAfter,?_⟩
    simp only [EvaluatedChainResiduals.blocks,List.length_map,List.length_attach,after]
    rfl

/-- The SAME real site has a singleton terminal pair with different starts.
Its strict bound1 IH is genuinely vacuous, hence supplied unconditionally.
No direction equality is imposed on this terminal branch. -/
theorem actual_terminal_after
    (targetSelection : OccurrenceFragmentSelection current site.reduce (.inl ())) :
    ∃localTarget,History [[.fn]] (initLabels original.erase) localTarget ∧
      ∃edge : BetaEdge site.net,∃_selection : SourceEdgeSelection (initLabels original.erase) site.net (.inl ()),
        SiteBetaGeometry site edge ∧
        ∃left : ActualUnsafeMarkerCut [[.fn]] [[.fn]] original current (.atom 2) [] [[.fn]],
          ∃rightCut : ActualUnsafeMarkerCut [[.fn]] [[.fn]] original current (.atom 2) [.fn] [[.fn]],
            left.after=[] ∧rightCut.after=[] := by
  have matching := FanSuccessfulReachable.concrete.sourceIso.matches
    (encode_closed_matches FanSuccessfulReachable.term FanSuccessfulReachable.closed 0)
  have inputs := FanSuccessfulReachable.concrete.sourceIso.rootInputs
    (encode_closed_independence FanSuccessfulReachable.term FanSuccessfulReachable.closed 0).rootInputs
  obtain ⟨originalFlow⟩ := encode_flowBalance FanSuccessfulReachable.term 0
  have flow := FanSuccessfulReachable.concrete.sourceIso.flowBalance originalFlow
  obtain ⟨originalBalance⟩ := encode_indexed_balance FanSuccessfulReachable.term 0
  have balance := FanSuccessfulReachable.concrete.sourceIso.indexed_balance originalBalance
  have transparency := FanSuccessfulReachable.concrete.sourceIso.transparency
    (encode_closed_transparency FanSuccessfulReachable.term FanSuccessfulReachable.closed 0)
  obtain ⟨localTarget,labels,edge,selection,geometry,result⟩ :=
    site.beta_bounded_actual_after_comparison sourceClosed matching inputs flow rfl balance rfl transparency
      FanSuccessfulReachable.relative (by simp [FanSuccessfulReachable.endpoint,Marked.Normal]) actualHistory
      initial (.nil original) old selected (initial.outerBarsSafe _) targetSelection root_chain outer_stop
      (.refl _) (below_one targetClosed targetSelection)
  rcases result with safe|terminal|nonempty
  · exact False.elim (rootUnsafe (safe.1 [.fn] List.mem_cons_self))
  · exact ⟨localTarget,labels,edge,selection,geometry,terminal⟩
  · obtain ⟨left,rightCut,⟨out⟩⟩ := nonempty
    have empty := (cut_at_unsafe_head left rootUnsafe).2.2
    exact False.elim (out.leftMore empty)
end Physical

namespace Noninitial
open UniformOldCreatedIncomingLabelsChecks.Distinct
variable {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K→Graph.Label signature} {i : Nat}
variable (site : PathSite (.beta i) kept (B:=B) (W:=W) (V:=V))

/-- Real two-OLD/q0 syntax consumes the NEW high entry. Physical-site/full
development inputs and UNIVERSAL bounded IH remain honest hypotheses;
no such nonINIT physical realization or Joint truth is asserted here. -/
theorem actual_q0_two_old_conditional
    {root : B} {endpoint : Marked}
    (matching : Matches site.net root source.erase) (inputs : RootInputs site.net root)
    {boundary : B→Bool} (flow : FlowBalance site.net boundary) (positive : boundary root=true)
    {heights : B→Int} (balance : IndexedLevelBalance site.net heights) (rootDepth : heights root=0)
    (transparency : Transparency site.net root)
    (relative : Marked.RelativeHistory [left,right] (Marked.mark (site.betaSyntaxFiber root source.erase) source.erase) endpoint)
    (normal : Marked.Normal endpoint)
    (selection : OccurrenceFragmentSelection target site.reduce root)
    (ih : ChainForwardBelow (labels.closed ActualSpineAfterAlignmentChecks.EmptyCopy.sourceClosed) selection 3) :
    ∃localTarget,History [left,right] (initLabels source.erase) localTarget ∧
      ∃edge : BetaEdge site.net,∃localSelection : SourceEdgeSelection (initLabels source.erase) site.net root,
        SiteBetaGeometry site edge ∧
        ∃lc : ActualUnsafeMarkerCut F [left,right] source target (.atom 7) right [right,[.arg],[.fn]],
          ∃rc : ActualUnsafeMarkerCut F [left,right] source target (.atom 7) right [right,[.arg],[.fn]],
            ∃out : BoundedAfterPhysicalOutput site (localTarget:=localTarget) lc rc edge localSelection selection,
              lc.after=[[.arg],[.fn]] ∧rc.after=[[.arg],[.fn]] ∧(out.leftEvaluation.blocks site).length=2 := by
  have notSafe : ¬degreeReadSafe (.atom 7) (target.labelAt right) := by
    intro safe
    exact marked (safe leftNode.label rfl)
  obtain ⟨localTarget,localHistory,edge,localSelection,geometry,result⟩ :=
    site.beta_bounded_actual_after_comparison ActualSpineAfterAlignmentChecks.EmptyCopy.sourceClosed matching inputs
      flow positive balance rootDepth transparency relative normal labels initial globalHistory old selected source_safe
      selection ActualSpineAfterAlignmentChecks.EmptyCopy.remaining ActualSpineAfterAlignmentChecks.EmptyCopy.remaining
      (.refl _) ih
  rcases result with safe|terminal|nonempty
  · exact False.elim (notSafe (safe.1 right List.mem_cons_self))
  · obtain ⟨lc,_rc,empty,_⟩ := terminal
    rw [(cut_at_unsafe_head lc notSafe).2.2] at empty
    cases empty
  · obtain ⟨lc,rc,⟨out⟩⟩ := nonempty
    have le := (cut_at_unsafe_head lc notSafe).2.2
    have re := (cut_at_unsafe_head rc notSafe).2.2
    exact ⟨localTarget,localHistory,edge,localSelection,geometry,lc,rc,out,le,re,
      by simp only [EvaluatedChainResiduals.blocks,List.length_map,List.length_attach,le];rfl⟩
end Noninitial

namespace Safe
open OldChainBetaFixture
noncomputable def presentation := Classical.choice actual_presentation
noncomputable abbrev site := presentation.site
def chain : PrerequisiteChain result [] [[.fn]] := .redex_app rfl
theorem closedTarget : Closed result.erase := history.closed closed
def old : Marked.RelativeOldHistory [[]] [[]] (Marked.mark [[]] initial.erase) endpoint :=
  .cons (.redRoot _ _ _) (by decide) (.nil _)
theorem selected (p : Path) (inside : p∈([[]] : List Path)) : initial.degreeAt p=some (.atom 1) := by
  have same := List.mem_singleton.mp inside
  subst p
  rfl
theorem safe : ∀e∈([[.fn]] : List Path),degreeReadSafe (.atom 1) (result.labelAt e) := by
  intro e member label atLabel
  have equal := List.mem_singleton.mp member
  subst e
  have labelEq : label=Label.atom 4 := Option.some.inj atLabel.symm
  subst label
  trivial
private theorem no_cut
    (cut : ActualUnsafeMarkerCut [[]] [[]] initial result (.atom 1) [] [[.fn]]) : False := by
  have inside : cut.edge∈([[.fn]] : List Path) :=
    Eq.mp (congrArg (fun es : List Path => cut.edge∈es) cut.split.symm)
      (List.mem_append_right _ List.mem_cons_self)
  exact cut.marked (safe cut.edge inside cut.node.label (by simp only [LTerm.labelAt,cut.lookup,Option.map_some]))

/-- A different real initial beta site has all-safe successful READ edges.
The bound1 IH is vacuous; the producer and high entry are genuinely called. -/
theorem actual_all_safe_producer
    (targetSelection : OccurrenceFragmentSelection result site.reduce (.inl ())) :
    ∃localTarget,History [[]] (initLabels initial.erase) localTarget ∧
      ∃edge : BetaEdge site.net,∃_selection : SourceEdgeSelection (initLabels initial.erase) site.net (.inl ()),
        SiteBetaGeometry site edge ∧∀e∈([[.fn]] : List Path),degreeReadSafe (.atom 1) (result.labelAt e) := by
  have matching := presentation.sourceIso.matches (encode_closed_matches term closed 0)
  have inputs := presentation.sourceIso.rootInputs (encode_closed_independence term closed 0).rootInputs
  obtain ⟨originalFlow⟩ := encode_flowBalance term 0
  have flow := presentation.sourceIso.flowBalance originalFlow
  obtain ⟨originalBalance⟩ := encode_indexed_balance term 0
  have balance := presentation.sourceIso.indexed_balance originalBalance
  have transparency := presentation.sourceIso.transparency (encode_closed_transparency term closed 0)
  obtain ⟨localTarget,labels,edge,selection,geometry,resultCase⟩ :=
    site.beta_bounded_actual_after_comparison (source:=initial) (target:=result) closed matching inputs flow rfl balance rfl transparency
      (relative presentation) (by simp [endpoint,Marked.Normal]) history (init_is_INIT term) (.nil initial)
      old selected ((init_is_INIT term).outerBarsSafe _) targetSelection chain chain (.refl _)
      (below_one closedTarget targetSelection)
  rcases resultCase with allSafe|terminal|nonempty
  · exact ⟨localTarget,labels,edge,selection,geometry,allSafe.1⟩
  · obtain ⟨lc,_rc,_⟩ := terminal
    exact False.elim (no_cut lc)
  · obtain ⟨lc,_rc,_⟩ := nonempty
    exact False.elim (no_cut lc)
end Safe

#print axioms Physical.actual_nonempty_after_evaluators
#print axioms Physical.actual_terminal_after
#print axioms Noninitial.actual_q0_two_old_conditional
#print axioms Safe.actual_all_safe_producer
end Lamping.Checks.BoundedAfterPhysicalComparisonChecks
