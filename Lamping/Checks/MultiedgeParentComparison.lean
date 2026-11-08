import Lamping.Lamping.MultiedgeParentComparison
import Lamping.Checks.BoundedAfterPhysicalComparison
import Lamping.Checks.TerminalHeadSuppliers

namespace Lamping.Checks.MultiedgeParentComparisonChecks
open AG Graph Lambda Lambda.Labelled
open FanSuccessfulChains
noncomputable abbrev site := FanSuccessfulReachable.concrete.site

private theorem source_joint
    (sourceSelection : OccurrenceFragmentSelection original site.net (.inl ())) :
    JointRepresentation sourceClosed sourceSelection := by
  obtain ⟨initialSelection,initialJoint⟩:=encode_initial_joint_realization original sourceClosed initial 0
  exact (FanSuccessfulReachable.concrete.sourceIso.joint_representation
    (encode_closed_matches FanSuccessfulReachable.term FanSuccessfulReachable.closed 0)
    sourceClosed initialSelection sourceSelection).mpr initialJoint

/-- Actual physical source and marked four-READ parent, different starts but
SAME edge list. The universal strict CURRENT IH is honestly conditional. -/
theorem actual_four_read_forward
    (sourceSelection : OccurrenceFragmentSelection original site.net (.inl ()))
    (targetSelection : OccurrenceFragmentSelection current site.reduce (.inl ()))
    (ih : ChainForwardBelow targetClosed targetSelection 4) :
    SameChainRepresentation targetSelection right_lambda_chain right_variable_chain := by
  have matching:=FanSuccessfulReachable.concrete.sourceIso.matches
    (encode_closed_matches FanSuccessfulReachable.term FanSuccessfulReachable.closed 0)
  have inputs:=FanSuccessfulReachable.concrete.sourceIso.rootInputs
    (encode_closed_independence FanSuccessfulReachable.term FanSuccessfulReachable.closed 0).rootInputs
  obtain ⟨originalFlow⟩:=encode_flowBalance FanSuccessfulReachable.term 0
  have flow:=FanSuccessfulReachable.concrete.sourceIso.flowBalance originalFlow
  obtain ⟨originalBalance⟩:=encode_indexed_balance FanSuccessfulReachable.term 0
  have balance:=FanSuccessfulReachable.concrete.sourceIso.indexed_balance originalBalance
  have transparency:=FanSuccessfulReachable.concrete.sourceIso.transparency
    (encode_closed_transparency FanSuccessfulReachable.term FanSuccessfulReachable.closed 0)
  exact site.beta_multiedge_chain_forward sourceClosed matching inputs flow rfl balance rfl transparency
    FanSuccessfulReachable.relative (by simp [FanSuccessfulReachable.endpoint,Marked.Normal]) actualHistory
    initial (.nil original) BoundedAfterPhysicalComparisonChecks.Physical.old
    BoundedAfterPhysicalComparisonChecks.Physical.selected (initial.outerBarsSafe _) sourceSelection
    (source_joint sourceSelection) targetSelection right_lambda_chain right_variable_chain (.refl _) (by decide) ih

/-- The actual five-READ parent has a nonempty old BEFORE before its marked
lambda. This selfpair directly exercises the NEW whole-parent high. -/
theorem actual_five_read_forward
    (sourceSelection : OccurrenceFragmentSelection original site.net (.inl ()))
    (targetSelection : OccurrenceFragmentSelection current site.reduce (.inl ()))
    (ih : ChainForwardBelow targetClosed targetSelection 5) :
    SameChainRepresentation targetSelection right_body_chain right_body_chain := by
  have matching:=FanSuccessfulReachable.concrete.sourceIso.matches
    (encode_closed_matches FanSuccessfulReachable.term FanSuccessfulReachable.closed 0)
  have inputs:=FanSuccessfulReachable.concrete.sourceIso.rootInputs
    (encode_closed_independence FanSuccessfulReachable.term FanSuccessfulReachable.closed 0).rootInputs
  obtain ⟨originalFlow⟩:=encode_flowBalance FanSuccessfulReachable.term 0
  have flow:=FanSuccessfulReachable.concrete.sourceIso.flowBalance originalFlow
  obtain ⟨originalBalance⟩:=encode_indexed_balance FanSuccessfulReachable.term 0
  have balance:=FanSuccessfulReachable.concrete.sourceIso.indexed_balance originalBalance
  have transparency:=FanSuccessfulReachable.concrete.sourceIso.transparency
    (encode_closed_transparency FanSuccessfulReachable.term FanSuccessfulReachable.closed 0)
  exact site.beta_multiedge_chain_forward sourceClosed matching inputs flow rfl balance rfl transparency
    FanSuccessfulReachable.relative (by simp [FanSuccessfulReachable.endpoint,Marked.Normal]) actualHistory
    initial (.nil original) BoundedAfterPhysicalComparisonChecks.Physical.old
    BoundedAfterPhysicalComparisonChecks.Physical.selected (initial.outerBarsSafe _) sourceSelection
    (source_joint sourceSelection) targetSelection right_body_chain right_body_chain (.refl _) (by decide) ih

private def bodyPrefix : PrerequisitePrefix current rightBody [rightVar] right :=
  .app rfl (by intro l b impossible;cases impossible)
    (.var (parent:=right) (rest:=[.fn]) rfl rfl rfl rfl .refl)
private theorem bodyLookup : current.subterm right=some (.lam rightLabel callerBody) := rfl
private theorem bodyMarked : ¬rightLabel.OuterBarsSafe (fun d=>d≠Label.atom 2) := by
  intro safe
  change (Label.atom 2≠Label.atom 2) ∧True at safe
  exact safe.1 rfl
private theorem bodySafe (p : Path) (member : p∈[rightVar]) :
    degreeReadSafe (.atom 2) (current.labelAt p) := by
  have same:=List.mem_singleton.mp member
  subst p
  intro label eq
  have actual : label=Label.atom 11:=Option.some.inj eq.symm
  subst label
  trivial
private def bodyReading : PrerequisiteReadsDirected current right right false :=
  ⟨Or.inr ⟨rightLabel,callerBody,bodyLookup,rfl⟩,rfl⟩
private def bodySpine : DirectedMarkerSpine [[.fn]] original (.atom 2) false [[.fn]] current
    ([rightVar].map current.labelAt) right :=
  BoundedAfterPhysicalComparisonChecks.Physical.old.directed_marker_spine actualHistory
    BoundedAfterPhysicalComparisonChecks.Physical.selected (initial.outerBarsSafe _) bodyPrefix bodyReading
    bodyLookup bodyMarked (by
      intro p member node lookup
      exact bodySafe p member node.label (by simp only [LTerm.labelAt,lookup,Option.map_some]))
private def bodyCut : ActualUnsafeMarkerCut [[.fn]] [[.fn]] original current (.atom 2) rightBody rightBodyEdges where
  before:=[rightVar]
  edge:=right
  after:=[[.fn,.body,.fn],xVar,[.fn]]
  reader:=right
  node:=.lam rightLabel callerBody
  forward:=false
  split:=rfl
  segment:=bodyPrefix
  remaining:=right_lambda_chain
  reading:=bodyReading
  lookup:=bodyLookup
  safeBefore:=bodySafe
  marked:=bodyMarked
  spine:=bodySpine
  leaf:=bodySpine.leaf_output bodyLookup

theorem actual_before_and_after_profile :
    bodyCut.before.length=1 ∧bodyCut.after.length=3 ∧bodyCut.forward=false ∧rightBodyEdges.length=5 ∧
      right≠rightVar := by decide

namespace LargerTerminal
abbrev sourceTerm := NormalFalseCanonicalOriginalComparisonChecks.Terminal.original
abbrev targetTerm := NormalFalseCanonicalOriginalComparisonChecks.Terminal.current

/-- Honest conditional physical specialization of the real len2/zero-jump
syntax. No new actual corridor presentation or universal IH truth is asserted. -/
theorem conditional_actual_terminal_forward
    {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
    {kept : K→Graph.Label signature} {i : Nat}
    (betaSite : PathSite (.beta i) kept (B:=B) (W:=W) (V:=V)) {root : B}
    (matching : Matches betaSite.net root sourceTerm.erase)
    (inputs : RootInputs betaSite.net root)
    {boundary : B→Bool} (flow : FlowBalance betaSite.net boundary) (positive : boundary root=true)
    {heights : B→Int} (balance : IndexedLevelBalance betaSite.net heights) (rootDepth : heights root=0)
    (transparency : Transparency betaSite.net root) {marked : Marked}
    (relative : Marked.RelativeHistory [[]]
      (Marked.mark (betaSite.betaSyntaxFiber root sourceTerm.erase) sourceTerm.erase) marked)
    (normal : Marked.Normal marked)
    (sourceSelection : OccurrenceFragmentSelection sourceTerm betaSite.net root)
    (sourceJoint : JointRepresentation TerminalHeadSuppliersChecks.Larger.sourceClosed sourceSelection)
    (targetSelection : OccurrenceFragmentSelection targetTerm betaSite.reduce root)
    (ih : ChainForwardBelow TerminalHeadSuppliersChecks.Larger.targetClosed targetSelection 2) :
    SameChainRepresentation targetSelection TerminalHeadSuppliersChecks.Larger.leftChain
      TerminalHeadSuppliersChecks.Larger.rightChain := by
  exact betaSite.beta_multiedge_chain_forward TerminalHeadSuppliersChecks.Larger.sourceClosed matching
    inputs flow positive balance rootDepth transparency relative normal
    NormalFalseCanonicalOriginalComparisonChecks.Terminal.actualHistory TerminalHeadSuppliersChecks.Larger.initial
    (.nil sourceTerm) TerminalHeadSuppliersChecks.Larger.old TerminalHeadSuppliersChecks.Larger.selected
    (TerminalHeadSuppliersChecks.Larger.initial.outerBarsSafe _) sourceSelection sourceJoint targetSelection
    TerminalHeadSuppliersChecks.Larger.leftChain TerminalHeadSuppliersChecks.Larger.rightChain (.refl _) (by decide) ih
end LargerTerminal

theorem actual_whole_singleton_boundary :
    PrerequisiteChain current [] [[.fn]] ∧PrerequisiteChain current [.fn] [[.fn]] ∧
      ¬1<max ([[.fn]] : List Path).length ([[.fn]] : List Path).length :=
  ⟨root_chain,outer_stop,by decide⟩

#print axioms actual_four_read_forward
#print axioms actual_five_read_forward
#print axioms actual_before_and_after_profile
#print axioms LargerTerminal.conditional_actual_terminal_forward
#print axioms actual_whole_singleton_boundary
end Lamping.Checks.MultiedgeParentComparisonChecks
