import Lamping.Lamping.FanCopiedLambdaBodyContextCuts
import Lamping.Checks.FanLambdaChainPassages
namespace Lamping.Checks.FanBodyPhysicalConsumer
open AG Graph Lambda Lambda.Labelled FanSuccessfulReachable
open FanSuccessfulChains hiding current original
open FanLambdaChainPassageConsumer
abbrev bodyStamp (branch : Bool) : Label := if branch then rightLabel else leftLabel
abbrev bodyEdge (branch : Bool) := sourceEdge [bodyStamp branch,functionLabel] (.lamBody (bodyStamp branch)) callerBody
abbrev bodyPosition (branch : Bool) : Path := if branch then rightBody else leftBody

def bodyOccurrence (branch : Bool) : SourceSubterm [] .external current (bodyPosition branch)
    [bodyStamp branch,functionLabel] (.lamBody (bodyStamp branch)) callerBody := by
  cases branch
  · exact left_body_occurrence
  · exact right_body_occurrence

def bodyRole (branch : Bool) : SourceDeparture (.lam (bodyStamp branch) callerBody) .body (bodyEdge branch).fromPort := .body

theorem bodyWord (branch : Bool) : bodyPosition branch=
    accessWord targetNet (SuccessfulAuxiliaryPhysicalPair.chosenParent branch).val++[.body] := by
  rw [SuccessfulAuxiliaryPhysicalPair.chosenWord]
  cases branch <;> rfl

local notation "site" => actualFanPresentation.site
noncomputable abbrev actualBodyCut : Net signature actualFanPresentation.Kept
    (Boundary term⊕(Bool⊕Bool)) actualFanPresentation.Outside := cutFragment actualFanPresentation.site.net
  (pathPartition (Schema.fanAction Op.lam 0 1 (by decide)) actualFanPresentation.Inside) actualFanPresentation.site.closed
local notation "cut" => actualBodyCut
abbrev actualBodyRight := fanRight Op.lam 0 1
local notation "rhs" => actualBodyRight

/-- Actual body APP fragments after the first fan-lambda step have the real
BODY/writer/outside prefix. This does not instantiate a lambda-ending cut. -/
theorem actual_body_prefix (branch : Bool)
    (target : SourceEdgeFragment current targetNet (.inl ()) (bodyEdge branch) (bodyPosition branch))
    {a b : Context} (labels : Labelling targetNet target.segments a b) :
    ∃tail middle,target.segments.map (plugEnd (cut).label (rhs).label).invFun=
      .inr (.inl ⟨.inl branch,.inr true⟩):: .inr (.inl ⟨.inr true,.inl ()⟩)::
        .inl (.inr (.inl (.inr (.inr true))))::tail ∧
      Traversal 0 (.op .fan) (.inr branch) (.inl ()) a middle ∧
      PlugLabelling cut rhs (.inl (.inr (.inl (.inr (.inr true))))::tail) middle b := by
  exact fan_copied_lambda_body_fragment cut 0 1 branch actual_target_matches target (bodyRole branch)
    (SuccessfulAuxiliaryPhysicalPair.chosenParent branch) (bodyWord branch)
    (SuccessfulAuxiliaryPhysicalPair.chosenFinish branch) labels

/-- The parent normalization consumes the actual parent assignment extracted
from THIS body whole, on ONE principal and THIS source parent access. -/
theorem actual_body_parent_canonical (principal : SiteActionPrincipal site)
    (source : OccurrenceFragmentSelection current sourceNet (.inl ())) (branch : Bool)
    (target : SourceEdgeFragment current targetNet (.inl ()) (bodyEdge branch) (bodyPosition branch))
    {a b : Context} (labels : Labelling targetNet target.access.val a b) :
    ∃middle, Labelling targetNet (SuccessfulAuxiliaryPhysicalPair.chosenParent branch).val a middle ∧
      ActionCanonicalBlocks site principal
        ((SuccessfulAuxiliaryPhysicalPair.chosenParent branch).val.map (plugEnd (cut).label (rhs).label).invFun++
          [.inr (.inl ⟨.inl branch,.inr true⟩),.inr (.inl ⟨.inr true,.inl ()⟩),
            .inl (.inr (.inl (.inr (.inr true))))])
        ((source (selectedPosition branch)).fragment.access.val++[.inl ⟨.inr (.inr ()),.inr true⟩]) ∧
      PlugExcursions cut rhs
        ((SuccessfulAuxiliaryPhysicalPair.chosenParent branch).val.map (plugEnd (cut).label (rhs).label).invFun++
          [.inr (.inl ⟨.inl branch,.inr true⟩),.inr (.inl ⟨.inr true,.inl ()⟩),
            .inl (.inr (.inl (.inr (.inr true))))]) a (InitialOffsets.fanAt 0 branch middle) := by
  have childCut := target.child_prefix actual_target_matches (bodyRole branch)
    (SuccessfulAuxiliaryPhysicalPair.chosenParent branch) (bodyWord branch)
  obtain ⟨middle,parentOrEmpty,_pieceLabels⟩ := target.assignments a b labels
  rw [childCut.1] at parentOrEmpty
  have parentLabels : Labelling targetNet (SuccessfulAuxiliaryPhysicalPair.chosenParent branch).val a middle := by
    rcases parentOrEmpty with ⟨empty,_⟩|actual
    · have head := (SuccessfulAuxiliaryPhysicalPair.chosenParent branch).property.2.1
      rw [empty] at head;cases head
    · exact actual
  obtain ⟨flow,_,_,_,_⟩ := beta_certified
  have word : accessWord sourceNet (source (selectedPosition branch)).fragment.access.val=
      accessWord targetNet (SuccessfulAuxiliaryPhysicalPair.chosenParent branch).val := by
    rw [(source (selectedPosition branch)).fragment.word,SuccessfulAuxiliaryPhysicalPair.chosenWord]
    rfl
  obtain ⟨canonical,whole⟩ := PathSite.fan_lambda_body_parent_canonical actualFanPresentation.site
    (actualFanPresentation.sourceIso.flowBalance flow) (.inl ()) rfl actual_source_matches principal
    (source (selectedPosition branch)).fragment.access (SuccessfulAuxiliaryPhysicalPair.chosenParent branch)
    word branch (SuccessfulAuxiliaryPhysicalPair.chosenFinish branch) parentLabels
  exact ⟨middle,parentLabels,canonical,whole⟩

/-- Same original INIT/history and real two-rule trace supply both branch
body fragments and arbitrary actual assignments; BODY incoming is not asserted
to be a chain member. The successful chain starts at the APP node. -/
theorem actual_reachable_body_supply :
    INIT original ∧Closed original.erase ∧History [[.fn]] original current ∧
    GraphTrace (ActualNet.initial term) (ActualNet.ofNet targetNet)
      [.beta 0,.fanAction .lam 0 1 (by decide)] ∧
    Matches sourceNet (.inl ()) current.erase ∧Matches targetNet (.inl ()) current.erase ∧
    Nonempty (OccurrenceFragmentSelection current sourceNet (.inl ())) ∧
    (∀branch,Nonempty (SourceEdgeFragment current sourceNet (.inl ()) (bodyEdge branch) (bodyPosition branch)) ∧
      Nonempty (SourceEdgeFragment current targetNet (.inl ()) (bodyEdge branch) (bodyPosition branch)) ∧
      PrerequisiteChain current (starting branch) (fullEdges branch)) := by
  refine ⟨FanSuccessfulChains.initial,sourceClosed,actualHistory,actual_two_step_trace,
    actual_source_matches,actual_target_matches,actual_source_matches.occurrence_fragment_selection targetClosed,?_⟩
  intro branch
  exact ⟨actual_source_matches.base_source_edge_fragment targetClosed (bodyOccurrence branch),
    actual_target_matches.base_source_edge_fragment targetClosed (bodyOccurrence branch),actualChain branch⟩
end Lamping.Checks.FanBodyPhysicalConsumer
#print axioms Lamping.AG.fan_typed_body_prefix
#print axioms Lamping.AG.fan_copied_lambda_body_fragment
#print axioms Lamping.AG.PendingRhsBlock.fan_lambda_body_path
#print axioms Lamping.AG.PendingRhsBlock.fan_lambda_body_completion
#print axioms Lamping.AG.PathSite.fan_lambda_body_parent_canonical
#print axioms Lamping.AG.SourceEdgeFragment.fan_copied_body_context_cut
#print axioms Lamping.Checks.FanBodyPhysicalConsumer.actual_body_prefix
#print axioms Lamping.Checks.FanBodyPhysicalConsumer.actual_body_parent_canonical
#print axioms Lamping.Checks.FanBodyPhysicalConsumer.actual_reachable_body_supply
