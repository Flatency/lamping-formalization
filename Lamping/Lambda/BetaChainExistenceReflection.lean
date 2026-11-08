import Lamping.Lambda.UncreatedPrefixTransport
import Lamping.Lambda.PrerequisiteUndefined
namespace Lamping.Lambda.Labelled
/-- Backwards existence is tied to the SAME actual occurrence preimage.
It neither completes a missing chain nor preserves an arbitrary edge list. -/
theorem StepAt.chain_preimage_exists
    {source target body argument : LTerm} {site start : Path} {beta alpha : Label}
    (step : StepAt site source target)
    (redex : source.subterm site=some (.app beta (.lam alpha body) argument))
    (chain : PrerequisiteChain target start edges) :
    ∃ oldStart oldEdges,BetaNodePreimage body argument site start oldStart ∧
      PrerequisiteChain source oldStart oldEdges := by
  classical
  by_cases created : ∃ edge∈edges,BetaCreatedIncoming body site edge
  · obtain ⟨before,edge,after,middle,oldMiddle,first,last,computed,split,segment,
        remaining,reads,origin,oldTwo,lastLookup,actualCreated,uncreated⟩ :=
      step.first_created_reading_origins redex chain created
    obtain ⟨oldStart,oldBefore,oldMiddle,first,last,startOrigin,_,_,_,oldChain,_,_⟩ :=
      step.created_prefix_old_chain redex segment reads actualCreated uncreated
    exact ⟨oldStart,_,startOrigin,oldChain⟩
  · obtain ⟨oldStart,oldEdges,startOrigin,oldChain,_,_,_⟩ :=
      step.uncreated_chain_reflect redex chain (by
        intro edge member actual;exact created ⟨edge,member,actual⟩)
    exact ⟨oldStart,oldEdges,startOrigin,oldChain⟩
theorem StepAt.chain_reflect_at_preimage
    {source target body argument : LTerm} {site start oldStart : Path} {beta alpha : Label}
    (step : StepAt site source target)
    (redex : source.subterm site=some (.app beta (.lam alpha body) argument))
    (origin : BetaNodePreimage body argument site start oldStart)
    (chain : PrerequisiteChain target start edges) :
    ∃ oldEdges,PrerequisiteChain source oldStart oldEdges := by
  obtain ⟨actual,oldEdges,actualOrigin,oldChain⟩ := step.chain_preimage_exists redex chain
  have equal := actualOrigin.unique origin
  exact ⟨oldEdges,equal ▸ oldChain⟩
theorem StepAt.no_prerequisite_at_preimage
    {source target body argument : LTerm} {site start oldStart : Path} {beta alpha : Label}
    (step : StepAt site source target)
    (redex : source.subterm site=some (.app beta (.lam alpha body) argument))
    (origin : BetaNodePreimage body argument site start oldStart)
    (undefined : NoPrerequisite source oldStart) : NoPrerequisite target start := by
  rintro ⟨edges,chain⟩
  exact undefined (step.chain_reflect_at_preimage redex origin chain)
end Lamping.Lambda.Labelled

namespace Lamping.Lambda.Labelled
/-- Finite operational occurrence ancestry, indexed by THIS actual labelled
history. No labels, chain existence, or undefined status is a field. -/
inductive BetaNodeHistoryPreimage : {ps : List Path} →{source target : LTerm} →
    History ps source target →Path →Path →Prop where
  | nil (t : LTerm) (p : Path) : BetaNodeHistoryPreimage (.nil t) p p
  | one {site : Path} {ps : List Path} {source middle target body argument : LTerm}
      {beta alpha : Label} {currentPosition middlePosition oldPosition : Path}
      {step : StepAt site source middle} {remaining : History ps middle target}
      (redex : source.subterm site=some (.app beta (.lam alpha body) argument))
      (origin : BetaNodePreimage body argument site middlePosition oldPosition)
      (tail : BetaNodeHistoryPreimage remaining currentPosition middlePosition) :
      BetaNodeHistoryPreimage (.cons step remaining) currentPosition oldPosition
/-- The source position and lookup are internally constructed from the actual
final lookup. The same labels/history are fixed throughout. -/
theorem History.node_preimage_from_lookup
    (labels : History ps source target) (lookup : target.subterm p=some current) :
    ∃ oldPosition old,source.subterm oldPosition=some old ∧
      BetaNodeHistoryPreimage labels p oldPosition := by
  induction labels with
  | nil => exact ⟨p,current,lookup,.nil _ _⟩
  | cons step rest ih =>
    obtain ⟨middlePosition,middle,atMiddle,tailTrace⟩ := ih lookup
    obtain ⟨beta,alpha,body,argument,redex,_⟩ := step.head_lookups
    obtain ⟨oldPosition,origin⟩ := step.beta_node_preimage redex atMiddle
    obtain ⟨old,atOld,_⟩ := step.preimage_node_constructor redex origin atMiddle
    exact ⟨oldPosition,old,atOld,.one (step:=step) redex origin tailTrace⟩
theorem BetaNodeHistoryPreimage.no_prerequisite
    {ps : List Path} {source target : LTerm} {labels : History ps source target} {p oldPosition : Path}
    (trace : BetaNodeHistoryPreimage labels p oldPosition)
    (undefined : NoPrerequisite source oldPosition) : NoPrerequisite target p := by
  induction trace with
  | nil => exact undefined
  | @one _ _ _ _ _ _ _ _ _ _ _ _ step _ redex origin tail ih =>
    exact ih (step.no_prerequisite_at_preimage redex origin undefined)
/-- THIS schedule/target fixes the old coordinate, not converse injectivity. -/
theorem BetaNodeHistoryPreimage.unique
    {ps : List Path} {source target : LTerm} {labels : History ps source target}
    {p firstPosition secondPosition : Path}
    (first : BetaNodeHistoryPreimage labels p firstPosition)
    (second : BetaNodeHistoryPreimage labels p secondPosition) : firstPosition=secondPosition := by
  induction first generalizing secondPosition with
  | nil => cases second;rfl
  | @one site ps source middle target body argument beta alpha current mid old step remaining redex origin tail ih =>
    cases second with
    | @one _ _ _ otherMiddle _ otherBody otherArgument otherBeta otherAlpha _ otherMid _ otherStep otherRemaining otherRedex otherOrigin otherTail =>
      have middleEq := step.deterministic otherStep
      subst otherMiddle
      have coordinateEq := ih otherTail
      subst otherMid
      have redexEq := Option.some.inj (redex.symm.trans otherRedex)
      cases redexEq
      exact origin.unique otherOrigin
end Lamping.Lambda.Labelled
