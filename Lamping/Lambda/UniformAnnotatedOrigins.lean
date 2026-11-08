import Lamping.Lambda.BetaPreimageErasure
import Lamping.Lambda.LabelUniformDevelopment
import Lamping.Lambda.BetaChainExistenceReflection
namespace Lamping.Lambda.Labelled
private theorem same_erasure_after {source target otherSource otherTarget : LTerm}
    (step : StepAt site source target) (other : StepAt site otherSource otherTarget)
    (same : source.erase=otherSource.erase) : target.erase=otherTarget.erase := by
  have bare : BetaAt otherSource.erase site target.erase := by rw [←same];exact step.betaAt
  obtain ⟨candidate,lifted,erased⟩ := lift_betaAt bare
  have equal := lifted.deterministic other
  rw [equal] at erased
  exact erased.symm
end Lamping.Lambda.Labelled

namespace Lamping.Lambda.Marked
open Labelled

/-- Follow one actual marker-free occurrence through the SAME global OLD
schedule and a second actual annotation history. Only the global degrees
are uniform. Intermediate labels may be unsafe and the second annotation
need not be INIT. The returned shared old coordinate carries the actual
global history-preimage trace, not merely two equal label values. -/
theorem RelativeOldHistory.marker_free_paired_origin {F ps : List Path} {m n : Marked}
    (old : RelativeOldHistory F ps m n) {d : Path →Option Label}
    {source target otherSource otherTarget current otherCurrent : LTerm} {edge : Path} {degree : Label}
    (aligned : DegreeAligned d m source) (labels : Labelled.History ps source target)
    (otherLabels : Labelled.History ps otherSource otherTarget)
    (same : source.erase=otherSource.erase)
    (selected : ∀ path∈F,d path=some degree)
    (lookup : target.subterm edge=some current)
    (otherLookup : otherTarget.subterm edge=some otherCurrent)
    (safe : current.label.OuterBarsSafe (fun payload=>payload≠degree)) :
    ∃ oldPosition oldNode otherOld,
      source.subterm oldPosition=some oldNode ∧otherSource.subterm oldPosition=some otherOld ∧
      oldNode.label=current.label ∧otherOld.label=otherCurrent.label ∧
      BetaNodeHistoryPreimage labels edge oldPosition := by
  induction old generalizing source target otherSource otherTarget edge with
  | nil => cases labels;cases otherLabels;exact ⟨edge,current,otherCurrent,lookup,otherLookup,rfl,rfl,.nil _ _⟩
  | @cons path _ _ _ _ reduction member tail ih =>
    cases labels with
    | @cons _ _ middle _ _ turn remaining =>
      cases otherLabels with
      | @cons _ _ otherMiddle _ _ otherTurn otherRemaining =>
        have middleSame := same_erasure_after turn otherTurn same
        obtain ⟨middlePosition,middleNode,otherMiddleNode,atMiddle,atOtherMiddle,middleLabel,otherMiddleLabel,tailTrace⟩ :=
          ih (aligned.step reduction turn) remaining otherRemaining middleSame lookup otherLookup
        obtain ⟨name,chosen,residual⟩ := (mem_setResidualPositions _ _ _).mp member
        have atDegree := (aligned.trace_degree residual).trans (selected name chosen)
        obtain ⟨beta,body,argument,redex⟩ := LTerm.degreeAt_redex atDegree
        have uncreated : ¬BetaCreatedIncoming body path middlePosition := by
          intro created
          apply turn.created_label_not_safe redex atMiddle created
          rw [middleLabel];exact safe
        obtain ⟨oldPosition,origin⟩ := turn.beta_node_preimage redex atMiddle
        obtain ⟨oldNode,oldLookup,oldLabel⟩ := turn.beta_preimage_label redex origin atMiddle uncreated
        obtain ⟨otherBeta,otherAlpha,otherBody,otherArgument,otherRedex,_contractum⟩ := otherTurn.head_lookups
        have heads : subtermAt source.erase path=subtermAt otherSource.erase path := congrArg (fun t=>subtermAt t path) same
        simp only [←LTerm.erase_subterm,redex,otherRedex,Option.map_some,LTerm.erase] at heads
        have components := Term.app.inj (Option.some.inj heads)
        have bodySame := Term.lam.inj components.1
        have otherOrigin := origin.reannotate bodySame components.2
        have otherUncreated := fun created=>uncreated ((betaCreatedIncoming_of_same_erase bodySame).mpr created)
        obtain ⟨otherOld,otherOldLookup,otherOldLabel⟩ :=
          otherTurn.beta_preimage_label otherRedex otherOrigin atOtherMiddle otherUncreated
        exact ⟨oldPosition,oldNode,otherOld,oldLookup,otherOldLookup,
          oldLabel.trans middleLabel,otherOldLabel.trans otherMiddleLabel,
          .one (step:=turn) redex origin tailTrace⟩
end Lamping.Lambda.Marked
