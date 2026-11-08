import Lamping.Lambda.AuxiliaryUncreatedOrigins
import Lamping.Lambda.UniformAnnotatedOrigins
namespace Lamping.Lambda.Marked
open Labelled
/-- Marker-free auxiliary status is transported along THIS actual OLD
history. Intermediate labels may be unsafe; only the final incoming label
is tested, and all selected degrees come from the SAME original map. -/
theorem RelativeOldHistory.marker_free_auxiliary_origin
    {F ps : List Path} {m n : Marked} (old : RelativeOldHistory F ps m n)
    {d : Path →Option Label} {source target current : LTerm} {p : Path} {degree : Label}
    (aligned : DegreeAligned d m source) (labels : Labelled.History ps source target)
    (selected : ∀ path∈F,d path=some degree)
    (lookup : target.subterm p=some current)
    (safe : current.label.OuterBarsSafe (fun payload=>payload≠degree)) :
    ∃ oldPosition oldNode,source.subterm oldPosition=some oldNode ∧oldNode.label=current.label ∧
      BetaNodeHistoryPreimage labels p oldPosition ∧
      (PrerequisiteEligible target p ↔PrerequisiteEligible source oldPosition) ∧
      (AuxiliaryAt target p ↔AuxiliaryAt source oldPosition) := by
  induction old generalizing source target p with
  | nil => cases labels;exact ⟨p,current,lookup,rfl,.nil _ _,Iff.rfl,Iff.rfl⟩
  | @cons path _ _ _ _ reduction member tail ih =>
    cases labels with
    | @cons _ _ middle _ _ turn remaining =>
      obtain ⟨midPosition,midNode,midLookup,midLabel,tailTrace,tailEligible,tailAux⟩ :=
        ih (aligned.step reduction turn) remaining lookup
      obtain ⟨name,chosen,residual⟩ := (mem_setResidualPositions _ _ _).mp member
      have atDegree := (aligned.trace_degree residual).trans (selected name chosen)
      obtain ⟨beta,body,argument,redex⟩ := LTerm.degreeAt_redex atDegree
      have uncreated : ¬BetaCreatedIncoming body path midPosition := by
        intro created
        apply turn.created_label_not_safe redex midLookup created
        rw [midLabel];exact safe
      obtain ⟨oldPosition,origin⟩ := turn.beta_node_preimage redex midLookup
      obtain ⟨oldNode,oldLookup,oldLabel,eligible,auxiliary⟩ :=
        turn.uncreated_auxiliary_origin redex origin midLookup uncreated
      exact ⟨oldPosition,oldNode,oldLookup,oldLabel.trans midLabel,
        .one (step:=turn) redex origin tailTrace,tailEligible.trans eligible,tailAux.trans auxiliary⟩
end Lamping.Lambda.Marked
