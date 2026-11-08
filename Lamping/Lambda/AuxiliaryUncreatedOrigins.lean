import Lamping.Lambda.UncreatedPrerequisiteReadings
import Lamping.Lambda.BetaPreimageLabels
namespace Lamping.Lambda.Labelled
private theorem last_append_nonempty {A : Type} (pre : List A) {rest : List A} (nonempty : rest≠[]) :
    (pre++rest).getLast?=rest.getLast? := by
  have some := List.getLast?_eq_some_getLast nonempty
  simp only [List.getLast?_append,some,Option.some_or]

theorem BetaNodePreimage.uncreated_last_step
    (origin : BetaNodePreimage body argument site p oldPosition)
    (uncreated : ¬BetaCreatedIncoming body site p) : p.getLast?=oldPosition.getLast? := by
  cases origin with
  | context => rfl
  | @retained relative node lookup nonselected =>
    have nonempty : relative≠[] := by
      intro empty
      exact uncreated (Or.inl (by simp only [empty,List.append_nil]))
    rw [last_append_nonempty _ nonempty,last_append_nonempty _ nonempty]
  | @copied q relative node occurs lookup =>
    have nonempty : relative≠[] := by
      intro empty
      apply uncreated
      exact betaCreatedIncoming_iff.mpr (Or.inr ⟨q,occurs,by simp only [empty,List.append_nil]⟩)
    rw [last_append_nonempty _ nonempty,last_append_nonempty _ nonempty]

private theorem function_departure_iff_last {t current : LTerm} {p : Path}
    (lookup : t.subterm p=some current) :
    (∃ parent stamp fn arg,p=parent++[.fn] ∧t.subterm parent=some (.app stamp fn arg)) ↔
      p.getLast?=some .fn := by
  constructor
  · rintro ⟨parent,stamp,fn,arg,split,_atParent⟩
    rw [split,List.getLast?_concat]
  · intro last
    obtain ⟨parent,split⟩ := List.getLast?_eq_some_iff.mp last
    have inside := lookup
    rw [split,LTerm.subterm_append] at inside
    cases atParent : t.subterm parent with
    | none => rw [atParent] at inside;cases inside
    | some node =>
      rw [atParent,Option.bind_some] at inside
      cases node with
      | var => cases inside
      | lam => cases inside
      | app stamp fn arg => exact ⟨parent,stamp,fn,arg,split,atParent⟩

private theorem eligible_iff_last_or_lambda
    (lookup : t.subterm p=some current) :
    PrerequisiteEligible t p ↔p.getLast?=some .fn ∨current.constructorTag=1 := by
  unfold PrerequisiteEligible
  rw [function_departure_iff_last lookup]
  apply or_congr Iff.rfl
  constructor
  · rintro ⟨stamp,body,atLambda⟩
    have same := Option.some.inj (lookup.symm.trans atLambda)
    rw [same];rfl
  · intro tag
    cases current with
    | var => cases tag
    | app => cases tag
    | lam stamp body => exact ⟨stamp,body,lookup⟩

/-- A noncreated incoming occurrence preserves its genuine auxiliary role
at THIS old coordinate. Labels and constructor identity are derived from
actual beta syntax, not assumed as incidence-map certificates. -/
theorem StepAt.uncreated_auxiliary_origin
    {source target body argument current : LTerm} {site p oldPosition : Path} {beta alpha : Label}
    (step : StepAt site source target)
    (redex : source.subterm site=some (.app beta (.lam alpha body) argument))
    (origin : BetaNodePreimage body argument site p oldPosition)
    (lookup : target.subterm p=some current)
    (uncreated : ¬BetaCreatedIncoming body site p) :
    ∃ old,source.subterm oldPosition=some old ∧old.label=current.label ∧
      (PrerequisiteEligible target p ↔PrerequisiteEligible source oldPosition) ∧
      (AuxiliaryAt target p ↔AuxiliaryAt source oldPosition) := by
  obtain ⟨old,oldLookup,sameTag⟩ := step.preimage_node_constructor redex origin lookup
  obtain ⟨labelNode,labelLookup,sameLabel⟩ := step.beta_preimage_label redex origin lookup uncreated
  have sameNode := Option.some.inj (labelLookup.symm.trans oldLookup)
  subst labelNode
  have eligible : PrerequisiteEligible target p ↔PrerequisiteEligible source oldPosition := by
    rw [eligible_iff_last_or_lambda lookup,eligible_iff_last_or_lambda oldLookup,
      origin.uncreated_last_step uncreated,sameTag]
  exact ⟨old,oldLookup,sameLabel,eligible,by
    rw [auxiliaryAt_iff_not_eligible,auxiliaryAt_iff_not_eligible,eligible]⟩
end Lamping.Lambda.Labelled
