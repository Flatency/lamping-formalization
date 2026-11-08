import Lamping.Lambda.AuxiliaryUncreatedOrigins
import Lamping.Lambda.BetaChainExistenceReflection
namespace Lamping.Lambda.Labelled
private theorem last_append_nonempty {A : Type} (pre : List A) {rest : List A} (nonempty : rest≠[]) :
    (pre++rest).getLast?=rest.getLast? := by
  have last := List.getLast?_eq_some_getLast nonempty
  simp only [List.getLast?_append,last,Option.some_or]

/-- An old FUNCTION ending is retained in the current path. The converse
fails at created roots, whose old path ends BODY or ARG. -/
theorem BetaNodePreimage.current_fn_of_old_fn
    (origin : BetaNodePreimage body argument site p oldPosition)
    (last : oldPosition.getLast?=some .fn) : p.getLast?=some .fn := by
  cases origin with
  | context => exact last
  | @retained relative node lookup nonselected =>
    cases relative with
    | nil => simp at last
    | cons child rest =>
      rw [last_append_nonempty _ (by simp)] at last ⊢
      exact last
  | @copied q relative node occurs lookup =>
    cases relative with
    | nil => simp at last
    | cons child rest =>
      rw [last_append_nonempty _ (by simp)] at last ⊢
      exact last

/-- Target auxiliary role reflects to THIS actual old node, even for a
created incoming edge. This is one-way node ancestry, not incidence mapping. -/
theorem StepAt.auxiliary_node_origin
    {source target body argument current : LTerm} {site p oldPosition : Path} {beta alpha : Label}
    (step : StepAt site source target)
    (redex : source.subterm site=some (.app beta (.lam alpha body) argument))
    (origin : BetaNodePreimage body argument site p oldPosition)
    (lookup : target.subterm p=some current)
    (aux : AuxiliaryAt target p) :
    ∃old,source.subterm oldPosition=some old ∧AuxiliaryAt source oldPosition := by
  obtain ⟨old,oldLookup,sameTag⟩ := step.preimage_node_constructor redex origin lookup
  refine ⟨old,oldLookup,?_,?_⟩
  · rintro ⟨oldParent,stamp,fn,arg,split,atParent⟩
    have last : oldPosition.getLast?=some .fn := by rw [split,List.getLast?_concat]
    obtain ⟨parent,currentSplit⟩ := List.getLast?_eq_some_iff.mp (origin.current_fn_of_old_fn last)
    have inside := lookup
    rw [currentSplit,LTerm.subterm_append] at inside
    cases atCurrentParent : target.subterm parent with
    | none => rw [atCurrentParent] at inside;cases inside
    | some node =>
      rw [atCurrentParent,Option.bind_some] at inside
      cases node with
      | var => cases inside
      | lam => cases inside
      | app stamp fn arg => exact aux.1 ⟨parent,stamp,fn,arg,currentSplit,atCurrentParent⟩
  · rintro ⟨stamp,inner,atLambda⟩
    have same := Option.some.inj (oldLookup.symm.trans atLambda)
    rw [same] at sameTag
    cases current with
    | var => cases sameTag
    | app => cases sameTag
    | lam stamp inner => exact aux.2 ⟨stamp,inner,lookup⟩

/-- Structural composition on the SAME actual operational node trace.
No OLD/freshness/label or successful endpoint assumptions are required. -/
theorem BetaNodeHistoryPreimage.auxiliary_source
    {ps : List Path} {source target current : LTerm} {labels : History ps source target}
    {p oldPosition : Path}
    (trace : BetaNodeHistoryPreimage labels p oldPosition)
    (lookup : target.subterm p=some current)
    (aux : AuxiliaryAt target p) :
    ∃old,source.subterm oldPosition=some old ∧AuxiliaryAt source oldPosition := by
  induction trace with
  | nil => exact ⟨current,lookup,aux⟩
  | @one site ps source middle target body argument beta alpha p mid oldPosition step remaining redex origin tail ih =>
    obtain ⟨midNode,atMid,midAux⟩ := ih lookup aux
    exact step.auxiliary_node_origin redex origin atMid midAux
#print axioms BetaNodePreimage.current_fn_of_old_fn
#print axioms StepAt.auxiliary_node_origin
#print axioms BetaNodeHistoryPreimage.auxiliary_source
end Lamping.Lambda.Labelled
