import Lamping.Lambda.FunctionHistoryParents
import Lamping.Lambda.ResidualTagImages

namespace Lamping.Lambda.Marked
open Labelled

/-- APP ancestry transports a genuine SOURCE tag along the SAME history. -/
theorem History.trace_node_image
    {ps : List Path} {source target currentFn currentArg : LTerm}
    {m n : Marked} {p q name : Path} {currentStamp : Label}
    {labels : Labelled.History ps source target}
    (marked : History ps m n) (valid : Valid m)
    (erased : source.erase=m.erase)
    (origin : BetaNodeHistoryPreimage labels p q)
    (lookup : target.subterm p=some (.app currentStamp currentFn currentArg))
    (oldTag : q∈tracePositions name m) : p∈tracePositions name n := by
  induction origin generalizing m n with
  | nil => cases marked;exact oldTag
  | @one _ _ _ _ _ _ _ _ _ _ _ _ step remaining redex image tail ih =>
    cases marked with
    | cons reduction rest =>
      have beta := step.betaAt
      rw [erased] at beta
      obtain ⟨actual,actualStep,actualErase⟩ := lift_general_betaAt beta
      have equal := reduction.deterministic actualStep
      subst actual
      obtain ⟨middle,atMiddle,_last,constructor⟩ := tail.lastAtom_constructor lookup
      cases middle with
      | var => cases constructor
      | lam => cases constructor
      | app stamp fn arg =>
        have middleTag := reduction.trace_node_image valid step erased redex image atMiddle oldTag
        exact ih rest (reduction.valid valid) actualErase.symm lookup middleTag

/-- The selected residual is constructed from real FUNCTION ancestry;
it is not supplied as a premise. -/
theorem RelativeOldHistory.function_origin_selected_residual
    {source target oldBody oldArg currentBody : LTerm}
    {F ps : List Path} {marked : Marked} {name currentFn : Path}
    {oldApp oldLam currentLam : Label}
    (old : RelativeOldHistory F ps (mark F source.erase) marked)
    (labels : Labelled.History ps source target)
    (selectedName : name∈F)
    (oldRedex : source.subterm name=some (.app oldApp (.lam oldLam oldBody) oldArg))
    (trace : BetaNodeHistoryPreimage labels currentFn (name++[.fn]))
    (lookup : target.subterm currentFn=some (.lam currentLam currentBody)) :
    ∃currentParent currentApp currentArg,
      currentFn=currentParent++[.fn] ∧
      target.subterm currentParent=some (.app currentApp (.lam currentLam currentBody) currentArg) ∧
      BetaNodeHistoryPreimage labels currentParent name ∧
      currentParent∈tracePositions name marked ∧
      currentParent∈setResidualPositions F marked := by
  obtain ⟨parent,stamp,arg,coordinate,atParent,parentTrace⟩ :=
    trace.function_redex_parent oldRedex lookup
  have general := ((relativeOld_iff_relative (selected_mark F source.erase)).mp old).general
  have initialTag : name∈tracePositions name (mark F source.erase) := by
    apply (trace_mark F source.erase name name).mpr
    refine ⟨rfl,(mem_redexPositions _ _).mpr
      ⟨.app (.lam oldBody.erase) oldArg.erase,?_,True.intro⟩⟩
    rw [←LTerm.erase_subterm,oldRedex]
    rfl
  have tagged := general.trace_node_image (valid_mark F source.erase)
    (erase_mark F source.erase).symm parentTrace atParent initialTag
  exact ⟨parent,stamp,arg,coordinate,atParent,parentTrace,tagged,
    (mem_setResidualPositions F marked parent).mpr ⟨name,selectedName,tagged⟩⟩

/-- Completeness excludes only the selected old FUNCTION origin. -/
theorem RelativeOldHistory.normal_no_selected_function_origin
    {source target oldBody oldArg currentBody : LTerm}
    {F ps : List Path} {marked : Marked} {name currentFn : Path}
    {oldApp oldLam currentLam : Label}
    (old : RelativeOldHistory F ps (mark F source.erase) marked)
    (labels : Labelled.History ps source target)
    (normal : Normal marked) (selectedName : name∈F)
    (oldRedex : source.subterm name=some (.app oldApp (.lam oldLam oldBody) oldArg))
    (lookup : target.subterm currentFn=some (.lam currentLam currentBody)) :
    ¬BetaNodeHistoryPreimage labels currentFn (name++[.fn]) := by
  intro trace
  obtain ⟨parent,_,_,_,_,_,_,member⟩ :=
    old.function_origin_selected_residual labels selectedName oldRedex trace lookup
  have endpointSelected :=
    ((relativeOld_iff_relative (selected_mark F source.erase)).mp old).general.selected
      (selected_mark F source.erase)
  have empty := (normal_iff_selected_residual_empty endpointSelected).mp normal
  simp only [empty,List.not_mem_nil] at member

#print axioms History.trace_node_image
#print axioms RelativeOldHistory.function_origin_selected_residual
#print axioms RelativeOldHistory.normal_no_selected_function_origin
end Lamping.Lambda.Marked
