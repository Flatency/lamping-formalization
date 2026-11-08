import Lamping.Lambda.ResidualNodePreimages
namespace Lamping.Lambda.Labelled
/-- A real OLD redex's FUNCTION lambda remains the corresponding child.
This excludes a newly substituted function variable using the actual old shape. -/
theorem BetaNodePreimage.redex_function_child {source : LTerm}
    (redex : source.subterm site=some (.app beta (.lam alpha body) argument))
    (origin : BetaNodePreimage body argument site p oldPosition)
    (oldRedex : source.subterm oldPosition=some (.app stamp (.lam lambdaStamp oldBody) oldArg)) :
    BetaNodePreimage body argument site (p++[.fn]) (oldPosition++[.fn]) := by
  cases origin with
  | @context p outside =>
    refine .context ?_
    rintro ⟨relative,equal⟩
    rcases List.append_eq_append_iff.mp equal with ⟨extra,siteEq,tailEq⟩ | ⟨extra,pEq,_⟩
    · cases extra with
      | nil => exact outside ⟨[],by simpa only [List.append_nil] using siteEq.symm⟩
      | cons head rest =>
        have tailEmpty : rest++relative=[] := (List.cons.inj tailEq).2.symm
        obtain ⟨restEmpty,relativeEmpty⟩ := List.append_eq_nil_iff.mp tailEmpty
        subst relative
        have siteAt : source.subterm site=some (.lam lambdaStamp oldBody) := by
          rw [←show p++[.fn]=site by simpa only [List.append_nil] using equal,
            LTerm.subterm_append,oldRedex];rfl
        rw [redex] at siteAt;cases siteAt
    · exact outside ⟨extra,pEq⟩
  | @retained relative old lookup nonselected =>
    have atOld : source.subterm ((site++[.fn,.body])++relative)=some old := by
      rw [List.append_assoc,LTerm.subterm_append,redex]
      simpa only [LTerm.subterm,Option.bind_some] using lookup
    have shape : old=.app stamp (.lam lambdaStamp oldBody) oldArg := Option.some.inj (atOld.symm.trans oldRedex)
    subst old
    have child : body.subterm (relative++[.fn])=some (.lam lambdaStamp oldBody) := by
      rw [LTerm.subterm_append,lookup];rfl
    simpa only [List.append_assoc] using
      (BetaNodePreimage.retained (site:=site) (argument:=argument) child (by intro s h;cases h))
  | @copied q relative old occurs lookup =>
    have atOld : source.subterm ((site++[.arg])++relative)=some old := by
      rw [List.append_assoc,LTerm.subterm_append,redex]
      simpa only [LTerm.subterm,Option.bind_some] using lookup
    have shape : old=.app stamp (.lam lambdaStamp oldBody) oldArg := Option.some.inj (atOld.symm.trans oldRedex)
    subst old
    have child : argument.subterm (relative++[.fn])=some (.lam lambdaStamp oldBody) := by
      rw [LTerm.subterm_append,lookup];rfl
    simpa only [List.append_assoc] using
      (BetaNodePreimage.copied (site:=site) occurs child)
end Lamping.Lambda.Labelled
namespace Lamping.Lambda.Marked
open Labelled
private theorem tag_app_redex {source : LTerm} (valid : Valid m) (erased : source.erase=m.erase)
    (member : p∈tracePositions name m) :
    ∃ beta alpha body argument,source.subterm p=some (.app beta (.lam alpha body) argument) := by
  obtain ⟨bare,lookup,isRedex⟩ := tracePositions_sound valid member
  rw [←erased] at lookup
  obtain ⟨alpha,degree⟩ := degreeAt_exists source ⟨p,⟨bare,lookup,isRedex⟩⟩
  obtain ⟨beta,body,argument,redex⟩ := LTerm.degreeAt_redex degree
  exact ⟨beta,alpha,body,argument,redex⟩
theorem History.trace_function_history_preimage
    (marked : History ps m n) (valid : Valid m)
    (labels : Labelled.History ps source target) (erased : source.erase=m.erase)
    (member : p∈tracePositions name n) :
    ∃ old,old∈tracePositions name m ∧BetaNodeHistoryPreimage labels (p++[.fn]) (old++[.fn]) := by
  induction marked generalizing source target p with
  | nil => cases labels;exact ⟨p,member,.nil _ _⟩
  | cons reduction tail ih =>
    cases labels with
    | cons turn remaining =>
      have beta := turn.betaAt
      rw [erased] at beta
      obtain ⟨actual,actualStep,actualErase⟩ := lift_general_betaAt beta
      have equal := reduction.deterministic actualStep
      subst actual
      obtain ⟨middlePosition,middleMember,tailTrace⟩ :=
        ih (reduction.valid valid) remaining actualErase.symm member
      obtain ⟨old,beta,alpha,body,argument,oldMember,redex,origin⟩ :=
        reduction.trace_node_preimage valid turn erased middleMember
      obtain ⟨stamp,lambdaStamp,oldBody,oldArg,atOld⟩ := tag_app_redex valid erased oldMember
      exact ⟨old,oldMember,.one (step:=turn) redex (origin.redex_function_child redex atOld) tailTrace⟩
theorem History.initial_name_function_preimage
    (marked : History ps (mark F source.erase) n)
    (labels : Labelled.History ps source target) (member : p∈tracePositions name n) :
    BetaNodeHistoryPreimage labels (p++[.fn]) (name++[.fn]) := by
  obtain ⟨old,oldMember,trace⟩ := marked.trace_function_history_preimage (valid_mark F source.erase) labels (erase_mark F source.erase).symm member
  obtain ⟨same,_⟩ := (trace_mark F source.erase name old).mp oldMember
  subst old;exact trace
theorem RelativeOldHistory.selected_app_function_preimages
    (old : RelativeOldHistory F ps (mark F source.erase) n)
    (labels : Labelled.History ps source target)
    (member : p∈setResidualPositions F n) :
    ∃ name∈F,
      (∃ beta alpha body argument,source.subterm name=some (.app beta (.lam alpha body) argument)) ∧
      BetaNodeHistoryPreimage labels p name ∧
      BetaNodeHistoryPreimage labels (p++[.fn]) (name++[.fn]) := by
  obtain ⟨name,chosen,residual⟩ := (mem_setResidualPositions F n p).mp member
  have general := ((relativeOld_iff_relative (selected_mark F source.erase)).mp old).general
  obtain ⟨redex,appTrace⟩ := general.initial_name_node_preimage labels residual
  exact ⟨name,chosen,redex,appTrace,general.initial_name_function_preimage labels residual⟩
end Lamping.Lambda.Marked