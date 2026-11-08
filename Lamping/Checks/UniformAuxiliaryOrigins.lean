import Lamping.Lambda.UniformAuxiliaryOrigins

namespace Lamping.Checks.UniformAuxiliaryOrigins
open Lambda Lambda.Labelled
/-- This intermediate annotation deliberately repeats the two selected
lambda degrees. It is not asserted to be INIT or a complete historical
family; the theorem needs only its actual two-event uniform OLD schedule. -/
private abbrev argument : LTerm := .lam (.atom 5) (.var (.atom 6) 0)
private abbrev redex : LTerm := .app (.atom 3) (.lam (.atom 1) (.var (.atom 4) 0)) argument
private abbrev reduced : LTerm := LTerm.contract (.atom 3) (.atom 1) (.var (.atom 4) 0) argument
private abbrev source : LTerm := .app (.atom 0) redex redex
private abbrev middle : LTerm := .app (.atom 0) reduced redex
private abbrev target : LTerm := .app (.atom 0) reduced reduced
private def first : StepAt [.fn] source middle := .fn (.root _ _ _ _)
private def second : StepAt [.arg] middle target := .arg (.root _ _ _ _)
private def labels : History [[.fn],[.arg]] source target := .cons first (.cons second (.nil _))
private def complete : ParallelStep [[.fn],[.arg]] source.erase target.erase := by
  refine ⟨[[.fn],[.arg]],.app [] (.lam (.var 0)) (.lam (.var 0)),
    (Marked.completeOld_iff _ _).mpr ⟨?_,by simp [Marked.Normal]⟩,rfl⟩
  exact .cons (.appL (.root _ _ _)) (.cons (.appR (.root _ _ _)) (.nil _))

/-- The endpoint is after TWO actual events; the copied binding's old
coordinate is locked by both operational preimages, including context. -/
theorem actual_two_old_binding : AuxiliaryAt target [.fn,.body] ∧AuxiliaryAt source [.fn,.arg,.body] := by
  have selected (p : Path) (member : p∈([[.fn],[.arg]] : List Path)) : source.degreeAt p=some (Labelled.Label.atom 1) := by
    rcases List.mem_cons.mp member with first | rest
    · subst p;rfl
    · have second := List.mem_singleton.mp rest
      subst p;rfl
  obtain ⟨oldPosition,oldNode,lookup,_label,trace,_eligible,auxiliary⟩ :=
    complete.complete.1.marker_free_auxiliary_origin (DegreeAligned.initial source [[.fn],[.arg]]) labels selected
      (show target.subterm [.fn,.body]=some (.var (.atom 6) 0) from rfl) (by trivial)
  have copyOrigin : BetaNodePreimage (.var (.atom 4) 0) argument [.fn] [.fn,.body] [.fn,.arg,.body] :=
    .copied (q:=[]) (relative:=[.body]) rfl rfl
  have contextOrigin : BetaNodePreimage (.var (.atom 4) 0) argument [.arg] [.fn,.body] [.fn,.body] :=
    .context (by rintro ⟨p,h⟩;cases h)
  have known : BetaNodeHistoryPreimage labels [.fn,.body] [.fn,.arg,.body] :=
    .one (step:=first) rfl copyOrigin (.one (step:=second) rfl contextOrigin (.nil target [.fn,.body]))
  have same := trace.unique known
  subst oldPosition
  have oldAux : AuxiliaryAt source [.fn,.arg,.body] := by
    constructor
    · rintro ⟨parent,stamp,fn,arg,split,_atParent⟩
      have last := congrArg List.getLast? split
      simp at last
    · rintro ⟨stamp,body,atLambda⟩
      cases atLambda
  exact ⟨auxiliary.mpr oldAux,oldAux⟩
#print axioms Marked.RelativeOldHistory.marker_free_auxiliary_origin
#print axioms actual_two_old_binding
end Lamping.Checks.UniformAuxiliaryOrigins
