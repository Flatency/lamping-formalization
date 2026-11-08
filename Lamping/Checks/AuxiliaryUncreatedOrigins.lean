import Lamping.Lambda.AuxiliaryUncreatedOrigins

namespace Lamping.Checks.AuxiliaryUncreatedOrigins
open Lambda Lambda.Labelled
private abbrev i : LTerm := .lam (.atom 4) (.var (.atom 5) 0)
private abbrev source : LTerm := .app (.atom 0)
  (.app (.atom 1) (.lam (.atom 2) (.var (.atom 3) 0)) i) i
private abbrev target : LTerm := .app (.atom 0)
  (LTerm.contract (.atom 1) (.atom 2) (.var (.atom 3) 0) i) i
private def turn : StepAt [.fn] source target := .fn (.root _ _ _ _)

/-- A genuine closed beta below FUNCTION preserves a root APP auxiliary
edge. The root is external and has no fabricated last child step. -/
theorem actual_root_app_auxiliary : AuxiliaryAt target [] ∧AuxiliaryAt source [] := by
  have origin : BetaNodePreimage (.var (.atom 3) 0) i [.fn] [] [] :=
    .context (by rintro ⟨p,h⟩;cases h)
  obtain ⟨old,lookup,_label,_eligible,auxiliary⟩ := turn.uncreated_auxiliary_origin
    (show source.subterm [.fn]=some (.app (.atom 1) (.lam (.atom 2) (.var (.atom 3) 0)) i) from rfl)
    origin (show target.subterm []=some target from rfl) (by decide)
  have sourceAux : AuxiliaryAt source [] := by simp [AuxiliaryAt,LTerm.subterm]
  exact ⟨auxiliary.mpr sourceAux,sourceAux⟩

private abbrev copying : LTerm := .app (.atom 0) (.lam (.atom 1) (.var (.atom 2) 0)) i
private abbrev copied : LTerm := LTerm.contract (.atom 0) (.atom 1) (.var (.atom 2) 0) i
private def copiedTurn : StepAt [] copying copied := .root _ _ _ _

/-- A genuinely copied variable binding edge remains auxiliary at its
actual ARG/BODY ancestor, with a different nonempty syntax coordinate. -/
theorem actual_copied_binding_auxiliary : AuxiliaryAt copied [.body] ∧AuxiliaryAt copying [.arg,.body] := by
  have origin : BetaNodePreimage (.var (.atom 2) 0) i [] [.body] [.arg,.body] :=
    .copied (q:=[]) (relative:=[.body]) rfl rfl
  obtain ⟨old,lookup,_label,_eligible,auxiliary⟩ := copiedTurn.uncreated_auxiliary_origin rfl origin
    (show copied.subterm [.body]=some (.var (.atom 5) 0) from rfl) (by decide)
  have sourceAux : AuxiliaryAt copying [.arg,.body] := by
    constructor
    · rintro ⟨parent,stamp,fn,arg,split,_atParent⟩
      have last := congrArg List.getLast? split
      simp at last
    · rintro ⟨stamp,body,atLambda⟩
      cases atLambda
  exact ⟨auxiliary.mpr sourceAux,sourceAux⟩
#print axioms BetaNodePreimage.uncreated_last_step
#print axioms StepAt.uncreated_auxiliary_origin
#print axioms actual_root_app_auxiliary
#print axioms actual_copied_binding_auxiliary
end Lamping.Checks.AuxiliaryUncreatedOrigins
