import Lamping.Lambda.LOHistory
import Lamping.Lambda.StandardizationCreation
import Lamping.Lambda.StandardizationLeftResiduals

namespace Lamping.Lambda

/-- Contracting strictly to the right preserves the actual global LO search
result at its original path. Earlier target redexes are reflected to source. -/
theorem BetaAt.loRedex_preserved_of_right {t u : Term} {p q : Path}
    (head : BetaAt t p u) (hit : loRedex t=some q) (right : LeftOf q p) :
    loRedex u=some q := by
  let source : RedexOcc t := ⟨q,loRedex_sound hit⟩
  obtain ⟨target,position,_residual,_unique⟩ := head.left_residual_exists source right
  have leftmost : ∀ other : RedexOcc u, ¬LeftOf other.val target.val := by
    intro other before
    rw [position] at before
    have old : ∃ z, subtermAt t other.val=some z ∧ IsRedex z :=
      head.redex_reflect_before right before other.property
    exact loRedex_leftmost hit ⟨other.val,old⟩ before
  calc
    loRedex u = some target.val := loRedex_eq_of_leftmost target leftmost
    _ = some q := congrArg some position

private theorem beta_history_lo_right {t u : Term} {ps : List Path} {q : Path}
    (history : BetaHistory ps t u) (hit : loRedex t=some q)
    (right : ∀ p ∈ ps, LeftOf q p) : loRedex u=some q := by
  revert hit right
  induction history with
  | nil =>
    intro hit _right
    exact hit
  | cons first rest ih =>
    intro hit right
    have next := first.loRedex_preserved_of_right hit
      (right _ (List.mem_cons_self ..))
    exact ih next (fun p hp => right p (List.mem_cons_of_mem _ hp))

/-- The supplied occurrence-indexed derivation is retained literally; each
actual contraction must be strictly to the right of the same original q. -/
theorem Derivation.loRedex_preserved_of_right {t u : Term} {q : Path}
    (history : Derivation t u) (hit : loRedex t=some q)
    (right : ∀ p ∈ history.paths, LeftOf q p) : loRedex u=some q :=
  beta_history_lo_right history.valid hit right

/-- A genuine right-side parallel-history invariant supplies the required
condition on its actual underlying contraction schedule. -/
theorem RightHistory.loRedex_preserved {t u : Term} {q : Path}
    {rho : ParallelHistory t u} (right : RightHistory q rho)
    (hit : loRedex t=some q) : loRedex u=some q :=
  rho.derivation.loRedex_preserved_of_right hit right.paths_right

#print axioms BetaAt.loRedex_preserved_of_right
#print axioms Derivation.loRedex_preserved_of_right
#print axioms RightHistory.loRedex_preserved

end Lamping.Lambda
