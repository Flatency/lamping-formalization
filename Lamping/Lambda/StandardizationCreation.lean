import Lamping.Lambda.StandardizationLeftResiduals
import Lamping.Lambda.CreationLocality
namespace Lamping.Lambda

/-- No position lies strictly between a path and its immediate function
child in the leftmost-outermost order. -/
theorem LeftOf.no_between_fn (h : LeftOf q s) (k : LeftOf s (q++[.fn])) : False := by
  induction q generalizing s with
  | nil =>
    cases s with
    | nil => exact LeftOf.irrefl [] h
    | cons e tail =>
      cases k with
      | child _ kk => cases kk
  | cons e q ih =>
    cases h with
    | child _ hh =>
      cases k with
      | child _ kk => exact ih hh kk
    | branch a b => cases k

/-- A contraction to the right of a protected source occurrence cannot
create a redex still further to its left. This follows from actual syntax
creation locality, without a standardization hypothesis. -/
theorem BetaAt.redex_reflect_before (h : BetaAt t p u)
    (before : LeftOf s p) (earlier : LeftOf q s)
    (newRedex : ∃ z, subtermAt u q=some z ∧ IsRedex z) :
    ∃ z, subtermAt t q=some z ∧ IsRedex z := by
  classical
  by_cases old : ∃ z, subtermAt t q=some z ∧ IsRedex z
  · exact old
  exfalso
  rcases h.creation_locality newRedex old with inside | parent
  · exact (earlier.trans before).not_inside_right inside
  · subst p
    exact earlier.no_between_fn before

end Lamping.Lambda
