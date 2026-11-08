import Lamping.Lambda.HeadVariableInvariant
import Lamping.Lambda.NoTagTransport
namespace Lamping.Lambda.Marked

/-- Before a particular outer beta fires, its future created application
identity occurs only in the body, headed by that binder's variable. -/
def RootHeadGuard (r : Path) : Marked → Prop
  | .app l (.lam b) a | .red l b a =>
      HeadVariable r 0 b ∧ r ∉ l ∧ tracePositions r a=[]
  | _ => False

theorem ReductionAt.trace_empty (h : ReductionAt p t u) (empty : tracePositions r t=[]) :
    tracePositions r u=[] := by
  exact (h.trace_outside (by intro q; rw [empty]; simp)).trans empty

/-- Reducing any redex other than the guarded outer root preserves its
potential-application invariant, even through argument duplication below it. -/
theorem ReductionAt.rootHeadGuard (h : ReductionAt p t u) (nonroot : p≠[])
    (guard : RootHeadGuard r t) : RootHeadGuard r u := by
  cases h with
  | appRoot => exact False.elim (nonroot rfl)
  | redRoot => exact False.elim (nonroot rfl)
  | lam => exact False.elim guard
  | @appL p f f' l a h =>
    cases f with
    | var => exact False.elim guard
    | app => exact False.elim guard
    | red => exact False.elim guard
    | lam b =>
      cases h with
      | lam h => exact ⟨h.headVariable guard.1,guard.2⟩
  | @appR p a a' l f h =>
    cases f with
    | var => exact False.elim guard
    | app => exact False.elim guard
    | red => exact False.elim guard
    | lam b => exact ⟨guard.1,guard.2.1,h.trace_empty guard.2.2⟩
  | redL h => exact ⟨h.headVariable guard.1,guard.2⟩
  | redR h => exact ⟨guard.1,guard.2.1,h.trace_empty guard.2.2⟩

private theorem guard_no_redex_app (h : HeadVariable r 0 b) (notRoot : r∉l)
    (noArgument : tracePositions r a=[]) (tag : r∈tagsAt (.app l (.lam b) a) q)
    (redex : ∃ u, subtermAt (Marked.app l (.lam b) a).erase q=some u ∧ IsRedex u) : False := by
  cases q with
  | nil => exact notRoot tag
  | cons s q =>
    cases s with
    | body => simp [tagsAt] at tag
    | arg =>
      have ht := (mem_tagsAt a r q).mp tag
      rw [noArgument] at ht
      simp at ht
    | fn =>
      cases q with
      | nil => simp [tagsAt] at tag
      | cons s q =>
        cases s with
        | fn => simp [tagsAt] at tag
        | arg => simp [tagsAt] at tag
        | body => exact h.tags_not_redex tag redex

theorem RootHeadGuard.no_redex (guard : RootHeadGuard r t) (tag : r∈tagsAt t q) :
    ¬ ∃ u, subtermAt t.erase q=some u ∧ IsRedex u := by
  intro redex
  cases t with
  | var => exact guard
  | lam => exact guard
  | app l f a =>
    cases f with
    | var => exact guard
    | app => exact guard
    | red => exact guard
    | lam b => exact guard_no_redex_app guard.1 guard.2.1 guard.2.2 tag redex
  | red l b a =>
    have tagsEq : tagsAt (.red l b a) q=tagsAt (.app l (.lam b) a) q := by
      cases q with
      | nil => rfl
      | cons s q =>
        cases s with
        | arg => rfl
        | body => rfl
        | fn =>
          cases q with
          | nil => rfl
          | cons s q => cases s <;> rfl
    exact guard_no_redex_app guard.1 guard.2.1 guard.2.2 (tagsEq ▸ tag) redex
end Lamping.Lambda.Marked
