import Lamping.Lambda.DevelopmentTheory
namespace Lamping.Checks.Residuals
open Lambda Lambda.Marked

-- Capture avoidance: the free argument stays free underneath the surviving λ.
example : Marked.contract (.lam (.var 1)) (.var 0) = .lam (.var 1) := by decide
example : Lambda.contract (.lam (.var 1)) (.var 0) = .lam (.var 1) := by decide

-- Duplication copies the old name to precisely the two argument copies.
def copied : Marked := Marked.contract (.app [] (.var 0) (.var 0))
  (.app [[.arg]] (.lam (.var 0)) (.var 0))
example : tracePositions [.arg] copied = [[.fn], [.arg]] := by decide
example : Valid copied := by simp [copied, Marked.contract, Marked.subst, single, Valid]
example : tracePositions [] copied = [] := by decide

-- Erasure destroys all names in an unused argument.
def erased : Marked := Marked.contract (.var 1)
  (.app [[.arg]] (.lam (.var 0)) (.var 0))
example : erased = .var 0 := by decide
example : tracePositions [.arg] erased = [] := by decide

-- Substitution exposes a fresh redex; it has no old name and is not active.
def created : Marked := Marked.contract (.app [] (.var 0) (.var 1)) (.lam (.var 0))
example : created = .app [] (.lam (.var 0)) (.var 0) := by decide
example : redexPositions created.erase = [[]] := by decide
example : tracePositions [] created = [] := by decide
example : activePositions created = [] := by decide
example : Normal created := by trivial

-- A selected argument may be duplicated; either complete schedule is covered.
def nested : Marked := .red [[]] (.app [] (.var 0) (.var 0))
  (.red [[.arg]] (.var 0) (.var 0))
example : activePositions nested = [[], [.arg]] := by decide
example : nested.dev = .app [] (.var 0) (.var 0) := by decide
example : ∃ u, Complete nested u := complete_exists nested
example {u v : Marked} (h : Complete nested u) (k : Complete nested v) :
    u = v ∧ tracePositions [.arg] u = tracePositions [.arg] v :=
  ⟨complete_unique h k, complete_residual_independent h k _⟩

example : ¬ ∃ f : Nat → Marked, ∀ n, Marked.Step (f n) (f (n+1)) :=
  no_infinite_development

#print axioms Marked.Step.weight_lt
#print axioms Marked.no_infinite_development
#print axioms Marked.dev_subst
#print axioms Marked.complete_unique
#print axioms Marked.lift_betaAt
#print axioms Marked.tracePositions_sound
#print axioms Marked.complete_residual_independent





-- The initial finite set selects the outer redex, but not the old argument R.
def duplicationTerm : Term := .app (.lam (.app (.var 0) (.var 0)))
  (.app (.lam (.var 0)) (.var 0))
example : activePositions (mark [[]] duplicationTerm) = [[]] := by decide
example : tracePositions [.arg] (mark [[]] duplicationTerm) = [[.arg]] := by decide
example : Marked.StepAt [] (mark [[]] duplicationTerm) copied := .root _ _ _
example : Complete (mark [[]] duplicationTerm) copied :=
  ⟨.cons (.root _ _ _) (.refl _), by trivial⟩
example : redexPositions copied.erase = [[.fn], [.arg]] := by decide

-- A complete empty development may leave many real beta redexes.
example : Complete (mark [] duplicationTerm) (mark [] duplicationTerm) :=
  ⟨.refl _, by trivial⟩
example : redexPositions (mark [] duplicationTerm).erase ≠ [] := by decide

-- A newly created redex can be fired along a general beta history, while it
-- is excluded from the development of the original singleton selection.
def creationTerm : Term := .app (.lam (.app (.var 0) (.var 1))) (.lam (.var 0))
example : ReductionAt [] (mark [[]] creationTerm) created := .redRoot _ _ _
example : ReductionAt [] created (.var 0) := .appRoot _ _ _
example : History [[], []] (mark [[]] creationTerm) (.var 0) :=
  .cons (.redRoot _ _ _) (.cons (.appRoot _ _ _) (.nil _))
example : ¬ ∃ u, Marked.Step created u := (normal_iff_no_step created).mp (by trivial)

-- General beta transport follows an unselected old R into the root position.
def passiveTerm : Term := .app (.lam (.var 0)) (.app (.lam (.var 0)) (.var 0))
def passiveAfter : Marked := .app [[.arg]] (.lam (.var 0)) (.var 0)
example : ReductionAt [] (mark [] passiveTerm) passiveAfter := .appRoot _ _ _
example : tracePositions [.arg] passiveAfter = [[]] := by decide
example : tracePositions [] passiveAfter = [] := by decide
example : ReductionAt [] passiveAfter (.var 0) := .appRoot _ _ _
example : tracePositions [.arg] (Marked.var 0) = [] := by decide

#print axioms Marked.lift_general_betaAt
#print axioms Marked.lift_betaHistory
#print axioms Marked.History.deterministic
#print axioms Marked.RelativeHistory.length_bound
#print axioms Marked.finite_selection_complete
#print axioms Marked.finite_developments_independent
#print axioms Marked.initial_residual
#print axioms Marked.residual_composition



-- Two different complete schedules for the same nested selection.
def nestedOuter : Marked := .app [] (.red [[.arg]] (.var 0) (.var 0))
  (.red [[.arg]] (.var 0) (.var 0))
def nestedLeftDone : Marked := .app [] (.var 0) (.red [[.arg]] (.var 0) (.var 0))
def nestedInner : Marked := .red [[]] (.app [] (.var 0) (.var 0)) (.var 0)
def nestedEnd : Marked := .app [] (.var 0) (.var 0)
example : RelativeHistory [[], [.fn], [.arg]] nested nestedEnd :=
  .cons (.root _ _ _)
    (.cons (.appL (.root _ _ _)) (.cons (.appR (.root _ _ _)) (.nil _)))
example : RelativeHistory [[.arg], []] nested nestedEnd :=
  .cons (.redR (.root _ _ _)) (.cons (.root _ _ _) (.nil _))
example : Closed (.lam duplicationTerm) := by simp [Closed, Scoped, duplicationTerm]

-- Source-level theorem applies directly to genuine original RedexOcc values.
example (F : List Path) (t : Term) (h : CompleteOldDevelopment F t ps u)
    (k : CompleteOldDevelopment F t qs v) (r : RedexOcc t) :
    u.erase = v.erase ∧ tracePositions r.val u = tracePositions r.val v :=
  completeOld_independent h k r
example (F : List Path) (t : Term) : ∃ ps u, CompleteOldDevelopment F t ps u :=
  completeOld_exists F t

#print axioms Marked.relativeOld_iff_relative
#print axioms Marked.normal_iff_selected_residual_empty
#print axioms Marked.completeOld_exists
#print axioms Marked.completeOld_independent
#print axioms Marked.no_infinite_relativeOld
#print axioms Marked.relativeOld_length_bound
end Lamping.Checks.Residuals

