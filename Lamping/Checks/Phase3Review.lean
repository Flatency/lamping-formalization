import Lamping.Lambda.Occurrences
import Lamping.Lambda.BetaPaths
import Lamping.Lambda.DevelopmentMeasure
import Lamping.Lambda.ResidualInit
import Lamping.Lambda.ResidualSelection
import Lamping.Lambda.DevelopmentTheory
import Lamping.Lamping.FreeVars
import Lamping.Lamping.System
import Lamping.Lamping.Encoding
import Lamping.Lamping.Fixtures

/- Independent phase-3 probes. Further AG and residual checks are added only
   after their implementation interfaces stabilize. -/
namespace Lamping.Checks.Phase3Review
open Lamping.Lambda

/-- Independent substitution oracle: the outer free variable must survive
    passage beneath a new binder. A capturing implementation returns lam(var 0). -/
example : subst (fun | 0 => .var 0 | n+1 => .var n)
    (.lam (.var 1)) = .lam (.var 1) := rfl

example : subst (fun | 0 => .var 0 | n+1 => .var n)
    (.lam (.var 1)) ≠ .lam (.var 0) := by decide

/-- Nested redexes remain distinct occurrences even when they have equal shape. -/
private def nested : Term :=
  .app (.lam (.var 0)) (.app (.lam (.var 0)) (.var 0))
example : redexPositions nested = [[], [.arg]] := rfl

#print axioms scoped_subst
#print axioms mem_redexPositions
/-- The actual root contraction oracle includes lifting under the surviving binder. -/
example : BetaAt (.app (.lam (.lam (.var 1))) (.var 0)) [] (.lam (.var 1)) :=
  ⟨_, _, rfl, rfl⟩

example : ¬ BetaAt (.app (.lam (.lam (.var 1))) (.var 0)) [] (.lam (.var 0)) := by
  simp [BetaAt, subtermAt, replaceAt, contract, subst, singleSub,
    liftSub, rename]

/-- In a duplicating active redex the argument's old tag is copied twice. -/
private def duplicate : Marked :=
  .red [[]] (.app [] (.var 0) (.var 0))
    (.app [[.arg]] (.lam (.var 0)) (.var 0))
example : Marked.contract (.app [] (.var 0) (.var 0))
    (.app [[.arg]] (.lam (.var 0)) (.var 0)) =
    .app [] (.app [[.arg]] (.lam (.var 0)) (.var 0))
      (.app [[.arg]] (.lam (.var 0)) (.var 0)) := rfl
example : Marked.Step duplicate
    (.app [] (.app [[.arg]] (.lam (.var 0)) (.var 0))
      (.app [[.arg]] (.lam (.var 0)) (.var 0))) := .root _ _ _

/-- The finite-developments descent has no scope or environment-positivity assumption. -/
example (h : Marked.Step t u) (e : Nat → Nat) :
    Marked.weight e u < Marked.weight e t := h.weight_lt e

example : ¬ Lamping.AG.free (.lam (.var 0)) 0 := by decide
example : Lamping.AG.free (.lam (.var 1)) 0 := rfl

#print axioms beta_iff_betaAt
#print axioms Marked.Step.weight_lt
#print axioms Marked.no_infinite_development
#print axioms Lamping.AG.scoped_iff_free_lt
open Lamping.AG Lamping.Graph

/-- β joins ctx to body, while fan cancellation preserves the two branch names. -/
example : (Schema.beta 3).right.net.wire (.inr (.inl (.inl false))) =
    .inr (.inl (.inr true)) := rfl
example : (Schema.fanCancel 3).right.net.wire (.inr (.inl (.inl false))) =
    .inr (.inl (.inr false)) := rfl
example : (Schema.fanCancel 3).right.net.wire (.inr (.inl (.inl false))) ≠
    .inr (.inl (.inr true)) := by intro h; cases h

example : ¬ (2 < 2) := by decide
example : (unaryRight .cro .app 1 2).label (.inl ()) = label .app 1 := rfl
example : (unaryRight .cro .app 1 2).label (.inr false) = label .cro 1 := rfl
example : (fanRight .lam 1 4).label (.inl false) = label .lam 4 := rfl
example : (fanRight .lam 1 4).wire (.inl ⟨.inl true, .inr false⟩) =
    .inl ⟨.inr false, .inr true⟩ := rfl

#print axioms Site.reduce_pairing
#print axioms Site.reduce_boundary
/-- Only the outer redex is selected; the copied argument redex remains passive
    and is still tracked under its original name. -/
private def oldArgument : Term :=
  .app (.lam (.app (.var 0) (.var 0))) (.app (.lam (.var 0)) (.var 0))
example : Marked.tracePositions [.arg] (Marked.dev (Marked.mark [[]] oldArgument)) =
    [[.fn], [.arg]] := by decide
example : Marked.activePositions (Marked.dev (Marked.mark [[]] oldArgument)) = [] := by decide
example : redexPositions (Marked.dev (Marked.mark [[]] oldArgument)).erase =
    [[.fn], [.arg]] := by decide
example : Marked.tracePositions [] (Marked.dev (Marked.mark [[]] oldArgument)) = [] := by decide

example (h : Marked.Complete (Marked.mark F t) u)
    (k : Marked.Complete (Marked.mark F t) v) (r : Path) :
    u.erase = v.erase ∧ Marked.tracePositions r u = Marked.tracePositions r v :=
  ⟨Marked.complete_term_independent h k, Marked.complete_residual_independent h k r⟩

#print axioms Marked.dev_subst
#print axioms Marked.complete_exists
#print axioms Marked.complete_unique
#print axioms Marked.lift_betaAt
#print axioms Marked.tracePositions_sound
#print axioms Marked.complete_residual_independent
/-- Constructor-level translation checks on actual recursively composed nets. -/
example : (encode 5 (.lam (.var 0))).net.label (.inl ()) = label .lam 5 := rfl
example : (encode 5 (.lam (.var 0))).net.label (.inr ()) = label .cro 5 := rfl
example : (encode 5 (.lam (.lam (.var 0)))).net.label (.inl (.inr ())) = garbage := rfl
example : (encode 5 (.app (.var 0) (.var 0))).net.label (.inr (.inl ())) = label .cro 5 := rfl
example : (encode 5 (.app (.var 0) (.var 0))).net.label (.inr (.inr ())) = label .cro 6 := rfl
example : (encode 5 (.app (.var 0) (.var 0))).net.label
    (.inl (.inr (.inl ⟨0, rfl⟩))) = label .bra 5 := rfl
example : (encode 5 (.app (.var 0) (.var 0))).net.label
    (.inl (.inr (.inr ⟨⟨0, rfl⟩, rfl⟩))) = label .fan 5 := rfl
/-- The parameter-only input still receives a bracket. -/
example : (encode 5 (.app (.lam (.var 0)) (.var 0))).net.label
    (.inl (.inr (.inl ⟨0, rfl⟩))) = label .bra 5 := rfl

#print axioms encode_pairing
#print axioms closed_boundary_unique
/-- Arbitrary β histories can contract a newly created, unnamed redex. -/
private def createsThenContracts : Term :=
  .app (.lam (.app (.var 0) (.var 1))) (.lam (.var 0))
example : Marked.History [[], []] (Marked.mark [[]] createsThenContracts) (.var 0) :=
  .cons (.redRoot _ _ _) (.cons (.appRoot _ _ _) (.nil _))

example (h : Betas t u) : ∃ ps v,
    Marked.History ps (Marked.mark F t) v ∧ v.erase = u :=
  Marked.lift_betas h _ (Marked.erase_mark F t)

#print axioms Marked.active_mark
#print axioms Marked.trace_mark
#print axioms Marked.lift_general_betaAt
#print axioms Marked.lift_betas
#print axioms Marked.History.deterministic
#print axioms Marked.residual_composition
/-- The source is literally the recursive encoding, transported by a proved Bij. -/
example : actualBetaSite.net.wire = identityAppNet.wire.rename betaEncodingEnds := rfl
example : actualContinuationSite.net.wire = actualBetaReduced.wire.rename continuationEnds := rfl
example : actualBetaReduced.label (.inl (.inr (.inl ()))) = label .lam 1 := rfl
example : actualControlReduced.label (.inr (.inl ())) = label .lam 0 := rfl
example : actualControlReduced.label (.inr (.inr false)) = label .cro 0 := rfl
example (e) : actualControlReduced.wire (actualControlReduced.wire e) = e :=
  actualControlReduced.wire.involutive e

#print axioms PathSite.closed
#print axioms PathSite.reduce_pairing
#print axioms actualBetaSite
#print axioms actualContinuationSite
/-- The selected names remain exactly active redex occurrences after arbitrary transport. -/
example (h : Marked.History ps (Marked.mark F t) u) (p : Path) :
    p ∈ Marked.activePositions u ↔ ∃ r, r ∈ F ∧ p ∈ Marked.tracePositions r u :=
  Marked.active_iff_selected_trace (h.selected (Marked.selected_mark F t)) p

#print axioms Marked.Selected.subst
#print axioms Marked.History.selected
#print axioms Marked.selected_mark
#print axioms Marked.active_iff_selected_trace
/-- The final acceptance statements use only real contractions at old residuals,
    and completion only says that no selected old residual remains. -/
example (F : List Path) (t : Term) :
    ∃ ps u, Marked.CompleteOldDevelopment F t ps u := Marked.completeOld_exists F t
example (h : Marked.CompleteOldDevelopment F t ps u)
    (k : Marked.CompleteOldDevelopment F t qs v) (r : RedexOcc t) :
    u.erase = v.erase ∧ Marked.tracePositions r.val u = Marked.tracePositions r.val v :=
  Marked.completeOld_independent h k r
example (F : List Path) (t : Term) :
    ¬ ∃ f : Nat → Marked, f 0 = Marked.mark F t ∧
      ∀ n, ∃ p, Marked.ReductionAt p (f n) (f (n+1)) ∧
        p ∈ Marked.setResidualPositions F (f n) := Marked.no_infinite_relativeOld F t

#print axioms Marked.relativeOld_iff_relative
#print axioms Marked.normal_iff_selected_residual_empty
#print axioms Marked.completeOld_exists
#print axioms Marked.completeOld_independent
#print axioms Marked.no_infinite_relativeOld
end Lamping.Checks.Phase3Review









