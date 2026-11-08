import Lamping.Lambda.InitialFamilies
import Lamping.Lambda.ExtractionContexts
import Lamping.Lambda.StandardizationFactorization
import Lamping.Lambda.OrdinarySplits
namespace Lamping.Lambda
/-- Repeated genuine rule (i) removes every history step before an initial
redex residual. No standardness or confluence assumption is needed. -/
theorem Atomic.extract_initial_residual {ρ : ParallelHistory t u} (atomic : Atomic ρ)
    (initial : RedexOcc t) (last : BetaAt u p v)
    (residual : ρ.derivation.Residual initial ⟨p,last.redex⟩) (initialStep : BetaAt t initial.val w) :
    Extraction (.of (ρ.append (.single (singleContraction last))) (atomic.append (.single last)))
      (.of (.single (singleContraction initialStep)) (.single initialStep)) := by
  induction atomic generalizing p v w with
  | nil t =>
    have same := congrArg Subtype.val ((Derivation.residual_nil initial ⟨p,last.redex⟩).mp residual)
    have runEq : ExtractionRun.of ((ParallelHistory.nil t).append (.single (singleContraction last)))
        ((Atomic.nil t).append (.single last)) = .of (.single (singleContraction initialStep)) (.single initialStep) := by
      apply ExtractionRun.ext_paths
      change [p]=[initial.val]
      rw [same]
    rw [runEq]
    exact .refl _
  | @cons t q mid u tail head tailAtomic ih =>
    change (head |> singleContraction).derivation.append tail.derivation |>.Residual initial ⟨p,last.redex⟩ at residual
    obtain ⟨middle,first,rest⟩ := (Derivation.residual_append _ _ initial ⟨p,last.redex⟩).mp residual
    obtain ⟨target,middleStep⟩ := middle.contract_exists
    have removedTail := (ih middle last rest middleStep).prepend (.single (singleContraction head)) (.single head)
    have removedHead := Extraction.single (ExtractionStep.residual (.nil t) (.nil t) head middleStep initialStep first)
    exact .trans (by simpa only [ExtractionRun.prepend,ExtractionRun.of,ParallelHistory.single,ParallelHistory.append] using removedTail) removedHead

/-- AG5.2.8 for the actual Copy relation and arbitrary ordinary target
representation. The original singleton is recovered by real extraction. -/
theorem Copy.initial_extraction (initial : RedexOcc m) (b : RedexWithHistory m)
    (copy : Copy ⟨m,.nil m,initial⟩ b) (represented : RunRepresents r b)
    (initialStep : BetaAt m initial.val w) :
    Extraction r (.of (.single (singleContraction initialStep)) (.single initialStep)) := by
  have residual : b.history.derivation.Residual initial b.redex :=
    (copy.initial_residual initial).mp ((Derivation.residual_nil initial initial).mpr rfl)
  obtain ⟨last,atomic,history⟩ := represented
  have sourceEq : r=.of (b.history.append (.single (singleContraction last))) (atomic.append (.single last)) := by
    apply ExtractionRun.ext_paths
    change r.history.derivation.paths=_
    rw [history]
    rfl
  rw [sourceEq]
  exact atomic.extract_initial_residual initial last residual initialStep
end Lamping.Lambda
