import Lamping.Lambda.StandardPrefixes
import Lamping.Lambda.OrdinarySplits
import Lamping.Lambda.ExtractionContexts
import Lamping.Lambda.StandardizationExistence
namespace Lamping.Lambda

/-- A nonempty ordinary prefix cannot carry any old redex to the final
point of an extraction normal run: rule (i) would delete its last step. -/
theorem normal_no_old_last (ρ : ParallelHistory m t) (ha : Atomic ρ)
    (positive : 0<ρ.length) (S : BetaAt t p u)
    (normal : ExtractionNormal (.of (ρ.append (.single (singleContraction S))) (ha.append (.single S))))
    (r : RedexOcc m) : ¬ρ.derivation.Residual r ⟨p,S.redex⟩ := by
  intro residual
  obtain ⟨v,q,pre,R,hpre,shape⟩ := ha.last positive
  rw [shape,ParallelHistory.derivation_append] at residual
  obtain ⟨old,_,oldResidual⟩ := (Derivation.residual_append _ _ r ⟨p,S.redex⟩).mp residual
  obtain ⟨target,original⟩ := old.contract_exists
  let source : ExtractionRun m := .of
    ((pre.append (.single (singleContraction R))).append (.single (singleContraction S)))
    ((hpre.append (.single R)).append (.single S))
  have sourceEq : source = .of (ρ.append (.single (singleContraction S))) (ha.append (.single S)) := by
    apply ExtractionRun.ext_paths
    change _ = (ρ.append (.single (singleContraction S))).derivation.paths
    rw [shape]
    rfl
  have step : ExtractionStep source
      (.of (pre.append (.single (singleContraction original))) (hpre.append (.single original))) :=
    .residual pre hpre R S original oldResidual
  exact normal ⟨_,sourceEq ▸ step⟩

/-- Appending the final contraction cannot introduce a return-left witness
if its redex has no old ancestor along the given ordinary prefix. -/
theorem DoesNotReturnLeft.append_last {ρ : ParallelHistory t u} (ha : Atomic ρ)
    (h : DoesNotReturnLeft r ρ) (S : BetaAt u p v)
    (noOld : ∀ s : RedexOcc t, ¬ρ.derivation.Residual s ⟨p,S.redex⟩) :
    DoesNotReturnLeft r (ρ.append (.single (singleContraction S))) := by
  intro s before x y F pre step suffix decomposition q lo residual
  have wholeAtomic : Atomic (pre.append (.cons step suffix)) := by
    rw [←decomposition]
    exact ha.append (.single S)
  have parts := wholeAtomic.split_append (ρ:=pre) (σ:=.cons step suffix)
  have bound : pre.length≤ρ.length := by
    have lengths := congrArg ParallelHistory.length decomposition
    simp only [ParallelHistory.length_append,ParallelHistory.single,ParallelHistory.length] at lengths
    omega
  obtain ⟨bridge,hbridge,prefixEq,suffixEq⟩ :=
    parts.1.prefix_comparable ha parts.2 (.single S) decomposition.symm bound
  cases bridge with
  | nil =>
    rw [ParallelHistory.append_nil] at prefixEq
    cases prefixEq
    cases suffixEq
    have path : q.val=p := List.mem_singleton.mp lo.1
    have point : q=⟨p,S.redex⟩ := Subtype.ext path
    exact noOld s (point ▸ residual)
  | cons head rest =>
    cases suffixEq
    exact h s before pre step rest prefixEq q lo residual

/-- An extraction-normal pointed run with a standard ordinary prefix is
standard as a full run. Its last contraction is not assumed standard. -/
theorem normal_standard_append (ρ : ParallelHistory m t) (ha : Atomic ρ)
    (S : BetaAt t p u) (standard : Standard ρ)
    (normal : ExtractionNormal (.of (ρ.append (.single (singleContraction S))) (ha.append (.single S)))) :
    Standard (ρ.append (.single (singleContraction S))) := by
  induction ha generalizing p u with
  | nil => exact Standard.single_step _ ⟨p,S.redex⟩ (leftmost_singleton _)
  | @cons m q v t tail R hat ih =>
    cases standard with
    | cons h r lo noReturn restStandard =>
      have noOld := normal_no_old_last (.cons (singleContraction R) tail) (.cons R hat)
        (by change 0<1+tail.length; omega) S normal
      have restNormal : ExtractionNormal
          (.of (tail.append (.single (singleContraction S))) (hat.append (.single S))) := by
        apply ExtractionNormal.of_prepend (pre:=.single (singleContraction R)) (ha:=.single R)
        exact normal
      exact .cons (singleContraction R) r lo (DoesNotReturnLeft.append_last (.cons R hat) noReturn S noOld)
        (ih S restStandard restNormal)

/-- The source convention for standard redexes with history concerns the
prefix, whereas CanonicalRun requires the final contraction as well. -/
def PrefixStandard (r : ExtractionRun m) : Prop :=
  ∃ a : RedexWithHistory m, RunRepresents r a ∧ Standard a.history

theorem canonical_of_normal_prefix (normal : ExtractionNormal r) (standard : PrefixStandard r) :
    CanonicalRun r := by
  obtain ⟨a,⟨last,atomic,history⟩,standard⟩ := standard
  have runEq : r = .of (a.history.append (.single (singleContraction last))) (atomic.append (.single last)) := by
    apply ExtractionRun.ext_paths
    change r.history.derivation.paths = _
    rw [history]
    rfl
  rw [runEq] at normal ⊢
  refine ⟨?_,normal_standard_append a.history atomic last standard normal,normal⟩
  simp [ExtractionRun.rank,ExtractionRun.of,ParallelHistory.length_append,
    ParallelHistory.single,ParallelHistory.length]

end Lamping.Lambda
