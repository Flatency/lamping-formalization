import Lamping.Lambda.ExtractionNormalHead
import Lamping.Lambda.ExtractionArgumentResidualPeak
namespace Lamping.Lambda

theorem extraction_two_normal_of_fresh (R : BetaAt t p u) (S : BetaAt u q v)
    (fresh : ∀r : RedexOcc t,¬(singleContraction R).derivation.Residual r ⟨q,S.redex⟩) :
    ExtractionNormal (.of (.cons (singleContraction R) (.single (singleContraction S))) (.cons R (.single S))) := by
  rintro ⟨result,step⟩
  have root := step.root_of_normal_tail (extraction_single_normal S)
  cases root with
  | residual S A old => exact fresh ⟨_,A.redex⟩ old
  | disjoint original ho projected hp last row positive site apart inside =>
    cases ho with
    | nil => simp only [ParallelHistory.length] at positive; omega
    | cons A rest => exact fresh ⟨_,A.redex⟩ (row.head_singleton_residual A S)
  | functionPart original ho projected hp last row positive inside =>
    cases ho with
    | nil => simp only [ParallelHistory.length] at positive; omega
    | cons A rest => exact fresh ⟨_,A.redex⟩ (row.head_singleton_residual A S)
  | argumentPart copy hc original ho positive lift =>
    cases ho with
    | nil =>
      have len := lift.length hc (.nil _)
      simp only [ParallelHistory.length] at len
      omega
    | cons A rest => exact fresh ⟨_,A.redex⟩ (lift.head_residual R S A (.nil _) _)

end Lamping.Lambda
