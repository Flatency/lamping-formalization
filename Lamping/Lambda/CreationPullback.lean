import Lamping.Lambda.CreationIntersection
namespace Lamping.Lambda

/-- The reverse-square ancestor can be chosen to map to the specified two
 middle occurrences themselves, using non-merging of old redex identities. -/
theorem creation_predecessor_pullback (R : BetaAt t p u) (S : BetaAt t q v)
    (distinct : p ≠ q)
    (afterR : ParallelStep ((singleContraction R).residualSet [q]) u w)
    (afterS : ParallelStep ((singleContraction S).residualSet [p]) v w)
    (T1 : RedexOcc u) (T2 : RedexOcc v) (T : RedexOcc w)
    (h1 : afterR.derivation.Residual T1 T) (h2 : afterS.derivation.Residual T2 T) :
    ∃ T0 : RedexOcc t,
      (singleContraction R).derivation.Residual T0 T1 ∧
      (singleContraction S).derivation.Residual T0 T2 := by
  obtain ⟨r, hr, hs⟩ := creation_common_ancestor R S distinct afterR afterS T1 T2 T h1 h2
  obtain ⟨r1, first1, tail1⟩ := (Derivation.residual_append _ _ r T).mp hr
  obtain ⟨r2, first2, tail2⟩ := (Derivation.residual_append _ _ r T).mp hs
  have eq1 := afterR.derivation.residual_unique_source r1 T1 T tail1 h1
  have eq2 := afterS.derivation.residual_unique_source r2 T2 T tail2 h2
  cases eq1
  cases eq2
  exact ⟨r, first1, first2⟩
end Lamping.Lambda
