import Lamping.Lambda.ContextualCreationSeparation
import Lamping.Lambda.ResidualOrigins
namespace Lamping.Lambda

/-- Exercise5.2.6 in its two-arm form: the same genuine source occurrence
is an ancestor along both actual developments of the square. -/
theorem creation_common_ancestor (hR : BetaAt t p u) (hS : BetaAt t q v)
    (distinct : p ≠ q)
    (afterR : ParallelStep ((singleContraction hR).residualSet [q]) u w)
    (afterS : ParallelStep ((singleContraction hS).residualSet [p]) v w)
    (T1 : RedexOcc u) (T2 : RedexOcc v) (T : RedexOcc w)
    (h1 : afterR.derivation.Residual T1 T) (h2 : afterS.derivation.Residual T2 T) :
    ∃ T0 : RedexOcc t,
      ((singleContraction hR).derivation.append afterR.derivation).Residual T0 T ∧
      ((singleContraction hS).derivation.append afterS.derivation).Residual T0 T := by
  obtain ⟨r,hr⟩ := creation_separation hR hS distinct afterR afterS T1 T2 T h1 h2
  let sq : ParallelMovesSquare [p] [q] t u v w :=
    ⟨singleContraction hR,singleContraction hS,afterR,afterS⟩
  exact ⟨r,hr,(sq.residual r T).mp hr⟩

/-- The intersection of the two middle-redex residual images is exactly
the image of initial redexes. Creation separation supplies the reverse
inclusion; forward parallel moves alone only give the forward inclusion. -/
theorem creation_residual_intersection (hR : BetaAt t p u) (hS : BetaAt t q v)
    (distinct : p ≠ q)
    (afterR : ParallelStep ((singleContraction hR).residualSet [q]) u w)
    (afterS : ParallelStep ((singleContraction hS).residualSet [p]) v w)
    (T : RedexOcc w) :
    ((∃ T1 : RedexOcc u, afterR.derivation.Residual T1 T) ∧
      (∃ T2 : RedexOcc v, afterS.derivation.Residual T2 T)) ↔
    ∃ T0 : RedexOcc t,
      ((singleContraction hR).derivation.append afterR.derivation).Residual T0 T := by
  constructor
  · rintro ⟨⟨T1,h1⟩,⟨T2,h2⟩⟩
    exact creation_separation hR hS distinct afterR afterS T1 T2 T h1 h2
  · rintro ⟨T0,h⟩
    let sq : ParallelMovesSquare [p] [q] t u v w :=
      ⟨singleContraction hR,singleContraction hS,afterR,afterS⟩
    obtain ⟨T1,_,h1⟩ := (Derivation.residual_append _ _ T0 T).mp h
    obtain ⟨T2,_,h2⟩ := (Derivation.residual_append _ _ T0 T).mp ((sq.residual T0 T).mp h)
    exact ⟨⟨T1,h1⟩,⟨T2,h2⟩⟩

/-- Initial ancestry in the intersection is unique, using the independently
proved non-merging of old redex identities along arbitrary histories. -/
theorem creation_common_ancestor_unique (hR : BetaAt t p u) (hS : BetaAt t q v)
    (distinct : p ≠ q)
    (afterR : ParallelStep ((singleContraction hR).residualSet [q]) u w)
    (afterS : ParallelStep ((singleContraction hS).residualSet [p]) v w)
    (T1 : RedexOcc u) (T2 : RedexOcc v) (T : RedexOcc w)
    (h1 : afterR.derivation.Residual T1 T) (h2 : afterS.derivation.Residual T2 T) :
    ∃ T0 : RedexOcc t,
      (((singleContraction hR).derivation.append afterR.derivation).Residual T0 T ∧
        ((singleContraction hS).derivation.append afterS.derivation).Residual T0 T) ∧
      ∀ S0 : RedexOcc t,
        (((singleContraction hR).derivation.append afterR.derivation).Residual S0 T ∧
          ((singleContraction hS).derivation.append afterS.derivation).Residual S0 T) → S0=T0 := by
  obtain ⟨r,hr⟩ := creation_common_ancestor hR hS distinct afterR afterS T1 T2 T h1 h2
  exact ⟨r,hr,fun s hs => Derivation.residual_unique_source _ s r T hs.1 hr.1⟩

end Lamping.Lambda
