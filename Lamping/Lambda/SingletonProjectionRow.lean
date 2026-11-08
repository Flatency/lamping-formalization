import Lamping.Lambda.AtomicProjection
namespace Lamping.Lambda

/-- A prescribed single beta which contracts the entire literal residual
 singleton is the actual horizontal side of a genuine one-tile row. -/
theorem singleton_projection_row (R : BetaAt t p u) (original : BetaAt t r v)
    (projected : BetaAt u q w)
    (selection : (singleContraction R).residualSet [r] = [q]) :
    ∃ F, ∃ last : ParallelStep F v w,
      StepProjection (singleContraction R) (.single (singleContraction original))
        (.single (singleContraction projected)) last := by
  obtain ⟨z, a, b, _⟩ := parallel_moves (singleContraction R) (singleContraction original)
  have endpoint : z = w := a.endpoint_selection (singleContraction projected) (by intro s; rw [selection])
  subst z
  have row : StepProjection (singleContraction R) (.single (singleContraction original)) (.single a) b :=
    .cons ⟨singleContraction R, singleContraction original, a, b⟩ (.nil b)
  have he : ParallelHistory.single a = .single (singleContraction projected) := by
    generalize hs : (singleContraction R).residualSet [r] = G at a
    have hG : G = [q] := hs.symm.trans selection
    cases hG
    obtain ⟨β, hb⟩ := a.eq_single_contraction ⟨q, projected.redex⟩ rfl
    rw [hb]
  rw [he] at row
  exact ⟨_, b, row⟩
end Lamping.Lambda
