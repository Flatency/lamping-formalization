import Lamping.Lambda.ExtractionFunctionResidualPeak
import Lamping.Lambda.ExtractionRowSplits
import Lamping.Lambda.ProjectionSingletonSelection
namespace Lamping.Lambda

/-- LEV80 (3,1) after an arbitrary actual row prefix. The retained vertical
 singleton is the same occurrence p, not a freely chosen common ancestor. -/
theorem extraction_function_residual_prefixed_peak
    (R : BetaAt t p u) (R' : BetaAt a p b)
    (pre : ParallelHistory t a) (hpre : Atomic pre)
    (bottom : ParallelHistory u b) (hbottom : Atomic bottom)
    (prefixRow : StepProjection (singleContraction R) pre bottom (singleContraction R'))
    (S : BetaAt b s v) (T : BetaAt v z w)
    (S' : BetaAt a s' v') (T' : BetaAt v' z' w')
    {last : ParallelStep F w' w}
    (tailRow : StepProjection (singleContraction R')
      (.cons (singleContraction S') (.single (singleContraction T')))
      (.cons (singleContraction S) (.single (singleContraction T))) last)
    (inside : Internal (p ++ [.fn])
      (pre.append (.cons (singleContraction S') (.single (singleContraction T')))))
    (V : BetaAt b q x)
    (predecessor : (singleContraction S).derivation.Residual ⟨q, V.redex⟩ ⟨z, T.redex⟩) :
    ExtractionJoin
      (.of (pre.append (.cons (singleContraction S') (.single (singleContraction T'))))
        (hpre.append (.cons S' (.single T'))))
      (.of (.cons (singleContraction R) (bottom.append (.single (singleContraction V))))
        (.cons R (hbottom.append (.single V)))) := by
  obtain ⟨preInside, tailInside⟩ := (Internal.append_iff _ _).mp inside
  obtain ⟨q', target, original, G, vertical, residual, originalInside, projected⟩ :=
    function_residual_pullback R' S T S' T' tailRow tailInside V predecessor
  let common := ExtractionRun.of (pre.append (.single (singleContraction original)))
    (hpre.append (.single original))
  refine ⟨common, Extraction.single ?_, Extraction.single ?_⟩
  · simpa only [ParallelHistory.append_assoc] using
      (ExtractionStep.residual pre hpre S' T' original residual)
  · exact ExtractionStep.functionPart (.nil t) (.nil t) R _
      (hpre.append (.single original)) _ (hbottom.append (.single V)) vertical
      (prefixRow.append projected)
      (by rw [ParallelHistory.length_append]; change 0 < pre.length + 1; omega)
      ((Internal.append_iff _ _).mpr ⟨preInside, originalInside⟩)

/-- The (3,1) critical overlap with an arbitrary ordinary middle history.
 The given full row is cut at that history's actual end, and its retained
 singleton is reconstructed, so no normalized intermediate row is assumed. -/
theorem extraction_function_residual_long_peak
    (R : BetaAt t p u) (bottom : ParallelHistory u b) (hb : Atomic bottom)
    (S : BetaAt b s v) (T : BetaAt v z w)
    (σ : ParallelHistory t w') (ha : Atomic σ) {last : ParallelStep F w' w}
    (row : StepProjection (singleContraction R) σ
      (bottom.append (.cons (singleContraction S) (.single (singleContraction T)))) last)
    (inside : Internal (p ++ [.fn]) σ)
    (V : BetaAt b q x)
    (predecessor : (singleContraction S).derivation.Residual ⟨q, V.redex⟩ ⟨z, T.redex⟩) :
    ExtractionJoin (.of σ ha)
      (.of (.cons (singleContraction R) (bottom.append (.single (singleContraction V))))
        (.cons R (hb.append (.single V)))) := by
  obtain ⟨a, K, pre, post, vertical, hp, hq, he, row1, row2⟩ :=
    row.split_bottom bottom (.cons (singleContraction S) (.single (singleContraction T)))
      ha hb (.cons S (.single T))
  have parts := (Internal.append_iff pre post).mp (he ▸ inside)
  have outside : ¬ ∃ q, p = (p ++ [.fn]) ++ q := by
    rintro ⟨q, hq⟩
    have len := congrArg List.length hq
    simp only [List.length_append, List.length_singleton] at len
    omega
  have selected : K = [p] := row1.final_selection_singleton rfl ⟨p, R.redex⟩ rfl hp parts.1 outside
  subst K
  have actual := (row1.final_vertical_singleton parts.1 outside).2
  obtain ⟨R', verticalEq⟩ := vertical.eq_single_contraction ⟨p, actual.redex⟩ rfl
  cases verticalEq
  have length : post.length = 2 := by
    have len := row2.length
    change 2 = post.length at len
    exact len.symm
  obtain ⟨v', s', z', S', T', postEq⟩ := hq.two_contractions length
  cases postEq
  have joined := extraction_function_residual_prefixed_peak R R' pre hp bottom hb row1
    S T S' T' row2 (he ▸ inside) V predecessor
  simpa only [← he] using joined

end Lamping.Lambda
