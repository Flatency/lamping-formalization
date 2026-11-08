import Lamping.Lambda.StepProjectionHead
import Lamping.Lambda.ProjectionFamilies
import Lamping.Lambda.ResidualOrigins
import Lamping.Lambda.OrdinarySplits
namespace Lamping.Lambda

/-- Two ordinary top histories projecting to the same actual ordinary bottom
 schedule across developments of the same selection have the same paths.
 Each tile is identified by unique old origins, not by its endpoint. -/
theorem StepProjection.atomic_top_paths_unique
    {first second : ParallelStep F t u}
    {σ : ParallelHistory t v} {τ : ParallelHistory t v'} {bottom : ParallelHistory u w}
    {last : ParallelStep G v w} {last' : ParallelStep H v' w}
    (row : StepProjection first σ bottom last) (row' : StepProjection second τ bottom last')
    (ha : Atomic σ) (hb : Atomic τ) (hc : Atomic bottom) :
    σ.derivation.paths = τ.derivation.paths := by
  induction ha generalizing F u w H v' with
  | nil =>
    have zero := row.length
    cases hb with
    | nil => rfl
    | cons T hT =>
      have other := row'.length
      simp only [ParallelHistory.length] at zero other
      omega
  | @cons t p a v tail S hs ih =>
    cases hb with
    | nil =>
      have zero := row'.length
      have other := row.length
      simp only [ParallelHistory.length] at zero other
      omega
    | @cons t q a' v' tail' T ht =>
      cases hc with
      | nil =>
        have zero := row.length
        simp only [ParallelHistory.length] at zero
        omega
      | @cons u z b w rest B hrest =>
        obtain ⟨sq, hfirst, htop, _, hside, remaining⟩ := row.head_square
        obtain ⟨sq', hfirst', htop', _, hside', remaining'⟩ := row'.head_square
        cases sq with
        | mk first1 top1 side1 vertical1 =>
          cases hfirst
          cases htop
          cases sq' with
          | mk first2 top2 side2 vertical2 =>
            cases hfirst'
            cases htop'
            have oldS := first1.singleton_projection_residual ⟨p, S.redex⟩ ⟨z, B.redex⟩
              side1 (congrArg Derivation.paths hside)
            have oldT := first2.singleton_projection_residual ⟨q, T.redex⟩ ⟨z, B.redex⟩
              side2 (congrArg Derivation.paths hside')
            have same := first1.derivation.residual_unique_source ⟨p, S.redex⟩ ⟨q, T.redex⟩
              ⟨z, B.redex⟩ oldS ((first2.residual_independent first1 _ _).mp oldT)
            have path : p = q := congrArg Subtype.val same
            cases path
            have endpoint := S.unique T
            cases endpoint
            have beta : S = T := Subsingleton.elim _ _
            cases beta
            have tails := ih remaining remaining' ht hrest
            change p :: tail.derivation.paths = p :: tail'.derivation.paths
            exact congrArg (List.cons p) tails

theorem StepProjection.atomic_top_run_unique
    {first second : ParallelStep F t u}
    {σ : ParallelHistory t v} {τ : ParallelHistory t v'} {bottom : ParallelHistory u w}
    {last : ParallelStep G v w} {last' : ParallelStep H v' w}
    (row : StepProjection first σ bottom last) (row' : StepProjection second τ bottom last')
    (ha : Atomic σ) (hb : Atomic τ) (hc : Atomic bottom) :
    ExtractionRun.of σ ha = ExtractionRun.of τ hb :=
  ExtractionRun.ext_paths _ _ (row.atomic_top_paths_unique row' ha hb hc)

end Lamping.Lambda
