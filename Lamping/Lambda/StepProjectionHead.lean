import Lamping.Lambda.DerivationProjection
namespace Lamping.Lambda

/-- Invert a real row at its first tile before substituting concrete
singleton implementations. All four sides retain their actual schedules. -/
theorem StepProjection.head_square
    {first : ParallelStep F t u} {top : ParallelStep H t v}
    {bottom : ParallelStep K u w} {rest : ParallelHistory v x}
    {rest' : ParallelHistory w y} {last : ParallelStep L x y}
    (row : StepProjection first (.cons top rest) (.cons bottom rest') last) :
    ∃ sq : ParallelMovesSquare F H t u v w,
      sq.first=first ∧ sq.second=top ∧ HEq sq.afterFirst bottom ∧
      sq.afterFirst.derivation=bottom.derivation ∧
      StepProjection sq.afterSecond rest rest' last := by
  cases row with
  | cons sq tail => exact ⟨sq,rfl,rfl,HEq.rfl,rfl,tail⟩

end Lamping.Lambda
