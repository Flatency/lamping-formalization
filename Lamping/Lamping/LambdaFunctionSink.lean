import Lamping.Lambda.SelectedDevelopmentRoutes
import Lamping.Lambda.LabelBoundaryAtoms
namespace Lamping.Lambda.Labelled

/-- A lambda whose original incoming edge is a function edge remains a
sink for outer source routes. Over/under jumps cannot enter an appFn port.
The exact original edge, rather than its physical endpoint alone, is used. -/
theorem SourceRoute.function_lambda_sink
    {original : LTerm} (initial : INIT original) {appId alpha : Label}
    (functionEdge : (⟨alpha,.appFn appId,.lamContext alpha⟩ : SourceEdge)∈sourceEdges [] .external original)
    {start stamp finish} (route : SourceRoute (sourceEdges [] .external original) start stamp finish)
    (atLambda : finish=.lamContext alpha) : start=.appFn appId ∧stamp=alpha := by
  induction route with
  | atom member atomic =>
    have sameAtom := sourceEdges_to_lam original member atLambda
    have same := sourceEdges_unique initial member functionEdge sameAtom
    cases same
    exact ⟨rfl,atomic.symm⟩
  | over _left _middle _right _hl _hm hr =>
    have impossible := (hr atLambda).1
    cases impossible
  | under _left _middle _right _hl _hm hr =>
    have impossible := (hr atLambda).1
    cases impossible

theorem SelectedSourceRoute.function_lambda_sink
    {original : LTerm} (initial : INIT original) {appId alpha : Label}
    (functionEdge : (⟨alpha,.appFn appId,.lamContext alpha⟩ : SourceEdge)∈sourceEdges [] .external original)
    {allowed start stamp} (route : SelectedSourceRoute (sourceEdges [] .external original)
      allowed start stamp (.lamContext alpha)) : start=.appFn appId ∧stamp=alpha :=
  route.forget.function_lambda_sink initial functionEdge rfl

end Lamping.Lambda.Labelled
