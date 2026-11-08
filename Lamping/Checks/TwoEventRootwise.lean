import Lamping.Checks.WrappedLambdaParent
import Lamping.Checks.FunctionWrappedBodyParent
import Lamping.Lamping.PhysicalCorridorPresentation

namespace Lamping.Checks.TwoEventRootwise
open AG Graph Lambda
open FunctionWrappedReachable FunctionWrappedBodyParent WrappedLambdaParent

/-- The next root redex uses six actual departures of the existing carrier. -/
theorem next_root_corridor :
    ∃ route : TransparentCorridor croApp.site.reduce,
      route.edges = finalEdges.tail ∧
      route.first = ⟨.inl outerKept4, .inl ()⟩ ∧
      route.last = ⟨.inl copiedLambda4, .inl ()⟩ := by
  let route : TransparentCorridor croApp.site.reduce := {
    first := ⟨.inl outerKept4, .inl ()⟩
    last := ⟨.inl copiedLambda4, .inl ()⟩
    edges := finalEdges.tail
    start := rfl
    finish := by
      have inverse := congrArg croApp.site.reduce.wire final_context_finish
      simp only [Pairing.involutive] at inverse
      simpa only [finalEdges, List.tail_cons, List.getLast?_cons_cons,
        List.getLast?_singleton] using congrArg some inverse
    transparent := by
      intro e f member
      simp only [finalEdges, List.tail_cons, List.zip_cons_cons, List.zip_nil_right,
        List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with h | h | h | h | h
      · cases h
        exact ⟨.inl (.inl outerOutside4), false, final_outer, rfl⟩
      · cases h
        exact ⟨.inl (.inl contextOutside4), false, final_outer_finish, rfl⟩
      · cases h
        exact ⟨.inl (.inl bodyOutside4), true, final_context, rfl⟩
      · cases h
        exact ⟨.inl (.inl oldBodyOutside4), false, final_body, rfl⟩
      · cases h
        exact ⟨.inl (.inl controlContextOutside4), false, final_body_finish, rfl⟩ }
  exact ⟨route, rfl, rfl, rfl⟩

private theorem append_beta_corridor
    {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
    (g : Net signature N B W) (initial : ActualNet B) (schemas : List Schema)
    (trace : GraphTrace initial (ActualNet.ofNet g) schemas)
    (active passive : N) (p : Port (g.label active).sort) (q : Port (g.label passive).sort)
    (different : active ≠ passive)
    (activeLabel : g.label active = label .app 0)
    (passiveLabel : g.label passive = label .lam 0)
    (activePrincipal : HEq p (Sum.inl () : Port (.op .app)))
    (passivePrincipal : HEq q (Sum.inl () : Port (.op .lam)))
    (edges : List (Endpoint g))
    (corridor : ∃ route : TransparentCorridor g,
      route.edges = edges ∧ route.first = ⟨active, p⟩ ∧ route.last = ⟨passive, q⟩) :
    ∃ presentation : PhysicalCorridorPresentation g (.beta 0) active passive p q,
      GraphTrace initial (ActualNet.ofNet presentation.site.reduce) (schemas ++ [.beta 0]) := by
  obtain ⟨route, _edges, first, last⟩ := corridor
  obtain ⟨presentation⟩ := physical_corridor_presentation g (.beta 0) route active passive
    different activeLabel passiveLabel p q activePrincipal passivePrincipal first last
  exact ⟨presentation, trace.trans (.single presentation.graph_step)⟩

private theorem next_app_label :
    croApp.site.reduce.label (.inl outerKept4) = label .app 0 := rfl

private theorem next_lam_label :
    croApp.site.reduce.label (.inl copiedLambda4) = label .lam 0 := rfl

private theorem next_nodes_different :
    (Sum.inl outerKept4 : croApp.Kept ⊕ (Unit ⊕ Bool)) ≠ Sum.inl copiedLambda4 := by
  intro same
  have impossible : label .app 0 = label .lam 0 :=
    next_app_label.symm.trans ((congrArg croApp.site.reduce.label same).trans next_lam_label)
  cases impossible

/-- Two beta events separated by three actual standard administrative steps.
This certifies the trace, not a cross-event expanded-history splice. -/
theorem actual_two_beta_trace :
    ∃ presentation : PhysicalCorridorPresentation croApp.site.reduce (.beta 0)
      (.inl outerKept4) (.inl copiedLambda4) (.inl ()) (.inl ()),
      GraphTrace (ActualNet.initial FunctionWrappedReachable.term)
        (ActualNet.ofNet presentation.site.reduce)
        [.beta 0, .croAction .lam 0 1 (by decide),
          .croAction .cro 0 1 (by decide), .croAction .app 0 1 (by decide), .beta 0] := by
  exact append_beta_corridor croApp.site.reduce
    (ActualNet.initial FunctionWrappedReachable.term)
    [.beta 0, .croAction .lam 0 1 (by decide), .croAction .cro 0 1 (by decide),
      .croAction .app 0 1 (by decide)]
    actual_four_step_trace (.inl outerKept4) (.inl copiedLambda4) (.inl ()) (.inl ())
    next_nodes_different next_app_label next_lam_label HEq.rfl HEq.rfl finalEdges.tail
    next_root_corridor

#print axioms next_root_corridor
#print axioms actual_two_beta_trace
end Lamping.Checks.TwoEventRootwise
