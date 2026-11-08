import Lamping.Lambda.CreationPullback
import Lamping.Lambda.SingletonProjectionRow
import Lamping.Lambda.ResidualExtractionPeak
import Lamping.Lambda.ExtractionContexts
import Lamping.Lambda.StepProjectionHead
namespace Lamping.Lambda

private theorem redex_contract_exists (r : RedexOcc t) : ∃ u, BetaAt t r.val u := by
  obtain ⟨v, hv, hr⟩ := r.property
  cases v with
  | var => cases hr
  | lam => cases hr
  | app f a => cases f with
    | var => cases hr
    | app => cases hr
    | lam b =>
      have root : BetaAt (.app (.lam b) a) [] (contract b a) := ⟨b, a, rfl, rfl⟩
      obtain ⟨u, hu, _, _⟩ := root.prefix_lift hv
      exact ⟨u, by simpa only [List.append_nil] using hu⟩

/-- The actual predecessor and its singleton projection row in LEV80 (3,1).
 Retaining this data allows the core to be inserted into a longer row. -/
theorem function_residual_pullback
    (R : BetaAt t p u) (S : BetaAt u s v) (T : BetaAt v z w)
    (S' : BetaAt t s' v') (T' : BetaAt v' z' w')
    {last : ParallelStep F w' w}
    (row : StepProjection (singleContraction R)
      (.cons (singleContraction S') (.single (singleContraction T')))
      (.cons (singleContraction S) (.single (singleContraction T))) last)
    (inside : Internal (p ++ [.fn])
      (.cons (singleContraction S') (.single (singleContraction T'))))
    (V : BetaAt u a x)
    (predecessor : (singleContraction S).derivation.Residual ⟨a, V.redex⟩ ⟨z, T.redex⟩) :
    ∃ (a' : Path) (target : Term) (original : BetaAt t a' target)
      (G : List Path) (vertical : ParallelStep G target x),
      (singleContraction S').derivation.Residual ⟨a', original.redex⟩ ⟨z', T'.redex⟩ ∧
      Internal (p ++ [.fn]) (.single (singleContraction original)) ∧
      StepProjection (singleContraction R) (.single (singleContraction original))
        (.single (singleContraction V)) vertical := by
  have inS : ∃ q, s' = (p ++ [.fn]) ++ q := inside s' (by change s' ∈ [s', z']; simp)
  have inT : ∃ q, z' = (p ++ [.fn]) ++ q := inside z' (by change z' ∈ [s', z']; simp)
  have distinct : p ≠ s' := by
    intro he
    obtain ⟨q, hq⟩ := inS
    rw [← he] at hq
    have len := congrArg List.length hq
    simp only [List.length_append, List.length_singleton] at len
    omega
  obtain ⟨sq, hfirst, htop, _, hside, remaining⟩ := row.head_square
  cases sq with
  | mk first top side vertical =>
    cases hfirst
    cases htop
    have back := remaining.singleton_residual T' T
    have pred : side.derivation.Residual ⟨a, V.redex⟩ ⟨z, T.redex⟩ := by
      rw [hside]
      exact predecessor
    obtain ⟨initial, throughR, throughS⟩ := creation_predecessor_pullback R S' distinct
      side vertical ⟨a, V.redex⟩ ⟨z', T'.redex⟩ ⟨z, T.redex⟩ pred back
    have inInitial : ∃ q, initial.val = (p ++ [.fn]) ++ q := by
      classical
      by_cases hi : ∃ q, initial.val = (p ++ [.fn]) ++ q
      · exact hi
      · obtain ⟨q, hq⟩ := inS
        have paths : (singleContraction S').derivation.paths = [q].map (fun q => (p ++ [.fn]) ++ q) := by
          change [s'] = _
          simp only [List.map_cons, List.map_nil, hq]
        have he := (singleContraction S').derivation.prefix_residual_outside_source paths
          initial ⟨z', T'.redex⟩ hi throughS
        obtain ⟨q', hq'⟩ := inT
        exact False.elim (hi ⟨q', he.trans hq'⟩)
    obtain ⟨bodyPath, _, selection⟩ := R.function_residualSet_singleton initial inInitial
    have member : a ∈ (singleContraction R).residualSet [initial.val] := by
      exact (Marked.mem_setResidualPositions _ _ _).mpr
        ⟨initial.val, List.mem_singleton_self _,
          ((singleContraction R).residual_iff initial ⟨a, V.redex⟩).mp throughR⟩
    rw [selection] at member
    have name := List.mem_singleton.mp member
    have selected : (singleContraction R).residualSet [initial.val] = [a] := by
      rw [selection, name]
    obtain ⟨target, original⟩ := redex_contract_exists initial
    obtain ⟨G, vertical, projected⟩ := singleton_projection_row R original V selected
    refine ⟨initial.val, target, original, G, vertical, throughS, ?_, projected⟩
    intro q hq
    change q ∈ [initial.val] at hq
    cases List.mem_singleton.mp hq
    exact inInitial

/-- LEV80 critical case (3,1) for the actual three-contraction core. The
 function-part deletion and final residual deletion join in one step each. -/
theorem extraction_function_residual_peak
    (R : BetaAt t p u) (S : BetaAt u s v) (T : BetaAt v z w)
    (S' : BetaAt t s' v') (T' : BetaAt v' z' w')
    {last : ParallelStep F w' w}
    (row : StepProjection (singleContraction R)
      (.cons (singleContraction S') (.single (singleContraction T')))
      (.cons (singleContraction S) (.single (singleContraction T))) last)
    (inside : Internal (p ++ [.fn])
      (.cons (singleContraction S') (.single (singleContraction T'))))
    (V : BetaAt u a x)
    (predecessor : (singleContraction S).derivation.Residual ⟨a, V.redex⟩ ⟨z, T.redex⟩) :
    ExtractionJoin
      (.of (.cons (singleContraction S') (.single (singleContraction T')))
        (.cons S' (.single T')))
      (.of (.cons (singleContraction R) (.single (singleContraction V)))
        (.cons R (.single V))) := by
  obtain ⟨a', target, original, G, vertical, residual, internal, projected⟩ :=
    function_residual_pullback R S T S' T' row inside V predecessor
  refine ⟨.of (.single (singleContraction original)) (.single original),
    Extraction.single ?_, Extraction.single ?_⟩
  · exact ExtractionStep.residual (.nil t) (.nil t) S' T' original residual
  · exact ExtractionStep.functionPart (.nil t) (.nil t) R _ (.single original)
      _ (.single V) vertical projected (by change 0 < 1; omega) internal
end Lamping.Lambda
