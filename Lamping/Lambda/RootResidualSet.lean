import Lamping.Lambda.ProjectionSelections
import Lamping.Lambda.RootResidualPaths
import Lamping.Lambda.TraceNoDup
namespace Lamping.Lambda

theorem ParallelStep.residualSet_singleton_of_members (h : ParallelStep F t u)
    (hm : ∀ z, z ∈ h.residualSet [r] ↔ z = p) : h.residualSet [r] = [p] := by
  simp only [ParallelStep.residualSet, Marked.setResidualPositions, List.flatMap_cons,
    List.flatMap_nil, List.append_nil] at hm ⊢
  exact Marked.trace_singleton_of_members r p h.markedTarget hm

theorem single_root_trace (R : BetaAt (.app (.lam b) a) [] (contract b a)) (r : Path) :
    Marked.tracePositions r (singleContraction R).markedTarget =
      Marked.tracePositions r (Marked.contract (Marked.markAt [] b [.fn, .body])
        (Marked.markAt [] a [.arg])) := by
  have model : Marked.History [[]] (Marked.mark [] (.app (.lam b) a))
      (Marked.contract (Marked.markAt [] b [.fn, .body]) (Marked.markAt [] a [.arg])) :=
    .cons (.appRoot _ _ _) (.nil _)
  have he := (singleContraction R).tracked.deterministic model
  rw [← Marked.passive_trace r (singleContraction R).markedTarget, he]

/-- An old body redex has exactly one residual through root beta. Its old
 name cannot also occur in any substituted argument instance. -/
theorem root_body_residualSet_members
    (R : BetaAt (.app (.lam b) a) [] (contract b a)) (r : RedexOcc b) (z : Path) :
    z ∈ (singleContraction R).residualSet [[.fn, .body] ++ r.val] ↔ z = r.val := by
  change z ∈ Marked.setResidualPositions [[.fn, .body] ++ r.val] _ ↔ _
  simp only [Marked.setResidualPositions, List.flatMap_cons, List.flatMap_nil, List.append_nil]
  rw [single_root_trace R, Marked.contract_trace_iff]
  simp only [Marked.trace_markAt, Marked.erase_markAt]
  have hr := (mem_redexPositions b r.val).mpr r.property
  constructor
  · intro hz
    rcases hz with ⟨he, _⟩ | ⟨site, tail, _, _, he, _⟩
    · exact (List.append_cancel_left he).symm
    · cases he
  · intro hz
    subst z
    exact .inl ⟨rfl, hr⟩

theorem BetaAt.function_residualSet_members (R : BetaAt t p u)
    (r : RedexOcc t) (inside : ∃ q, r.val = (p ++ [.fn, .body]) ++ q) :
    ∃ q, r.val = (p ++ [.fn, .body]) ++ q ∧
      ∀ z, z ∈ (singleContraction R).residualSet [r.val] ↔ z = p ++ q := by
  obtain ⟨q, hq⟩ := inside
  obtain ⟨b, a, lookup, replace⟩ := R
  have root : BetaAt (.app (.lam b) a) [] (contract b a) := ⟨b, a, rfl, rfl⟩
  have rb : ∃ v, subtermAt b q = some v ∧ IsRedex v := by
    have hr := r.property
    rw [hq, List.append_assoc, subtermAt_append, lookup, Option.bind_some] at hr
    exact hr
  let bodyRedex : RedexOcc b := ⟨q, rb⟩
  have paths : (singleContraction ⟨b, a, lookup, replace⟩).paths =
      (singleContraction root).paths.map (fun p' => p ++ p') := by simp
  refine ⟨q, hq, ?_⟩
  intro z
  have hm := (singleContraction ⟨b, a, lookup, replace⟩).residualSet_prefix_members
    (singleContraction root) lookup paths (z := z) (r := [.fn, .body] ++ q)
  rw [hq, List.append_assoc]
  rw [hm, List.mem_map]
  constructor
  · rintro ⟨z', hz', he⟩
    have he' := (root_body_residualSet_members root bodyRedex z').mp hz'
    simpa only [he'] using he.symm
  · intro he
    exact ⟨q, (root_body_residualSet_members root bodyRedex q).mpr rfl, he.symm⟩

theorem BetaAt.function_body_position (R : BetaAt t p u) (r : RedexOcc t)
    (inside : ∃ q, r.val = (p ++ [.fn]) ++ q) :
    ∃ q, r.val = (p ++ [.fn, .body]) ++ q := by
  obtain ⟨q, hq⟩ := inside
  obtain ⟨b, a, lookup, _⟩ := R
  have function : subtermAt t (p ++ [.fn]) = some (.lam b) := by
    rw [subtermAt_append, lookup]
    rfl
  obtain ⟨v, hv, hred⟩ := r.property
  rw [hq, subtermAt_append, function, Option.bind_some] at hv
  cases q with
  | nil => simp only [subtermAt, Option.some.injEq] at hv; subst v; cases hred
  | cons e q => cases e with
    | fn => simp [subtermAt] at hv
    | arg => simp [subtermAt] at hv
    | body => exact ⟨q, by simpa only [List.append_assoc, List.cons_append, List.nil_append] using hq⟩

theorem BetaAt.function_residualSet_singleton (R : BetaAt t p u)
    (r : RedexOcc t) (inside : ∃ q, r.val = (p ++ [.fn]) ++ q) :
    ∃ q, r.val = (p ++ [.fn, .body]) ++ q ∧
      (singleContraction R).residualSet [r.val] = [p ++ q] := by
  obtain ⟨q, hq, hm⟩ := R.function_residualSet_members r (R.function_body_position r inside)
  exact ⟨q, hq, (singleContraction R).residualSet_singleton_of_members hm⟩

theorem BetaAt.outside_residualSet_singleton (h : BetaAt t p u) (r : RedexOcc t)
    (outside : ¬ ∃ q, r.val = p ++ q) : (singleContraction h).residualSet [r.val] = [r.val] := by
  have ht := (singleContraction h).tracked
  change Marked.History [p] (Marked.mark [] t) _ at ht
  cases ht with
  | cons hm hs =>
    cases hs
    have hn : ∀ q, p ++ q ∉ Marked.tracePositions r.val (Marked.mark [] t) := by
      intro q hq
      exact outside ⟨q, ((Marked.initial_residual [] t r (p ++ q)).mp hq).symm⟩
    have he := hm.trace_outside hn
    simp only [Marked.passive_trace] at he
    change Marked.setResidualPositions [r.val] _ = _
    simp only [Marked.setResidualPositions, List.flatMap_cons, List.flatMap_nil, List.append_nil]
    rw [he, Marked.initial_trace_singleton]
end Lamping.Lambda
