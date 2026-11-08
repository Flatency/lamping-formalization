import Lamping.Lambda.StandardizationProtection
import Lamping.Lambda.ProjectionSelections
import Lamping.Lambda.AtomicProjection
namespace Lamping.Lambda

/-- Pulling a protected left beta through a right-hand history retains the
actual projection row, including its chosen residual schedules. -/
theorem RightHistory.pull_projection {ρ : ParallelHistory t u} {cut : Path}
    (right : RightHistory cut ρ) (s : RedexOcc t) (atCut : s.val=cut)
    (later : BetaAt u cut w) :
    ∃ (v : Term) (source : BetaAt t cut v) (tail : ParallelHistory v w)
      (K : List Path) (last : ParallelStep K u w),
      StepProjection (singleContraction source) ρ tail last ∧
      tail.length=ρ.length ∧ last.paths=[cut] ∧
      PermEq (.single last) (.single (singleContraction later)) := by
  obtain ⟨v,source⟩ := s.contract_exists
  have sourceCut : BetaAt t cut v := by rw [←atCut]; exact source
  obtain ⟨z,K,tail,last,row⟩ := StepProjection.exists_projection (singleContraction sourceCut) ρ
  have valid : ∀p∈[cut],∃term,subtermAt t p=some term ∧ IsRedex term := by
    intro p hp; cases List.mem_singleton.mp hp; exact sourceCut.redex
  have pathsRight : ∀p∈ρ.derivation.paths,LeftOf s.val p := by
    rw [atCut]
    exact right.paths_right
  have members (q : RedexOcc u) : q.val∈K ↔q.val=cut := by
    rw [row.final_selection valid q]
    constructor
    · rintro ⟨r,selected,residual⟩
      have same : r=s := Subtype.ext ((List.mem_singleton.mp selected).trans atCut.symm)
      subst r
      exact ((ρ.derivation.left_fixed s pathsRight q).mp residual).trans atCut
    · intro position
      exact ⟨s,(List.mem_singleton.mpr atCut),
        (ρ.derivation.left_fixed s pathsRight q).mpr (position.trans atCut.symm)⟩
  have sameSelection : ∀p,p∈K ↔p∈[cut] := by
    intro p
    constructor
    · intro hp
      let q : RedexOcc u := ⟨p,row.final_selection_valid valid p hp⟩
      exact List.mem_singleton.mpr ((members q).mp hp)
    · intro hp
      have position := List.mem_singleton.mp hp
      have red : ∃term,subtermAt u p=some term ∧ IsRedex term := by rw [position]; exact later.redex
      exact (members ⟨p,red⟩).mpr position
  have endpoint : z=w := last.endpoint_selection (singleContraction later) sameSelection
  cases endpoint
  have singlePaths := (last.reindex [cut] sameSelection).singleton_paths
    ⟨cut,later.redex⟩ rfl
  exact ⟨v,sourceCut,tail,K,last,row,row.length,singlePaths,PermEq.selection last (singleContraction later) sameSelection⟩

end Lamping.Lambda
