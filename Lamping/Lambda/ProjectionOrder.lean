import Lamping.Lambda.ProjectionUsedSources
import Lamping.Lambda.AtomicRowExistence
import Lamping.Lambda.ArgumentParallelCuts
namespace Lamping.Lambda

theorem LeftOf.prefix_append (h : LeftOf p q) (pre : Path) : LeftOf (pre++p) (pre++q) := by
  induction pre with
  | nil => exact h
  | cons s pre ih => exact .child s ih

theorem LeftOf.strip_prefix {pre : Path} (h : LeftOf (pre++p) (pre++q)) : LeftOf p q := by
  induction pre with
  | nil => exact h
  | cons s pre ih => cases h with | child _ h => exact ih h

/-- In the two non-argument extraction regions, an earlier old redex has a
unique actual image still left of the projected head contraction. -/
theorem BetaAt.region_left_image (R : BetaAt t p u) (region : ExtractionRegion p site)
    (head : RedexOcc t) (headInside : ∃ q, head.val=site++q)
    (projected : RedexOcc u) (headResidual : (singleContraction R).derivation.Residual head projected)
    (r : RedexOcc t) (inside : ∃ q, r.val=site++q) (before : LeftOf r.val head.val) :
    ∃ image : RedexOcc u, LeftOf image.val projected.val ∧
      ∀ z : RedexOcc u, (singleContraction R).derivation.Residual r z → z=image := by
  rcases region with disjoint | function
  · obtain ⟨headTail,headAt⟩ := headInside
    obtain ⟨tail,atSite⟩ := inside
    have headApart : DisjointPositions p head.val := by
      rw [headAt]; exact ((disjoint.symm.descend_left headTail).symm)
    have apart : DisjointPositions p r.val := by
      rw [atSite]; exact ((disjoint.symm.descend_left tail).symm)
    have headFixed := (R.disjoint_residual_iff head headApart projected).mp headResidual
    have selection := R.outside_residualSet_singleton r apart.1
    let image : RedexOcc u := ⟨r.val,(singleContraction R).residualSet_valid r.val (by rw [selection]; simp)⟩
    refine ⟨image,?_,?_⟩
    · change LeftOf r.val projected.val
      rw [←headFixed]; exact before
    · intro z residual
      exact Subtype.ext ((R.disjoint_residual_iff r apart z).mp residual).symm
  · have headFunction : ∃ q,head.val=(p++[.fn])++q := by simpa only [function] using headInside
    have oldFunction : ∃ q,r.val=(p++[.fn])++q := by simpa only [function] using inside
    obtain ⟨headTail,headAt,headMembers⟩ := R.function_residualSet_members head (R.function_body_position head headFunction)
    obtain ⟨tail,atBody,members⟩ := R.function_residualSet_members r (R.function_body_position r oldFunction)
    have headSelected : projected.val∈(singleContraction R).residualSet [head.val] :=
      ((singleContraction R).mem_residualSet_iff (by intro q hq; cases List.mem_singleton.mp hq; exact head.property) projected).mpr
        ⟨head,by simp,headResidual⟩
    have headTarget := (headMembers projected.val).mp headSelected
    let image : RedexOcc u := ⟨p++tail,(singleContraction R).residualSet_valid (p++tail) ((members _).mpr rfl)⟩
    refine ⟨image,?_,?_⟩
    · have localBefore : LeftOf tail headTail := by
        rw [atBody,headAt] at before
        exact before.strip_prefix
      change LeftOf (p++tail) projected.val
      rw [headTarget]
      exact localBefore.prefix_append p
    · intro z residual
      have selected : z.val∈(singleContraction R).residualSet [r.val] :=
        ((singleContraction R).mem_residualSet_iff (by intro q hq; cases List.mem_singleton.mp hq; exact r.property) z).mpr
          ⟨r,by simp,residual⟩
      exact Subtype.ext ((members z.val).mp selected)
end Lamping.Lambda
