import Lamping.Lambda.CopyRegionExtraction
import Lamping.Lambda.SingletonProjectionRow
import Lamping.Lambda.ProjectionSingletonSelection
import Lamping.Lambda.ProjectionStepCongruence
import Lamping.Lambda.ProjectionSplits
namespace Lamping.Lambda

/-- Invert a complete disjoint ordinary row using the supplied actual bottom
program. Both the source program and the remaining actual beta are derived. -/
theorem Atomic.disjoint_row_pullback {σ : ParallelHistory u w} (ordinary : Atomic σ)
    (R : BetaAt t p u) (apart : DisjointPositions p site) (inside : Internal site σ) :
    ∃ v, ∃ source : ParallelHistory t v, ∃ remaining : BetaAt v p w,
      Atomic source ∧ source.derivation.paths=σ.derivation.paths ∧ Internal site source ∧
      StepProjection (singleContraction R) source σ (singleContraction remaining) := by
  induction ordinary generalizing t with
  | nil u => exact ⟨t,.nil t,R,.nil t,rfl,(by intro p hp; cases hp),.nil _⟩
  | @cons u q mid w tail S atomic ih =>
    have location : ∃r,q=site++r := inside q (by
      simp [ParallelHistory.derivation,Derivation.append,ParallelStep.derivation,singleContraction])
    obtain ⟨r,atSite⟩ := location
    have headApart : DisjointPositions p q := by rw [atSite]; exact (apart.symm.descend_left r).symm
    obtain ⟨ancestor,same,old⟩ := R.disjoint_initial_ancestor ⟨q,S.redex⟩ headApart
    change ancestor.val=q at same
    obtain ⟨v,original⟩ := ancestor.contract_exists
    have originalAt : BetaAt t q v := by rw [←same]; exact original
    have image : (singleContraction R).residualSet [q]=[q] :=
      (singleContraction R).apart_residualSet_singleton ⟨q,originalAt.redex⟩ (by
        intro pos hp
        have eq : pos=p := by simpa [singleContraction] using hp
        simpa [eq] using headApart.symm)
    obtain ⟨F,last,oneRow⟩ := singleton_projection_row R originalAt S image
    have originalInside : Internal site (.single (singleContraction originalAt)) := by
      intro pos hp
      have eq : pos=q := by simpa [ParallelHistory.single_derivation,ParallelStep.derivation,singleContraction] using hp
      exact ⟨r,eq.trans atSite⟩
    have outside : ¬∃s,p=site++s := apart.2
    obtain ⟨lastPaths,next⟩ := oneRow.final_vertical_singleton originalInside outside
    have selected := oneRow.final_selection_singleton rfl ⟨p,R.redex⟩ rfl (.single originalAt) originalInside outside
    have normalized := oneRow.last_congr selected lastPaths (last':=singleContraction next)
    have tailInside : Internal site tail := by
      intro pos hp; exact inside pos (by simp [ParallelHistory.derivation,Derivation.append,hp])
    obtain ⟨z,source,remaining,sourceAtomic,paths,sourceInside,row⟩ := ih next tailInside
    refine ⟨z,.cons (singleContraction originalAt) source,remaining,.cons originalAt sourceAtomic,?_,?_,?_⟩
    · change q::source.derivation.paths=q::tail.derivation.paths
      rw [paths]
    · intro pos hp
      change pos∈q::source.derivation.paths at hp
      rcases List.mem_cons.mp hp with eq | hp
      · exact ⟨r,eq.trans atSite⟩
      · exact sourceInside pos hp
    · exact normalized.append row

/-- Remove a whole actual prefix outside a nonempty internal program by
successive genuine rule (ii) steps. The returned source program is constructed
by inverse disjoint tile rows and executes precisely the supplied program. -/
theorem Atomic.extract_disjoint_prefix {pre : ParallelHistory t u} (preAtomic : Atomic pre)
    (σ : ParallelHistory u w) (ordinary : Atomic σ) (inside : Internal site σ)
    (positive : 0<σ.length)
    (apart : ∀ p∈pre.derivation.paths,DisjointPositions p site) :
    ∃ v, ∃ source : ParallelHistory t v, ∃ sourceAtomic : Atomic source,
      source.derivation.paths=σ.derivation.paths ∧ Internal site source ∧
      Extraction (.of (pre.append σ) (preAtomic.append ordinary)) (.of source sourceAtomic) := by
  induction preAtomic generalizing w with
  | nil t => exact ⟨w,σ,ordinary,rfl,inside,.refl _⟩
  | @cons t p mid u tail R tailAtomic ih =>
    have tailApart : ∀ q∈tail.derivation.paths,DisjointPositions q site := by
      intro q hq; exact apart q (by simp [ParallelHistory.derivation,Derivation.append,hq])
    obtain ⟨z,middle,middleAtomic,middlePaths,middleInside,removed⟩ :=
      ih σ ordinary inside positive tailApart
    have headApart : DisjointPositions p site := apart p (by
      simp [ParallelHistory.derivation,Derivation.append,ParallelStep.derivation,singleContraction])
    obtain ⟨v,source,remaining,sourceAtomic,sourcePaths,sourceInside,row⟩ :=
      middleAtomic.disjoint_row_pullback R headApart middleInside
    have sourcePositive : 0<source.length := by
      have eq := congrArg List.length (sourcePaths.trans middlePaths)
      rw [sourceAtomic.paths_length,ordinary.paths_length] at eq
      omega
    have first := removed.prepend (.single (singleContraction R)) (.single R)
    have second := Extraction.single (ExtractionStep.disjoint (.nil t) (.nil t)
      R source sourceAtomic middle middleAtomic (singleContraction remaining) row sourcePositive site headApart sourceInside)
    refine ⟨v,source,sourceAtomic,sourcePaths.trans middlePaths,sourceInside,?_,⟩
    exact .trans (by simpa only [ExtractionRun.prepend,ExtractionRun.of,ParallelHistory.single,ParallelHistory.append] using first) second

end Lamping.Lambda

