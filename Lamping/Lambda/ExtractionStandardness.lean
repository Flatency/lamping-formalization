import Lamping.Lambda.CanonicalPrefixStandard
import Lamping.Lambda.StandardizationNoReturn
import Lamping.Lambda.ProjectionStandardness
import Lamping.Lambda.ArgumentStandardness
namespace Lamping.Lambda
/-- PrefixStandard reads exactly the ordinary prefix before an actual final
contraction; it does not impose Standard on the whole extraction run. -/
theorem prefixStandard_append_last_iff (ρ : ParallelHistory m t) (atomic : Atomic ρ)
    (last : BetaAt t p u) :
    PrefixStandard (.of (ρ.append (.single (singleContraction last))) (atomic.append (.single last))) ↔ Standard ρ := by
  let point : RedexWithHistory m := ⟨t,ρ,⟨p,last.redex⟩⟩
  have represented : RunRepresents (.of (ρ.append (.single (singleContraction last))) (atomic.append (.single last))) point :=
    ⟨last,atomic,rfl⟩
  constructor
  · rintro ⟨other,representation,standard⟩
    have same := representation.unique represented
    subst other
    exact standard
  · intro standard; exact ⟨point,represented,standard⟩

/-- Extraction (i) deletes its penultimate contraction. The retained pointed
prefix is a genuine initial segment of the source's standard pointed prefix. -/
theorem residual_prefix_standard (ρ : ParallelHistory m t) (atomic : Atomic ρ)
    (R : BetaAt t p u) (S : BetaAt u q v) (original : BetaAt t q' w)
    (standard : PrefixStandard (.of ((ρ.append (.single (singleContraction R))).append (.single (singleContraction S)))
      ((atomic.append (.single R)).append (.single S)))) :
    PrefixStandard (.of (ρ.append (.single (singleContraction original))) (atomic.append (.single original))) := by
  apply (prefixStandard_append_last_iff ρ atomic original).mpr
  exact ((prefixStandard_append_last_iff _ (atomic.append (.single R)) S).mp standard).prefix
end Lamping.Lambda
namespace Lamping.Lambda
/-- Any actual pointed representation reads the same standard prefix. -/
theorem PrefixStandard.standard_of_representation (standard : PrefixStandard r)
    (represented : RunRepresents r a) : Standard a.history := by
  obtain ⟨b,hb,hs⟩ := standard
  have same := hb.unique represented
  subst b
  exact hs

/-- Both disjoint and function-part extraction preserve the standard pointed
prefix. Only the source prefix before its last contraction is assumed standard. -/
theorem region_prefix_standard (pre : ParallelHistory m t) (preAtomic : Atomic pre)
    (R : BetaAt t p u) (original : ParallelHistory t v) (originalAtomic : Atomic original)
    (full : ParallelHistory u w) (fullAtomic : Atomic full) (last : ParallelStep F v w)
    (row : StepProjection (singleContraction R) original full last) (positive : 0<original.length)
    (region : ExtractionRegion p site) (inside : Internal site original)
    (standard : PrefixStandard (.of ((pre.append (.single (singleContraction R))).append full)
      ((preAtomic.append (.single R)).append fullAtomic))) :
    PrefixStandard (.of (pre.append original) (preAtomic.append originalAtomic)) := by
  obtain ⟨topMid,q,topPre,S,topPreAtomic,topEq⟩ := originalAtomic.last positive
  have row' : StepProjection (singleContraction R) (topPre.append (.single (singleContraction S))) full last := by
    rw [←topEq]; exact row
  obtain ⟨bottomMid,K,bottomPre,vertical,projected,prefixRow,fullEq⟩ := row'.split_last topPre (singleContraction S)
  have bottomAtomic : Atomic (bottomPre.append (.single projected)) := by rw [←fullEq]; exact fullAtomic
  obtain ⟨bottomPreAtomic,lastAtomic⟩ := bottomAtomic.split_append
  obtain ⟨lastPath,B,paths⟩ := lastAtomic.single_step
  have singleEq : ParallelHistory.single projected=.single (singleContraction B) :=
    lastAtomic.paths_injective (.single B) (by simpa only [ParallelHistory.single_derivation] using paths)
  let sourcePointed : RedexWithHistory m := ⟨bottomMid,(pre.append (.single (singleContraction R))).append bottomPre,⟨lastPath,B.redex⟩⟩
  have represented : RunRepresents (.of ((pre.append (.single (singleContraction R))).append full)
      ((preAtomic.append (.single R)).append fullAtomic)) sourcePointed := by
    refine ⟨B,(preAtomic.append (.single R)).append bottomPreAtomic,?_⟩
    change (pre.append (.single (singleContraction R))).append full=
      ((pre.append (.single (singleContraction R))).append bottomPre).append (.single (singleContraction B))
    simp only [fullEq,singleEq,ParallelHistory.append_assoc]
  have sourceStandard := standard.standard_of_representation represented
  have localStandard : Standard bottomPre := sourceStandard.suffix
  have topInside : Internal site topPre := by
    intro r hr
    exact inside r (by rw [topEq,ParallelHistory.derivation_append]; change r∈topPre.derivation.paths++_; exact List.mem_append_left _ hr)
  let root : RedexOcc t := ⟨p,R.redex⟩
  have reflected := topPreAtomic.region_standard_reflect (singleContraction R) rfl root rfl region topInside prefixRow bottomPreAtomic localStandard
  have replaced : Standard (pre.append topPre) := Standard.replace_suffix_extension preAtomic
    ((Atomic.single R).append bottomPreAtomic) (by
      change Standard (pre.append ((ParallelHistory.single (singleContraction R)).append bottomPre))
      simpa only [sourcePointed,ParallelHistory.append_assoc] using sourceStandard)
    reflected (.single vertical) prefixRow.permutation
  let targetPointed : RedexWithHistory m := ⟨topMid,pre.append topPre,⟨q,S.redex⟩⟩
  refine ⟨targetPointed,⟨S,preAtomic.append topPreAtomic,?_⟩,replaced⟩
  change pre.append original=(pre.append topPre).append (.single (singleContraction S))
  rw [topEq,ParallelHistory.append_assoc]
end Lamping.Lambda
namespace Lamping.Lambda
/-- All four actual extraction generators preserve the source convention of
a standard pointed prefix. No full-run Standard premise is used. -/
theorem ExtractionStep.prefix_standard (step : ExtractionStep r s) (standard : PrefixStandard r) :
    PrefixStandard s := by
  cases step with
  | residual pre atomic R S original residual =>
    exact residual_prefix_standard pre atomic R S original standard
  | disjoint pre atomic R original ordinary full fullAtomic last row positive site apart inside =>
    exact region_prefix_standard pre atomic R original ordinary full fullAtomic last row positive (.inl apart) inside standard
  | functionPart pre atomic R original ordinary full fullAtomic last row positive inside =>
    exact region_prefix_standard pre atomic R original ordinary full fullAtomic last row positive (.inr rfl) inside standard
  | argumentPart pre atomic R copy copyAtomic original ordinary positive lift =>
    exact lift.prefix_standard copyAtomic ordinary positive pre atomic standard

/-- The complete least extraction closure preserves pointed-prefix standardness. -/
theorem Extraction.prefix_standard (steps : Extraction r s) (standard : PrefixStandard r) : PrefixStandard s := by
  induction steps with
  | refl => exact standard
  | cons step rest ih => exact ih (step.prefix_standard standard)

/-- Every standard pointed ordinary run has an actual canonical extraction
successor, obtained by termination plus the proved four-rule preservation. -/
theorem canonical_extraction_exists (standard : PrefixStandard r) :
    ∃ s, Extraction r s ∧ CanonicalRun s := by
  obtain ⟨s,steps,normal⟩ := extraction_normal_exists r
  exact ⟨s,steps,canonical_of_normal_prefix normal (steps.prefix_standard standard)⟩
end Lamping.Lambda
