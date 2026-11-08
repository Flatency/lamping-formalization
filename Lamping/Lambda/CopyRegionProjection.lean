import Lamping.Lambda.CopyRegionPruning
import Lamping.Lambda.FunctionProjectionStandardness
namespace Lamping.Lambda

/-- Project a genuinely ordinary function/disjoint pointed source through
the target's first beta. The actual projected pointed projectedPrefix is standard,
is a Copy ancestor of the target tail, and its prefixed run really extracts
back to the supplied source by rule (ii) or (iii). -/
theorem Copy.project_region_run (R : BetaAt m p t) (a : RedexWithHistory m) (b : RedexWithHistory t)
    (copy : Copy a ⟨b.target,(ParallelHistory.single (singleContraction R)).append b.history,b.redex⟩)
    (represented : RunRepresents r a) (standard : Standard a.history)
    (region : ExtractionRegion p site) (inside : Internal site r.history) :
    ∃ s : ExtractionRun t, ∃ image : RedexWithHistory t,
      RunRepresents s image ∧ Standard image.history ∧ Copy image b ∧
      Extraction (s.prepend (.single (singleContraction R)) (.single R)) r := by
  obtain ⟨S,ordinary,history⟩ := represented
  have prefixInside : Internal site a.history := by
    intro q hq
    apply inside q
    rw [history,ParallelHistory.derivation_append]
    exact List.mem_append_left _ hq
  have lastInside : ∃q,a.redex.val=site++q := inside a.redex.val (by
    rw [history,ParallelHistory.derivation_append,ParallelHistory.single_derivation]
    change a.redex.val∈a.history.derivation.paths++[a.redex.val]
    simp)
  obtain ⟨A,F,projectedPrefix,vertical,prefixAtomic,row⟩ := ordinary.region_projection (singleContraction R)
    rfl ⟨p,R.redex⟩ rfl region prefixInside
  have selected := row.final_selection_singleton rfl ⟨p,R.redex⟩ rfl ordinary prefixInside region.root_outside
  obtain ⟨_,remaining⟩ := row.final_vertical_singleton prefixInside region.root_outside
  subst F
  obtain ⟨R1,verticalEq⟩ := vertical.eq_single_contraction ⟨p,remaining.redex⟩ rfl
  subst vertical
  obtain ⟨image,oldImage,copyImage⟩ := copy.project_target_head R a b row
  obtain ⟨w,T⟩ := image.contract_exists
  have oneImage : ∃q,(singleContraction R1).residualSet [a.redex.val]=[q] := by
    rcases region with apart | function
    · exact ⟨a.redex.val,R1.outside_residualSet_singleton a.redex (apart.descendant_outside lastInside)⟩
    · obtain ⟨q,_,selection⟩ := R1.function_residualSet_singleton a.redex (by simpa only [function] using lastInside)
      exact ⟨p++q,selection⟩
  obtain ⟨q,selection⟩ := oneImage
  have chosenSelection := (singleContraction R1).residual_image_target a.redex image selection oldImage
  obtain ⟨G,last,tailRow⟩ := singleton_projection_row R1 S T chosenSelection
  have fullRow := row.append tailRow
  let sourceRun : ExtractionRun m := .of (a.history.append (.single (singleContraction S))) (ordinary.append (.single S))
  let targetRun : ExtractionRun t := .of (projectedPrefix.append (.single (singleContraction T))) (prefixAtomic.append (.single T))
  have sourceEq : sourceRun=r := by
    apply ExtractionRun.ext_paths
    change (a.history.append (.single (singleContraction S))).derivation.paths=r.history.derivation.paths
    rw [history]
  have fullInside : Internal site sourceRun.history := by rw [sourceEq]; exact inside
  have positive : 0<(a.history.append (.single (singleContraction S))).length := by
    simp [ParallelHistory.length_append,ParallelHistory.single,ParallelHistory.length]
  have actual : ExtractionStep (targetRun.prepend (.single (singleContraction R)) (.single R)) sourceRun := by
    rcases region with apart | function
    · simpa only [targetRun,sourceRun,ExtractionRun.prepend,ExtractionRun.of,ParallelHistory.append] using
        ExtractionStep.disjoint (.nil m) (.nil m) R _ (ordinary.append (.single S))
          _ (prefixAtomic.append (.single T)) last fullRow positive site apart fullInside
    · subst site
      simpa only [targetRun,sourceRun,ExtractionRun.prepend,ExtractionRun.of,ParallelHistory.append] using
        ExtractionStep.functionPart (.nil m) (.nil m) R _ (ordinary.append (.single S))
          _ (prefixAtomic.append (.single T)) last fullRow positive fullInside
  refine ⟨targetRun,⟨A,projectedPrefix,image⟩,⟨T,prefixAtomic,rfl⟩,?_,copyImage,?_⟩
  · exact ordinary.region_standard_project (singleContraction R) rfl ⟨p,R.redex⟩ rfl region prefixInside row prefixAtomic standard
  · rw [←sourceEq]
    exact .single actual

end Lamping.Lambda

