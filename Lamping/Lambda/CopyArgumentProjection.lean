import Lamping.Lambda.ArgumentForwardMirror
import Lamping.Lambda.RenameProjectionStandardness
namespace Lamping.Lambda

/-- Select the actual ordinary argument copy required by the target tail.
The given full parallelization is never assumed ordinary or standard. -/
theorem Copy.project_argument_run (R : BetaAt m p t) (a : RedexWithHistory m) (b : RedexWithHistory t)
    (copy : Copy a ⟨b.target,(ParallelHistory.single (singleContraction R)).append b.history,b.redex⟩)
    (represented : RunRepresents r a) (standard : Standard a.history)
    (inside : Internal (p++[.arg]) r.history) :
    ∃ s : ExtractionRun t, ∃ image : RedexWithHistory t,
      RunRepresents s image ∧ Standard image.history ∧ Copy image b ∧
      Extraction (s.prepend (.single (singleContraction R)) (.single R)) r := by
  obtain ⟨S,ordinary,history⟩ := represented
  obtain ⟨body,argument,lookup,replace⟩ := R
  have R : BetaAt m p t := ⟨body,argument,lookup,replace⟩
  have prefixInside : Internal (p++[.arg]) a.history := by
    intro q hq
    apply inside q
    rw [history,ParallelHistory.derivation_append]
    exact List.mem_append_left _ hq
  obtain ⟨localLast,lastAt⟩ := inside a.redex.val (by
    rw [history,ParallelHistory.derivation_append,ParallelHistory.single_derivation]
    change a.redex.val∈a.history.derivation.paths++[a.redex.val]
    simp)
  have outside : ¬∃q,p=(p++[.arg])++q := by
    rintro ⟨q,eq⟩
    have lengths := congrArg List.length eq
    simp only [List.length_append,List.length_singleton] at lengths
    omega
  obtain ⟨A,F,full,vertical,row⟩ := StepProjection.exists_projection (singleContraction R) a.history
  have selected := row.final_selection_singleton rfl ⟨p,R.redex⟩ rfl ordinary prefixInside outside
  obtain ⟨_,remaining⟩ := row.final_vertical_singleton prefixInside outside
  subst F
  obtain ⟨R1,verticalEq⟩ := vertical.eq_single_contraction ⟨p,remaining.redex⟩ rfl
  subst vertical
  obtain ⟨image,oldImage,copyImage⟩ := copy.project_target_head R a b row
  obtain ⟨argument',_,afterLookup,_,_⟩ := a.history.argument_head_preserved lookup prefixInside
  obtain ⟨occ,occurs,imageAt⟩ := (R1.argument_residual_iff afterLookup a.redex lastAt image).mp oldImage
  obtain ⟨V,chosen,chosenAtomic,mirror,mirrorOcc⟩ := ordinary.argument_forward_mirror R lookup prefixInside occurs
  obtain ⟨other,factor,apart⟩ := mirror.factor_projection chosenAtomic ordinary row
  rw [mirrorOcc] at apart
  have stepsApart : ∀q∈other.derivation.paths,DisjointPositions image.val q := by
    intro q hq
    rw [imageAt]
    exact (apart.paths_apart q hq).descend_left localLast
  have fixed := other.derivation.valid.subterm_fixed_apart stepsApart
  have sourceValid := image.property
  rw [fixed] at sourceValid
  let chosenRedex : RedexOcc V := ⟨image.val,sourceValid⟩
  obtain ⟨sameImage,samePath,otherResidual⟩ := apart.inside_survives chosenRedex ⟨localLast,imageAt⟩
  have same : sameImage=image := Subtype.ext samePath
  subst sameImage
  have chosenCopy : Copy ⟨V,chosen,chosenRedex⟩ b :=
    (show Copy ⟨V,chosen,chosenRedex⟩ ⟨A,full,image⟩ from ⟨other,factor.symm,otherResidual⟩).trans copyImage
  obtain ⟨w,T⟩ := chosenRedex.contract_exists
  have copyPaths : chosen.derivation.paths=mirror.localPaths.map (fun q => (p++occ)++q) := by
    simpa only [mirrorOcc] using mirror.copy_paths
  let sourceRun : ExtractionRun m := .of (a.history.append (.single (singleContraction S))) (ordinary.append (.single S))
  let targetRun : ExtractionRun t := .of (chosen.append (.single (singleContraction T))) (chosenAtomic.append (.single T))
  have sourceEq : sourceRun=r := by
    apply ExtractionRun.ext_paths
    change (a.history.append (.single (singleContraction S))).derivation.paths=r.history.derivation.paths
    rw [history]
  have originalPaths : sourceRun.history.derivation.paths=(mirror.localPaths++[localLast]).map (fun q => (p++[.arg])++q) := by
    change (a.history.append (.single (singleContraction S))).derivation.paths=_
    simp only [ParallelHistory.derivation_append,ParallelHistory.single_derivation,Derivation.append,
      ParallelStep.derivation,singleContraction,List.map_append,List.map_cons,List.map_nil]
    rw [mirror.original_paths,lastAt]
  have chosenPaths : targetRun.history.derivation.paths=(mirror.localPaths++[localLast]).map (fun q => (p++occ)++q) := by
    change (chosen.append (.single (singleContraction T))).derivation.paths=_
    simp only [ParallelHistory.derivation_append,ParallelHistory.single_derivation,Derivation.append,
      ParallelStep.derivation,singleContraction,List.map_append,List.map_cons,List.map_nil]
    rw [copyPaths]
    simpa only [copyPaths] using congrArg (fun xs => chosen.derivation.paths++xs) (congrArg (fun q => [q]) imageAt)
  let fullMirror : ArgumentLift R targetRun.history sourceRun.history := {
    body := body
    argument := argument
    redex := lookup
    occurrence := occ
    isVariable := occurs
    localPaths := mirror.localPaths++[localLast]
    copy_paths := chosenPaths
    original_paths := originalPaths
    parallelization := StepProjection.exists_projection (singleContraction R) sourceRun.history }
  have actual : ExtractionStep (targetRun.prepend (.single (singleContraction R)) (.single R)) sourceRun := by
    simpa only [sourceRun,targetRun,ExtractionRun.prepend,ExtractionRun.of,ParallelHistory.append] using
      ExtractionStep.argumentPart (.nil m) (.nil m) R targetRun.history targetRun.atomic sourceRun.history sourceRun.atomic
        (by simp [targetRun,ExtractionRun.of,ParallelHistory.length_append,ParallelHistory.single,ParallelHistory.length]) fullMirror
  have argumentLookup : subtermAt m (p++[.arg])=some argument := by
    rw [subtermAt_append,lookup]
    simp [subtermAt]
  have chosenLookup : subtermAt t (p++occ)=some (rename (fun i => i+binderDepth occ) argument) := by
    rw [subtermAt_append,R.contract_lookup lookup,Option.bind_some]
    exact argument_copy occurs argument
  have chosenStandard := ordinary.region_rename_standard_project chosenAtomic argumentLookup chosenLookup
    mirror.localPaths mirror.original_paths copyPaths standard
  refine ⟨targetRun,⟨V,chosen,chosenRedex⟩,⟨T,chosenAtomic,rfl⟩,chosenStandard,chosenCopy,?_⟩
  rw [←sourceEq]
  exact .single actual

end Lamping.Lambda
