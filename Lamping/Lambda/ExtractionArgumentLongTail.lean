import Lamping.Lambda.ArgumentLiftSplits
import Lamping.Lambda.ArgumentMirrorResiduals
import Lamping.Lambda.ExtractionInternal
import Lamping.Lambda.ExtractionConfluence
import Lamping.Lambda.RootCreation
namespace Lamping.Lambda

private theorem prefix_map_injective (pre : Path) {xs ys : List Path}
    (he : xs.map (fun q => pre ++ q) = ys.map (fun q => pre ++ q)) : xs = ys := by
  induction xs generalizing ys with
  | nil =>
    cases ys with
    | nil => rfl
    | cons => simp at he
  | cons x xs ih =>
    cases ys with
    | nil => simp at he
    | cons y ys =>
      have parts := List.cons.inj he
      have head := List.append_cancel_left parts.1
      cases head
      exact congrArg (List.cons x) (ih parts.2)

private theorem contract_redex (r : RedexOcc t) : ∃ u, BetaAt t r.val u := by
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

/-- LEV80 (4,1), including an arbitrary middle history inside the specified
 argument instance. Both outputs join by actual (i) and (iv), respectively. -/
theorem extraction_argument_residual_long_peak
    (R : BetaAt t p u) (copyPre : ParallelHistory u b) (hc : Atomic copyPre)
    (S : BetaAt b s v) (T : BetaAt v z w)
    (original : ParallelHistory t w') (ho : Atomic original)
    (lift : ArgumentLift R
      (copyPre.append (.cons (singleContraction S) (.single (singleContraction T)))) original)
    (V : BetaAt b q x)
    (predecessor : (singleContraction S).derivation.Residual ⟨q, V.redex⟩ ⟨z, T.redex⟩) :
    ExtractionJoin (.of original ho)
      (.of (.cons (singleContraction R) (copyPre.append (.single (singleContraction V))))
        (.cons R (hc.append (.single V)))) := by
  obtain ⟨a, pre, post, hp, ht, whole, left, right, localSplit, copyLeft, copyRight,
      originalLeft, originalRight⟩ :=
    lift.split_prefix R copyPre _ original hc (.cons S (.single T)) ho
  have rightLength : right.length = 2 := by
    have h := congrArg List.length copyRight
    change 2 = (List.map _ right).length at h
    simpa only [List.length_map] using h.symm
  have postLength : post.length = 2 := by
    have h := congrArg List.length originalRight
    rw [ht.paths_length, List.length_map, rightLength] at h
    exact h
  obtain ⟨a', s', z', S', T', postEq⟩ := ht.two_contractions postLength
  cases postEq
  obtain ⟨localS, localT, rightEq⟩ : ∃ localS localT, right = [localS, localT] := by
    cases right with
    | nil => cases rightLength
    | cons first tail =>
      cases tail with
      | nil => cases rightLength
      | cons second rest =>
        have empty : rest = [] := by
          have len : rest.length = 0 := by simp only [List.length_cons] at rightLength; omega
          exact List.length_eq_zero_iff.mp len
        subst rest
        exact ⟨first, second, rfl⟩
  have copiedNames : s = (p ++ lift.occurrence) ++ localS ∧
      z = (p ++ lift.occurrence) ++ localT := by
    change [s, z] = _ at copyRight
    simpa only [rightEq, List.map_cons, List.map_nil, List.cons.injEq, and_true] using copyRight
  have originalNames : s' = (p ++ [.arg]) ++ localS ∧ z' = (p ++ [.arg]) ++ localT := by
    change [s', z'] = _ at originalRight
    simpa only [rightEq, List.map_cons, List.map_nil, List.cons.injEq, and_true] using originalRight
  have initialArgument : subtermAt t (p ++ [.arg]) = some lift.argument := by
    rw [subtermAt_append, lift.redex, Option.bind_some]
    cases lift.argument <;> rfl
  have initialCopy : subtermAt u (p ++ lift.occurrence) =
      some (rename (fun i => i + binderDepth lift.occurrence) lift.argument) := by
    rw [subtermAt_append, R.contract_lookup lift.redex, Option.bind_some]
    exact argument_copy lift.isVariable lift.argument
  obtain ⟨argument, argumentLookup, copyLookup⟩ := pre.derivation.region_rename_target
    copyPre.derivation initialArgument initialCopy left originalLeft copyLeft
  have sInside : Internal (p ++ lift.occurrence) (.single (singleContraction S)) :=
    (Internal.single_iff S).mpr ⟨localS, copiedNames.1⟩
  obtain ⟨localV, vName⟩ := (ParallelHistory.single (singleContraction S)).residual_reflect_internal
    sInside ⟨q, V.redex⟩ ⟨z, T.redex⟩ ⟨localT, copiedNames.2⟩ predecessor
  change q = (p ++ lift.occurrence) ++ localV at vName
  have copyRedex : ∃ redex, subtermAt
      (rename (fun i => i + binderDepth lift.occurrence) argument) localV = some redex ∧ IsRedex redex := by
    have h := V.redex
    rw [vName, subtermAt_append, copyLookup, Option.bind_some] at h
    exact h
  let old : RedexOcc a := ⟨(p ++ [.arg]) ++ localV, by
    rw [subtermAt_append, argumentLookup, Option.bind_some]
    exact redex_rename_reflect copyRedex⟩
  obtain ⟨target, originalV⟩ := contract_redex old
  have mirrored : (singleContraction S').derivation.Residual
      ⟨old.val, originalV.redex⟩ ⟨z', T'.redex⟩ := by
    apply ((singleContraction S').derivation.region_rename_residual_iff
      (singleContraction S).derivation argumentLookup copyLookup [localS]
      (by change [s'] = _; simp only [List.map_cons, List.map_nil, originalNames.1])
      (by change [s] = _; simp only [List.map_cons, List.map_nil, copiedNames.1])
      ⟨old.val, originalV.redex⟩ ⟨z', T'.redex⟩ ⟨q, V.redex⟩ ⟨z, T.redex⟩
      rfl originalNames.2 vName copiedNames.2).mp
    exact predecessor
  have preInternal : Internal (p ++ lift.occurrence) copyPre := by
    intro name member
    rw [copyLeft] at member
    obtain ⟨localName, _, rfl⟩ := List.mem_map.mp member
    exact ⟨localName, rfl⟩
  have newInternal : Internal (p ++ lift.occurrence)
      (copyPre.append (.single (singleContraction V))) :=
    (Internal.append_iff _ _).mpr ⟨preInternal, (Internal.single_iff V).mpr ⟨localV, vName⟩⟩
  obtain ⟨newTarget, newOriginal, hn, newLift, sameOccurrence⟩ :=
    argument_lift_exists R lift.redex lift.isVariable
      (copyPre.append (.single (singleContraction V))) newInternal
  have newLocal : newLift.localPaths = left ++ [localV] := by
    apply prefix_map_injective (p ++ lift.occurrence)
    have h := newLift.copy_paths
    rw [sameOccurrence] at h
    have actual : (copyPre.append (.single (singleContraction V))).derivation.paths =
        (left ++ [localV]).map (fun q => (p ++ lift.occurrence) ++ q) := by
      simp only [ParallelHistory.derivation_append, Derivation.append, ParallelHistory.single_derivation]
      change copyPre.derivation.paths ++ [q] = _
      simp only [copyLeft, List.map_append, List.map_cons, List.map_nil, vName]
    exact h.symm.trans actual
  let common := ExtractionRun.of (pre.append (.single (singleContraction originalV)))
    (hp.append (.single originalV))
  have newEqual : ExtractionRun.of newOriginal hn = common := by
    apply ExtractionRun.ext_paths
    simp only [ExtractionRun.of, common, ParallelHistory.derivation_append, Derivation.append,
      ParallelHistory.single_derivation]
    change newOriginal.derivation.paths = pre.derivation.paths ++ [old.val]
    rw [newLift.original_paths, newLocal, List.map_append, originalLeft]
    rfl
  refine ⟨common, Extraction.single ?_, Extraction.single ?_⟩
  · have sourceEqual : ExtractionRun.of original ho = ExtractionRun.of
        (pre.append (.cons (singleContraction S') (.single (singleContraction T'))))
        (hp.append (.cons S' (.single T'))) := by
      apply ExtractionRun.ext_paths
      exact congrArg (fun h => h.derivation.paths) whole
    rw [sourceEqual]
    simpa only [ParallelHistory.append_assoc] using
      (ExtractionStep.residual pre hp S' T' originalV mirrored)
  · have step := ExtractionStep.argumentPart (.nil t) (.nil t) R _
      (hc.append (.single V)) newOriginal hn
      (by rw [ParallelHistory.length_append]; change 0 < copyPre.length + 1; omega) newLift
    change ExtractionStep
      (.of (.cons (singleContraction R) (copyPre.append (.single (singleContraction V))))
        (.cons R (hc.append (.single V)))) (.of newOriginal hn) at step
    rw [newEqual] at step
    exact step

end Lamping.Lambda
