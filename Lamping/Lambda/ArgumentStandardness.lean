import Lamping.Lambda.MirrorUsedSources
import Lamping.Lambda.ProjectionOrder
import Lamping.Lambda.UsedSourceContexts
import Lamping.Lambda.ArgumentParallelization
import Lamping.Lambda.CanonicalPrefixStandard
namespace Lamping.Lambda
/-- Reflect standardness from a specified renamed copy executing exactly the
same local ordinary program. All used-redex transport is proved from actual
prefixes; neither no-return nor a target standardness certificate is supplied. -/
theorem Atomic.region_rename_standard_reflect {source : ParallelHistory t u}
    (sourceAtomic : Atomic source) {copy : ParallelHistory t' u'} (copyAtomic : Atomic copy)
    (lookup : subtermAt t pre=some a) (copyLookup : subtermAt t' pre'=some (rename ren a))
    (ps : List Path) (paths : source.derivation.paths=ps.map (fun q => pre++q))
    (copyPaths : copy.derivation.paths=ps.map (fun q => pre'++q))
    (standard : Standard copy) : Standard source := by
  induction sourceAtomic generalizing t' u' a ps with
  | nil => exact .nil _
  | @cons t s mid u source S sourceAtomic ih =>
    cases ps with
    | nil => change _::_=[] at paths; cases paths
    | cons q ps =>
      change s::source.derivation.paths=(pre++q)::ps.map (fun q => pre++q) at paths
      obtain ⟨sourceAt,sourceTailPaths⟩ := List.cons.inj paths
      subst s
      cases copyAtomic with
      | nil => change []=_::_ at copyPaths; cases copyPaths
      | @cons t' c copyMid u' copy T copyAtomic =>
        change c::copy.derivation.paths=(pre'++q)::ps.map (fun q => pre'++q) at copyPaths
        obtain ⟨copyAt,copyTailPaths⟩ := List.cons.inj copyPaths
        subst c
        cases standard with
        | cons _ witness lo noReturn copyStandard =>
          have inside : Internal pre (.cons (singleContraction S) source) := by
            intro p hp
            change p∈(pre++q)::source.derivation.paths at hp
            rw [paths] at hp
            change p∈(q::ps).map (fun q => pre++q) at hp
            obtain ⟨q,_,same⟩ := List.mem_map.mp hp
            exact ⟨q,same.symm⟩
          have noReturnSource : DoesNotReturnLeft ⟨pre++q,S.redex⟩ (.cons (singleContraction S) source) := by
            apply DoesNotReturnLeft.of_no_used
            intro old before used
            obtain ⟨localR,oldAt⟩ := used.internal (.cons S sourceAtomic) inside
            have localValid := old.property
            rw [oldAt,subtermAt_append,lookup,Option.bind_some] at localValid
            obtain ⟨redex,localLookup,isRedex⟩ := localValid
            let image : RedexOcc t' := ⟨pre'++localR,by
              refine ⟨rename (occurrenceRenaming ren localR) redex,?_,(isRedex_rename_iff _ _).mpr isRedex⟩
              rw [subtermAt_append,copyLookup,Option.bind_some,subtermAt_rename,localLookup]
              rfl⟩
            have imageUsed := UsedSource.region_rename (.cons S sourceAtomic) (.cons T copyAtomic)
              lookup copyLookup (q::ps) paths copyPaths old image oldAt rfl used
            have localBefore : LeftOf localR q := by
              change LeftOf old.val (pre++q) at before
              rw [oldAt] at before
              exact before.strip_prefix
            have witnessAt : witness.val=pre'++q := List.mem_singleton.mp lo.1
            exact noReturn.no_used_left (.cons T copyAtomic) image
              (by rw [witnessAt]; exact localBefore.prefix_append pre') imageUsed
          obtain ⟨a',nextLookup,nextCopyLookup⟩ :=
            (ParallelHistory.single (singleContraction S)).derivation.region_rename_target
              (ParallelHistory.single (singleContraction T)).derivation lookup copyLookup [q] rfl rfl
          exact .cons (singleContraction S) ⟨pre++q,S.redex⟩ (leftmost_singleton _) noReturnSource
            (ih copyAtomic nextLookup nextCopyLookup ps sourceTailPaths copyTailPaths copyStandard)
end Lamping.Lambda
namespace Lamping.Lambda
/-- Every old source actually used in the original argument program is used
by the chosen-copy program after the actual beta. Other copies need no steps. -/
theorem argument_used_inclusion (R : BetaAt t p u)
    (lookup : subtermAt t p=some (.app (.lam body) arg)) (occurs : ArgumentOccurrence body occ)
    (original : ParallelHistory t v) (ordinary : Atomic original)
    (copy : ParallelHistory u w) (copyAtomic : Atomic copy) (ps : List Path)
    (originalPaths : original.derivation.paths=ps.map (fun q => (p++[.arg])++q))
    (copyPaths : copy.derivation.paths=ps.map (fun q => (p++occ)++q))
    (r : RedexOcc t) (used : UsedSource original r) :
    UsedSource ((ParallelHistory.single (singleContraction R)).append copy) r := by
  have inside : Internal (p++[.arg]) original := by
    intro q hq
    rw [originalPaths] at hq
    obtain ⟨q,_,same⟩ := List.mem_map.mp hq
    exact ⟨q,same.symm⟩
  obtain ⟨localR,atOriginal⟩ := used.internal ordinary inside
  have argumentLookup : subtermAt t (p++[.arg])=some arg := by
    rw [subtermAt_append,lookup,Option.bind_some]
    cases arg <;> rfl
  have copyLookup : subtermAt u (p++occ)=some (rename (fun i => i+binderDepth occ) arg) := by
    rw [subtermAt_append,R.contract_lookup lookup,Option.bind_some]
    exact argument_copy occurs arg
  obtain ⟨image,atCopy,residual⟩ := R.argument_residual_exists lookup r atOriginal occurs
  have copied := UsedSource.region_rename ordinary copyAtomic argumentLookup copyLookup ps originalPaths copyPaths
    r image atOriginal atCopy used
  exact copied.prepend (.single (singleContraction R)) r (by simpa only [ParallelHistory.single_derivation] using residual)
end Lamping.Lambda
namespace Lamping.Lambda
private theorem nonempty_last (xs : List α) (nonempty : xs≠[]) : ∃ ys last, xs=ys++[last] := by
  cases eq : xs.reverse with
  | nil =>
    have empty := congrArg List.reverse eq
    simp only [List.reverse_reverse,List.reverse_nil] at empty
    exact False.elim (nonempty empty)
  | cons last rest =>
    refine ⟨rest.reverse,last,?_⟩
    have h := congrArg List.reverse eq
    simpa only [List.reverse_reverse,List.reverse_cons] using h
private theorem append_singleton_injective (h : xs++[a]=ys++[b]) : xs=ys ∧ a=b := by
  have reversed := congrArg List.reverse h
  simp only [List.reverse_append,List.reverse_cons,List.reverse_nil,List.nil_append,List.singleton_append] at reversed
  obtain ⟨last,same⟩ := List.cons.inj reversed
  refine ⟨?_,last⟩
  have h := congrArg List.reverse same
  simpa only [List.reverse_reverse] using h

/-- Argument-copy extraction preserves the source pointed standard-prefix
convention. No Standard assumption on the full run or other-copy extension is
introduced: actual old-source use inclusion protects the shared prefix. -/
theorem ArgumentLift.prefix_standard {R : BetaAt t p u} {copy : ParallelHistory u v}
    {original : ParallelHistory t w} (lift : ArgumentLift R copy original)
    (copyAtomic : Atomic copy) (originalAtomic : Atomic original) (positive : 0<copy.length)
    (pre : ParallelHistory m t) (preAtomic : Atomic pre)
    (standard : PrefixStandard (.of ((pre.append (.single (singleContraction R))).append copy)
      ((preAtomic.append (.single R)).append copyAtomic))) :
    PrefixStandard (.of (pre.append original) (preAtomic.append originalAtomic)) := by
  have localNonempty : lift.localPaths≠[] := by
    intro empty
    have lengths := congrArg List.length lift.copy_paths
    rw [copyAtomic.paths_length,empty,List.map_nil] at lengths
    change copy.length=0 at lengths
    omega
  obtain ⟨qs,lastPath,localPaths⟩ := nonempty_last lift.localPaths localNonempty
  obtain ⟨copyMid,copyLast,copyPre,S,copyPreAtomic,copyEq⟩ := copyAtomic.last positive
  have originalPositive : 0<original.length := by rw [lift.length copyAtomic originalAtomic]; exact positive
  obtain ⟨originalMid,originalLast,originalPre,T,originalPreAtomic,originalEq⟩ := originalAtomic.last originalPositive
  have copyPaths := lift.copy_paths
  conv at copyPaths => lhs; rw [copyEq,ParallelHistory.derivation_append]
  rw [localPaths,List.map_append,List.map_cons,List.map_nil] at copyPaths
  change copyPre.derivation.paths++[copyLast]=
    qs.map (fun q => (p++lift.occurrence)++q)++[(p++lift.occurrence)++lastPath] at copyPaths
  obtain ⟨copyPrefixPaths,_⟩ := append_singleton_injective copyPaths
  have originalPaths := lift.original_paths
  conv at originalPaths => lhs; rw [originalEq,ParallelHistory.derivation_append]
  rw [localPaths,List.map_append,List.map_cons,List.map_nil] at originalPaths
  change originalPre.derivation.paths++[originalLast]=
    qs.map (fun q => (p++[.arg])++q)++[(p++[.arg])++lastPath] at originalPaths
  obtain ⟨originalPrefixPaths,_⟩ := append_singleton_injective originalPaths
  let sourcePoint : RedexWithHistory m := ⟨copyMid,(pre.append (.single (singleContraction R))).append copyPre,⟨copyLast,S.redex⟩⟩
  have represents : RunRepresents (.of ((pre.append (.single (singleContraction R))).append copy)
      ((preAtomic.append (.single R)).append copyAtomic)) sourcePoint := by
    refine ⟨S,(preAtomic.append (.single R)).append copyPreAtomic,?_⟩
    change (pre.append (.single (singleContraction R))).append copy=
      ((pre.append (.single (singleContraction R))).append copyPre).append (.single (singleContraction S))
    simp only [copyEq,ParallelHistory.append_assoc]
  obtain ⟨point,pointRep,pointStandard⟩ := standard
  have same := pointRep.unique represents
  subst point
  have localStandard : Standard copyPre := pointStandard.suffix
  have argumentLookup : subtermAt t (p++[.arg])=some lift.argument := by
    rw [subtermAt_append,lift.redex,Option.bind_some]
    cases lift.argument <;> rfl
  have copyLookup : subtermAt u (p++lift.occurrence)=some (rename (fun i => i+binderDepth lift.occurrence) lift.argument) := by
    rw [subtermAt_append,R.contract_lookup lift.redex,Option.bind_some]
    exact argument_copy lift.isVariable lift.argument
  have reflected := originalPreAtomic.region_rename_standard_reflect copyPreAtomic argumentLookup copyLookup
    qs originalPrefixPaths copyPrefixPaths localStandard
  have replaced : Standard (pre.append originalPre) := Standard.replace_suffix_used preAtomic
    ((Atomic.single R).append copyPreAtomic) (by
      change Standard (pre.append ((ParallelHistory.single (singleContraction R)).append copyPre))
      simpa only [sourcePoint,ParallelHistory.append_assoc] using pointStandard)
    reflected (argument_used_inclusion R lift.redex lift.isVariable originalPre originalPreAtomic copyPre copyPreAtomic qs originalPrefixPaths copyPrefixPaths)
  let targetPoint : RedexWithHistory m := ⟨originalMid,pre.append originalPre,⟨originalLast,T.redex⟩⟩
  refine ⟨targetPoint,⟨T,preAtomic.append originalPreAtomic,?_⟩,replaced⟩
  change pre.append original=(pre.append originalPre).append (.single (singleContraction T))
  rw [originalEq,ParallelHistory.append_assoc]
end Lamping.Lambda
