import Lamping.Lambda.ArgumentStandardness
namespace Lamping.Lambda
private theorem prefix_paths (atomic : Atomic pre) (eq : whole=pre.append tail) :
    pre.derivation.paths=whole.derivation.paths.take pre.length := by
  rw [eq,ParallelHistory.derivation_append]
  change pre.derivation.paths=List.take pre.length (pre.derivation.paths++tail.derivation.paths)
  rw [←atomic.paths_length,List.take_left]
private theorem suffix_paths (atomic : Atomic pre) (eq : whole=pre.append tail) :
    tail.derivation.paths=whole.derivation.paths.drop pre.length := by
  rw [eq,ParallelHistory.derivation_append]
  change tail.derivation.paths=List.drop pre.length (pre.derivation.paths++tail.derivation.paths)
  rw [←atomic.paths_length,List.drop_left]

/-- Reflect genuine usage through a specified renamed subtree executing
the same actual ordinary program. Variable renaming need not be injective. -/
theorem UsedSource.region_rename_reflect {source : ParallelHistory t u} {copy : ParallelHistory t' u'}
    (sourceAtomic : Atomic source) (copyAtomic : Atomic copy)
    (lookup : subtermAt t pre=some a) (copyLookup : subtermAt t' pre'=some (rename ren a))
    (ps : List Path) (paths : source.derivation.paths=ps.map (fun q => pre++q))
    (copyPaths : copy.derivation.paths=ps.map (fun q => pre'++q))
    (r : RedexOcc t) (image : RedexOcc t') (atSource : r.val=pre++localR)
    (atCopy : image.val=pre'++localR) (used : UsedSource copy image) : UsedSource source r := by
  obtain ⟨v,w,F,copyPre,step,suffix,q,eq,selected,residual⟩ := used
  have whole : Atomic (copyPre.append (.cons step suffix)) := by rw [←eq]; exact copyAtomic
  obtain ⟨prefixAtomic,restAtomic⟩ := whole.split_append
  cases restAtomic with
  | cons head tailAtomic =>
    have qEq : q=⟨_,head.redex⟩ := Subtype.ext (List.mem_singleton.mp selected)
    subst q
    have copyPrefixPaths : copyPre.derivation.paths=(ps.take copyPre.length).map (fun q => pre'++q) := by
      rw [prefix_paths prefixAtomic eq,copyPaths,←List.map_take]
    have copyRestPaths : (.cons (singleContraction head) suffix : ParallelHistory v u').derivation.paths=
        (ps.drop copyPre.length).map (fun q => pre'++q) := by
      rw [suffix_paths prefixAtomic eq,copyPaths,←List.map_drop]
    have lengths : copyPre.length≤source.length := by
      have copyLength := congrArg List.length copyPaths
      have sourceLength := congrArg List.length paths
      rw [copyAtomic.paths_length,List.length_map] at copyLength
      rw [sourceAtomic.paths_length,List.length_map] at sourceLength
      have fullLength := congrArg ParallelHistory.length eq
      simp only [ParallelHistory.length_append,ParallelHistory.length] at fullLength
      omega
    obtain ⟨copyMid,sourcePrefix,sourceRest,sourcePrefixAtomic,sourceRestAtomic,sourceEq,sourceLength⟩ := sourceAtomic.split_at copyPre.length lengths
    have sourcePrefixPaths : sourcePrefix.derivation.paths=(ps.take copyPre.length).map (fun q => pre++q) := by
      rw [prefix_paths sourcePrefixAtomic sourceEq,sourceLength,paths,←List.map_take]
    have sourceRestPaths : sourceRest.derivation.paths=(ps.drop copyPre.length).map (fun q => pre++q) := by
      rw [suffix_paths sourcePrefixAtomic sourceEq,sourceLength,paths,←List.map_drop]
    cases localEq : ps.drop copyPre.length with
    | nil => rw [localEq,List.map_nil] at copyRestPaths; change _::_=[] at copyRestPaths; cases copyRestPaths
    | cons localHead localTail =>
      rw [localEq,List.map_cons] at copyRestPaths sourceRestPaths
      change _::suffix.derivation.paths=(pre'++localHead)::_ at copyRestPaths
      have sourceHeadAt := (List.cons.inj copyRestPaths).1
      cases sourceRestAtomic with
      | nil => change []=_::_ at sourceRestPaths; cases sourceRestPaths
      | @cons copyMid copyPath copyAfter u copyTail copiedHead copyTailAtomic =>
        change copyPath::copyTail.derivation.paths=(pre++localHead)::_ at sourceRestPaths
        have copiedHeadAt := (List.cons.inj sourceRestPaths).1
        let target : RedexOcc v := ⟨_,head.redex⟩
        let copiedTarget : RedexOcc copyMid := ⟨copyPath,copiedHead.redex⟩
        have mirrored := sourcePrefix.derivation.region_rename_residual_iff copyPre.derivation lookup copyLookup
          (ps.take copyPre.length) sourcePrefixPaths copyPrefixPaths r copiedTarget image target
          atSource copiedHeadAt atCopy sourceHeadAt
        refine ⟨copyMid,copyAfter,[copyPath],sourcePrefix,singleContraction copiedHead,copyTail,copiedTarget,sourceEq,by simp [copiedTarget],?_⟩
        exact mirrored.mp residual
/-- Forward standardness for the actual ordinary program in a specified
renamed subtree. This does not invert the variable renaming. -/
theorem Atomic.region_rename_standard_project {source : ParallelHistory t u}
    (sourceAtomic : Atomic source) {copy : ParallelHistory t' u'} (copyAtomic : Atomic copy)
    (lookup : subtermAt t pre=some a) (copyLookup : subtermAt t' pre'=some (rename ren a))
    (ps : List Path) (paths : source.derivation.paths=ps.map (fun q => pre++q))
    (copyPaths : copy.derivation.paths=ps.map (fun q => pre'++q))
    (standard : Standard source) : Standard copy := by
  induction sourceAtomic generalizing t' u' a ps with
  | nil =>
    have zero : copy.length=0 := by
      have lens := congrArg List.length paths
      change 0=List.length (List.map (fun q => pre++q) ps) at lens
      have copied := congrArg List.length copyPaths
      rw [copyAtomic.paths_length,List.length_map] at copied
      simp only [List.length_map] at lens
      omega
    cases copyAtomic with
    | nil => exact .nil _
    | cons T tail => change 1+_ = 0 at zero; omega
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
        | cons _ witness lo noReturn sourceStandard =>
          have inside : Internal pre' (.cons (singleContraction T) copy) := by
            intro p hp
            change p∈(pre'++q)::copy.derivation.paths at hp
            rw [copyPaths] at hp
            change p∈(q::ps).map (fun q => pre'++q) at hp
            obtain ⟨q,_,same⟩ := List.mem_map.mp hp
            exact ⟨q,same.symm⟩
          have noReturnCopy : DoesNotReturnLeft ⟨pre'++q,T.redex⟩ (.cons (singleContraction T) copy) := by
            apply DoesNotReturnLeft.of_no_used
            intro old before used
            obtain ⟨localR,oldAt⟩ := used.internal (.cons T copyAtomic) inside
            have localValid := old.property
            rw [oldAt,subtermAt_append,copyLookup,Option.bind_some] at localValid
            have originalValid := redex_rename_reflect localValid
            let original : RedexOcc t := ⟨pre++localR,by
              obtain ⟨z,hz,red⟩ := originalValid
              exact ⟨z,by rw [subtermAt_append,lookup,Option.bind_some]; exact hz,red⟩⟩
            have originalUsed := UsedSource.region_rename_reflect (.cons S sourceAtomic) (.cons T copyAtomic)
              lookup copyLookup (q::ps) paths copyPaths original old rfl oldAt used
            have localBefore : LeftOf localR q := by
              change LeftOf old.val (pre'++q) at before
              rw [oldAt] at before
              exact before.strip_prefix
            have witnessAt : witness.val=pre++q := List.mem_singleton.mp lo.1
            exact noReturn.no_used_left (.cons S sourceAtomic) original
              (by rw [witnessAt]; exact localBefore.prefix_append pre) originalUsed
          obtain ⟨a',nextLookup,nextCopyLookup⟩ :=
            (ParallelHistory.single (singleContraction S)).derivation.region_rename_target
              (ParallelHistory.single (singleContraction T)).derivation lookup copyLookup [q] rfl rfl
          exact .cons (singleContraction T) ⟨pre'++q,T.redex⟩ (leftmost_singleton _) noReturnCopy
            (ih copyAtomic nextLookup nextCopyLookup ps sourceTailPaths copyTailPaths sourceStandard)
end Lamping.Lambda
