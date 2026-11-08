import Lamping.Lambda.ProjectionUsedSources
import Lamping.Lambda.ArgumentMirrorResiduals
import Lamping.Lambda.ArgumentResidualScope
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

/-- Actual same-program histories in two corresponding renamed subtrees map
a genuinely used old occurrence to its corresponding used occurrence. -/
theorem UsedSource.region_rename {source : ParallelHistory t u} {copy : ParallelHistory t' u'}
    (sourceAtomic : Atomic source) (copyAtomic : Atomic copy)
    (lookup : subtermAt t pre=some a) (copyLookup : subtermAt t' pre'=some (rename ren a))
    (ps : List Path) (paths : source.derivation.paths=ps.map (fun q => pre++q))
    (copyPaths : copy.derivation.paths=ps.map (fun q => pre'++q))
    (r : RedexOcc t) (image : RedexOcc t') (atSource : r.val=pre++localR)
    (atCopy : image.val=pre'++localR) (used : UsedSource source r) : UsedSource copy image := by
  obtain ⟨v,w,F,sourcePre,step,suffix,q,eq,selected,residual⟩ := used
  have whole : Atomic (sourcePre.append (.cons step suffix)) := by rw [←eq]; exact sourceAtomic
  obtain ⟨prefixAtomic,restAtomic⟩ := whole.split_append
  cases restAtomic with
  | cons head tailAtomic =>
    have qEq : q=⟨_,head.redex⟩ := Subtype.ext (List.mem_singleton.mp selected)
    subst q
    have sourcePrefixPaths : sourcePre.derivation.paths=(ps.take sourcePre.length).map (fun q => pre++q) := by
      rw [prefix_paths prefixAtomic eq,paths,←List.map_take]
    have sourceRestPaths : (.cons (singleContraction head) suffix : ParallelHistory v u).derivation.paths=
        (ps.drop sourcePre.length).map (fun q => pre++q) := by
      rw [suffix_paths prefixAtomic eq,paths,←List.map_drop]
    have lengths : sourcePre.length≤copy.length := by
      have sourceLength := congrArg List.length paths
      have copyLength := congrArg List.length copyPaths
      rw [sourceAtomic.paths_length,List.length_map] at sourceLength
      rw [copyAtomic.paths_length,List.length_map] at copyLength
      have fullLength := congrArg ParallelHistory.length eq
      simp only [ParallelHistory.length_append,ParallelHistory.length] at fullLength
      omega
    obtain ⟨copyMid,copyPrefix,copyRest,copyPrefixAtomic,copyRestAtomic,copyEq,copyLength⟩ := copyAtomic.split_at sourcePre.length lengths
    have copyPrefixPaths : copyPrefix.derivation.paths=(ps.take sourcePre.length).map (fun q => pre'++q) := by
      rw [prefix_paths copyPrefixAtomic copyEq,copyLength,copyPaths,←List.map_take]
    have copyRestPaths : copyRest.derivation.paths=(ps.drop sourcePre.length).map (fun q => pre'++q) := by
      rw [suffix_paths copyPrefixAtomic copyEq,copyLength,copyPaths,←List.map_drop]
    cases localEq : ps.drop sourcePre.length with
    | nil => rw [localEq,List.map_nil] at sourceRestPaths; change _::_=[] at sourceRestPaths; cases sourceRestPaths
    | cons localHead localTail =>
      rw [localEq,List.map_cons] at sourceRestPaths copyRestPaths
      change _::suffix.derivation.paths=(pre++localHead)::_ at sourceRestPaths
      have sourceHeadAt := (List.cons.inj sourceRestPaths).1
      cases copyRestAtomic with
      | nil => change []=_::_ at copyRestPaths; cases copyRestPaths
      | @cons copyMid copyPath copyAfter u' copyTail copiedHead copyTailAtomic =>
        change copyPath::copyTail.derivation.paths=(pre'++localHead)::_ at copyRestPaths
        have copiedHeadAt := (List.cons.inj copyRestPaths).1
        let target : RedexOcc v := ⟨_,head.redex⟩
        let copiedTarget : RedexOcc copyMid := ⟨copyPath,copiedHead.redex⟩
        have mirrored := sourcePre.derivation.region_rename_residual_iff copyPrefix.derivation lookup copyLookup
          (ps.take sourcePre.length) sourcePrefixPaths copyPrefixPaths r target image copiedTarget
          atSource sourceHeadAt atCopy copiedHeadAt
        refine ⟨copyMid,copyAfter,[copyPath],copyPrefix,singleContraction copiedHead,copyTail,copiedTarget,copyEq,by simp [copiedTarget],?_⟩
        exact mirrored.mpr residual
end Lamping.Lambda

