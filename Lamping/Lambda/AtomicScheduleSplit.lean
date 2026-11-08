import Lamping.Lambda.OrdinarySplits
namespace Lamping.Lambda

/-- Split a given actual ordinary schedule at a specified local program
boundary. Neither the global intermediate term nor either global half is
assumed; both are recovered from the original schedule. -/
theorem Atomic.split_mapped_program {global : ParallelHistory T U} (hg : Atomic global)
    {pre : ParallelHistory a b} {post : ParallelHistory b c}
    (hp : Atomic pre) (hq : Atomic post)
    (paths : global.derivation.paths=(pre.append post).derivation.paths.map (fun p => site++p)) :
    ∃ M, ∃ first : ParallelHistory T M, ∃ last : ParallelHistory M U,
      Atomic first ∧ Atomic last ∧ global=first.append last ∧ first.length=pre.length ∧
      first.derivation.paths=pre.derivation.paths.map (fun p => site++p) ∧
      last.derivation.paths=post.derivation.paths.map (fun p => site++p) := by
  have total : global.length=pre.length+post.length := by
    have same := congrArg List.length paths
    rw [hg.paths_length,List.length_map,(hp.append hq).paths_length,
      ParallelHistory.length_append] at same
    exact same
  obtain ⟨M,first,last,ha,hb,whole,length⟩ := hg.split_at pre.length (by omega)
  have allPaths := congrArg (fun h => h.derivation.paths) whole
  change global.derivation.paths=(first.append last).derivation.paths at allPaths
  rw [paths] at allPaths
  simp only [ParallelHistory.derivation_append,Derivation.append,List.map_append] at allPaths
  have sameLength : first.derivation.paths.length=
      (pre.derivation.paths.map (fun p => site++p)).length := by
    rw [List.length_map,ha.paths_length,hp.paths_length,length]
  exact ⟨M,first,last,ha,hb,whole,length,
    List.append_inj_left allPaths.symm sameLength,
    List.append_inj_right allPaths.symm sameLength⟩

end Lamping.Lambda
