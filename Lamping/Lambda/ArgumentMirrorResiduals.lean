import Lamping.Lambda.RenameResiduals
import Lamping.Lambda.PointedRuns
namespace Lamping.Lambda

theorem Derivation.region_rename_target
    (h : Derivation t u) (k : Derivation t' u')
    (lookup : subtermAt t pre = some a)
    (lookup' : subtermAt t' pre' = some (rename ρ a))
    (localPaths : List Path)
    (paths : h.paths = localPaths.map (fun q => pre ++ q))
    (paths' : k.paths = localPaths.map (fun q => pre' ++ q)) :
    ∃ b, subtermAt u pre = some b ∧ subtermAt u' pre' = some (rename ρ b) := by
  have hh := h.valid
  rw [paths] at hh
  obtain ⟨b, localHistory, output⟩ := hh.prefix_reflect lookup
  have kk := k.valid
  rw [paths'] at kk
  obtain ⟨b', copied, output'⟩ := kk.prefix_reflect lookup'
  have same := copied.deterministic (localHistory.rename ρ)
  exact ⟨b, output, same ▸ output'⟩

/-- Two actual histories in corresponding renamed subtrees transport the
 same old local redex identities. Local target terms are recovered from the
 histories, so no endpoint mirroring is assumed. -/
theorem Derivation.region_rename_residual_iff
    (h : Derivation t u) (k : Derivation t' u')
    (lookup : subtermAt t pre = some a)
    (lookup' : subtermAt t' pre' = some (rename ρ a))
    (localPaths : List Path)
    (paths : h.paths = localPaths.map (fun q => pre ++ q))
    (paths' : k.paths = localPaths.map (fun q => pre' ++ q))
    (r : RedexOcc t) (s : RedexOcc u) (r' : RedexOcc t') (s' : RedexOcc u')
    (source : r.val = pre ++ localR) (target : s.val = pre ++ localS)
    (source' : r'.val = pre' ++ localR) (target' : s'.val = pre' ++ localS) :
    k.Residual r' s' ↔ h.Residual r s := by
  have hh := h.valid
  rw [paths] at hh
  obtain ⟨b, localHistory, output⟩ := hh.prefix_reflect lookup
  have kk := k.valid
  rw [paths'] at kk
  obtain ⟨b', copied, output'⟩ := kk.prefix_reflect lookup'
  have same := copied.deterministic (localHistory.rename ρ)
  cases same
  let original : Derivation a b := ⟨localPaths, localHistory⟩
  let mirrored : Derivation (rename ρ a) (rename ρ b) := ⟨localPaths, copied⟩
  let lr : RedexOcc a := ⟨localR, by
    have hr := r.property
    rw [source, subtermAt_append, lookup, Option.bind_some] at hr
    exact hr⟩
  let ls : RedexOcc b := ⟨localS, by
    have hs := s.property
    rw [target, subtermAt_append, output, Option.bind_some] at hs
    exact hs⟩
  let lr' : RedexOcc (rename ρ a) := ⟨localR, by
    have hr := r'.property
    rw [source', subtermAt_append, lookup', Option.bind_some] at hr
    exact hr⟩
  let ls' : RedexOcc (rename ρ b) := ⟨localS, by
    have hs := s'.property
    rw [target', subtermAt_append, output', Option.bind_some] at hs
    exact hs⟩
  exact (mirrored.prefix_residual_iff k lookup' paths' lr' ls' r' s' source' target').trans
    ((original.rename_residual_iff mirrored rfl lr ls lr' ls' rfl rfl).trans
      (original.prefix_residual_iff h lookup paths lr ls r s source target).symm)

end Lamping.Lambda
