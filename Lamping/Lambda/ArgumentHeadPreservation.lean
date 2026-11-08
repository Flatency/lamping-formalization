import Lamping.Lambda.ParallelPrefixScope
import Lamping.Lambda.ContextualHistories
import Lamping.Lambda.ProjectionSelections
namespace Lamping.Lambda

/-- Reflect actual ordinary contractions inside one syntax child, keeping
the surrounding constructor and the untouched child literally fixed. -/
theorem SyntaxFrame.history_reflect (C : SyntaxFrame)
    (h : BetaHistory (ps.map (C.edge::·)) (C.plug a) u) :
    ∃ b, BetaHistory ps a b ∧ u=C.plug b := by
  induction ps generalizing a u with
  | nil => cases h; exact ⟨a,.nil _,rfl⟩
  | cons p ps ih =>
    cases h with
    | cons first rest =>
      obtain ⟨b,localStep,shape⟩ := C.beta_reflect first
      subst shape
      obtain ⟨c,localTail,finish⟩ := ih rest
      exact ⟨c,.cons localStep localTail,finish⟩

/-- Reducing only inside the original argument keeps the original lambda
body unchanged at the redex site, even in an arbitrary enclosing context. -/
theorem ParallelHistory.argument_head_preserved (σ : ParallelHistory t v)
    (lookup : subtermAt t p=some (.app (.lam b) a))
    (inside : Internal (p++[.arg]) σ) :
    ∃ (a' : Term) (ps : List Path),
      subtermAt v p=some (.app (.lam b) a') ∧ BetaHistory ps a a' ∧
      σ.derivation.paths=ps.map (fun q => (p++[.arg])++q) := by
  obtain ⟨ps,paths⟩ := inside.local_paths
  have history : BetaHistory ((ps.map (Step.arg::·)).map (fun q => p++q)) t v := by
    have actual := σ.derivation.valid
    rw [paths] at actual
    simpa only [List.map_map,Function.comp_def,List.append_assoc,List.singleton_append] using
      actual
  obtain ⟨localTarget,localHistory,targetLookup⟩ := history.prefix_reflect lookup
  obtain ⟨a',argumentHistory,shape⟩ := (SyntaxFrame.arg (.lam b)).history_reflect localHistory
  rw [shape] at targetLookup
  exact ⟨a',ps,by simpa only [SyntaxFrame.plug] using targetLookup,argumentHistory,paths⟩

private theorem not_inside_argument (p : Path) : ¬∃ q, p=(p++[.arg])++q := by
  rintro ⟨q,hq⟩
  have lengths := congrArg List.length hq
  simp only [List.length_append,List.length_singleton] at lengths
  omega

/-- The original root redex has exactly its unchanged-position residual
through every actual internal argument history. -/
theorem ParallelHistory.argument_root_residual_iff (σ : ParallelHistory t v)
    (R : BetaAt t p u) (inside : Internal (p++[.arg]) σ) (z : RedexOcc v) :
    σ.derivation.Residual ⟨p,R.redex⟩ z ↔ z.val=p := by
  have h := σ.residual_outside_internal inside ⟨p,R.redex⟩ z (not_inside_argument p)
  exact h.trans eq_comm

/-- Reconstruct the actual residual beta with the same body after any
original-argument prefix. No body-preservation certificate is assumed. -/
theorem ParallelHistory.argument_root_exists (σ : ParallelHistory t v)
    (lookup : subtermAt t p=some (.app (.lam b) a))
    (inside : Internal (p++[.arg]) σ) :
    ∃ a' w, ∃ _R' : BetaAt v p w,
      subtermAt v p=some (.app (.lam b) a') := by
  obtain ⟨a',_,shape,_,_⟩ := σ.argument_head_preserved lookup inside
  have root : BetaAt (.app (.lam b) a') [] (contract b a') := ⟨b,a',rfl,rfl⟩
  obtain ⟨w,R',_,_⟩ := root.prefix_lift shape
  exact ⟨a',w,by simpa only [List.append_nil] using R',shape⟩

end Lamping.Lambda
