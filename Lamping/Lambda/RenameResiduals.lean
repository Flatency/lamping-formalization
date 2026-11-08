import Lamping.Lambda.RootResidualPaths
import Lamping.Lambda.ContextualHistories
import Lamping.Lambda.ContextualResiduals
namespace Lamping.Lambda.Marked

theorem markAt_rename (F : List Path) (t : Term) (ρ : Nat → Nat) (pre : Path) :
    markAt F (Lambda.rename ρ t) pre = rename ρ (markAt F t pre) := by
  induction t generalizing ρ pre with
  | var => rfl
  | lam b ih => simp only [Lambda.rename, markAt, rename, ih]
  | app f a hf ha =>
    cases f with
    | var => simp only [Lambda.rename, markAt, rename, ha]
    | app f b =>
      have hh := hf ρ (pre ++ [.fn])
      simp only [Lambda.rename] at hh
      simp only [Lambda.rename, markAt, rename, ha]
      rw [hh]
    | lam b =>
      have hb := hf ρ (pre ++ [.fn])
      simp only [Lambda.rename, markAt, rename, Marked.lam.injEq] at hb
      simp only [Lambda.rename, markAt, hb, ha]
      split <;> rfl

theorem ReductionAt.rename (h : ReductionAt p t u) (ρ : Nat → Nat) :
    ReductionAt p (rename ρ t) (rename ρ u) := by
  induction h generalizing ρ with
  | appRoot l b a => simpa only [Marked.rename, rename_contract] using
      ReductionAt.appRoot l (Marked.rename (liftRen ρ) b) (Marked.rename ρ a)
  | redRoot l b a => simpa only [Marked.rename, rename_contract] using
      ReductionAt.redRoot l (Marked.rename (liftRen ρ) b) (Marked.rename ρ a)
  | lam h ih => exact .lam (ih (liftRen ρ))
  | appL h ih => exact .appL (ih ρ)
  | appR h ih => exact .appR (ih ρ)
  | redL h ih => exact .redL (ih (liftRen ρ))
  | redR h ih => exact .redR (ih ρ)

theorem History.rename (h : History ps t u) (ρ : Nat → Nat) :
    History ps (rename ρ t) (rename ρ u) := by
  induction h with
  | nil => exact .nil _
  | cons h hs ih => exact .cons (h.rename ρ) ih

end Lamping.Lambda.Marked
namespace Lamping.Lambda

theorem BetaHistory.rename (h : BetaHistory ps t u) (ρ : Nat → Nat) :
    BetaHistory ps (Lambda.rename ρ t) (Lambda.rename ρ u) := by
  induction h with
  | nil => exact .nil _
  | cons h hs ih => exact .cons (h.rename ρ) ih

/-- Renaming variables preserves old-redex identities in both directions
 along the same actual contraction schedule. No injectivity is needed. -/
theorem Derivation.rename_residual_iff (h : Derivation t u)
    (k : Derivation (rename ρ t) (rename ρ u)) (paths : h.paths = k.paths)
    (r : RedexOcc t) (s : RedexOcc u)
    (r' : RedexOcc (rename ρ t)) (s' : RedexOcc (rename ρ u))
    (source : r.val = r'.val) (target : s.val = s'.val) :
    k.Residual r' s' ↔ h.Residual r s := by
  obtain ⟨tracked, hh, he⟩ := h.tracked
  have renamed : Marked.History k.paths (Marked.mark [] (rename ρ t))
      (Marked.rename ρ tracked) := by
    rw [← paths]
    simpa only [Marked.mark, Marked.markAt_rename] using hh.rename ρ
  constructor
  · rintro ⟨v, hv, _, hs⟩
    have eq := hv.deterministic renamed
    rw [eq, Marked.trace_rename, ← source, ← target] at hs
    exact ⟨tracked, hh, he, hs⟩
  · rintro ⟨v, hv, _, hs⟩
    have eq := hv.deterministic hh
    rw [eq] at hs
    refine ⟨Marked.rename ρ tracked, renamed, ?_, ?_⟩
    · rw [Marked.erase_rename, he]
    · simpa only [Marked.trace_rename, ← source, ← target] using hs

end Lamping.Lambda
