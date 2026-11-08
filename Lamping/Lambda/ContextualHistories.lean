import Lamping.Lambda.ContextualBeta
import Lamping.Lambda.AtomicHistories
namespace Lamping.Lambda
 theorem BetaHistory.prefix_lift (h : BetaHistory ps a b) (hp : subtermAt t site = some a) :
     ∃ u, BetaHistory (ps.map (fun q => site ++ q)) t u ∧ subtermAt u site = some b := by
   induction h generalizing t with
   | nil a => exact ⟨t, .nil _, hp⟩
   | cons hb hs ih =>
     obtain ⟨v, hv, hloc, _⟩ := hb.prefix_lift hp
     obtain ⟨u, hu, huLoc⟩ := ih hloc
     exact ⟨u, .cons hv hu, huLoc⟩

 theorem BetaHistory.prefix_reflect (h : BetaHistory (ps.map (fun q => site ++ q)) t u)
     (hp : subtermAt t site = some a) :
     ∃ b, BetaHistory ps a b ∧ subtermAt u site = some b := by
   induction ps generalizing t a with
   | nil => cases h; exact ⟨a, .nil _, hp⟩
   | cons q qs ih =>
     cases h with
     | cons hb hs =>
       obtain ⟨b, hlocal, _, hbLoc⟩ := hb.prefix_reflect hp
       obtain ⟨c, hc, hcLoc⟩ := ih hs hbLoc
       exact ⟨c, .cons hlocal hc, hcLoc⟩

 theorem BetaHistory.rename_reflect (h : BetaHistory ps (rename ρ t) u') :
     ∃ u, BetaHistory ps t u ∧ rename ρ u = u' := by
   induction ps generalizing t u' with
   | nil => cases h; exact ⟨t, .nil _, rfl⟩
   | cons p ps ih =>
     cases h with
     | cons hb hs =>
       obtain ⟨v, hv, he⟩ := hb.rename_reflect
       rw [← he] at hs
       obtain ⟨u, hu, heu⟩ := ih hs
       exact ⟨u, .cons hv hu, heu⟩

 theorem Internal.local_paths (hi : Internal site σ) :
     ∃ qs : List Path, σ.derivation.paths = qs.map (fun q => site ++ q) := by
   have aux (ps : List Path) (h : ∀ q ∈ ps, ∃ s, q = site ++ s) :
       ∃ qs : List Path, ps = qs.map (fun q => site ++ q) := by
     induction ps with
     | nil => exact ⟨[], rfl⟩
     | cons p ps ih =>
       obtain ⟨q, hq⟩ := h p (by simp)
       obtain ⟨qs, hqs⟩ := ih (by intro r hr; exact h r (by simp [hr]))
       exact ⟨q :: qs, by simp [hq, hqs]⟩
   exact aux _ hi

 theorem Internal.extract {σ : ParallelHistory t u} (hi : Internal site σ) (hp : subtermAt t site = some a) :
     ∃ (qs : List Path) (b : Term),
       σ.derivation.paths = qs.map (fun q => site ++ q) ∧
       BetaHistory qs a b ∧ subtermAt u site = some b := by
   obtain ⟨qs, hqs⟩ := hi.local_paths
   have hh := σ.derivation.valid
   rw [hqs] at hh
   obtain ⟨b, hb, hp'⟩ := hh.prefix_reflect hp
   exact ⟨qs, b, hqs, hb, hp'⟩
end Lamping.Lambda

