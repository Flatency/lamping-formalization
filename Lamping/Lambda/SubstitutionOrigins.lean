import Lamping.Lambda.ArgumentCopies
namespace Lamping.Lambda

/-- Exhaustive syntax sources for a redex after substitution. The second case
 is genuine creation at an application whose function was a variable; the
 third case enters one concrete substituted-variable instance. -/
inductive SubstRedexSource (σ : Nat → Term) (t : Term) (q : Path) : Prop where
  | old : (∃ z, subtermAt t q = some z ∧ IsRedex z) → SubstRedexSource σ t q
  | headVariable {i a} : subtermAt t q = some (.app (.var i) a) →
      (∃ b, liftSubN (binderDepth q) σ i = .lam b) → SubstRedexSource σ t q
  | inserted {site i tail} : subtermAt t site = some (.var i) → q = site ++ tail →
      (∃ z, subtermAt (liftSubN (binderDepth site) σ i) tail = some z ∧ IsRedex z) →
      SubstRedexSource σ t q

namespace SubstRedexSource
 theorem fn (h : SubstRedexSource σ f q) : SubstRedexSource σ (.app f a) (.fn :: q) := by
   cases h with
   | old h => exact .old h
   | headVariable hp hh => exact .headVariable hp hh
   | inserted hp he hs => exact .inserted (site := .fn :: _) hp (congrArg (List.cons .fn) he) hs
 theorem arg (h : SubstRedexSource σ a q) : SubstRedexSource σ (.app f a) (.arg :: q) := by
   cases h with
   | old h => exact .old h
   | headVariable hp hh => exact .headVariable hp hh
   | inserted hp he hs => exact .inserted (site := .arg :: _) hp (congrArg (List.cons .arg) he) hs
 theorem body (h : SubstRedexSource (liftSub σ) b q) : SubstRedexSource σ (.lam b) (.body :: q) := by
   cases h with
   | old h => exact .old h
   | headVariable hp hh =>
     exact .headVariable hp (by simpa only [binderDepth, liftSubN_shift] using hh)
   | inserted hp he hs =>
     exact .inserted (site := .body :: _) hp (congrArg (List.cons .body) he)
       (by simpa only [binderDepth, liftSubN_shift] using hs)
end SubstRedexSource

/-- Concrete origin classification for every actual redex in a substituted
 term. It does not assume that a new redex has an old residual ancestor. -/
 theorem subst_redex_source (hr : ∃ z, subtermAt (subst σ t) q = some z ∧ IsRedex z) :
     SubstRedexSource σ t q := by
   induction t generalizing σ q with
   | var i => exact .inserted (site := []) (i := i) rfl rfl hr
   | lam b ih =>
     cases q with
     | nil => simp [subst, subtermAt, IsRedex] at hr
     | cons s q => cases s with
       | fn => simp [subst, subtermAt] at hr
       | arg => simp [subst, subtermAt] at hr
       | body => exact (ih hr).body
   | app f a hf ha =>
     cases q with
     | cons s q => cases s with
       | fn => exact (hf hr).fn
       | arg => exact (ha hr).arg
       | body => simp [subst, subtermAt] at hr
     | nil =>
       cases f with
       | lam b => exact .old ⟨_, rfl, trivial⟩
       | app f b => simp [subst, subtermAt, IsRedex] at hr
       | var i =>
         cases hs : σ i with
         | var j => simp [subst, subtermAt, hs, IsRedex] at hr
         | app f b => simp [subst, subtermAt, hs, IsRedex] at hr
         | lam b => exact .headVariable rfl ⟨b, hs⟩
end Lamping.Lambda

