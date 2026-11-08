import Lamping.Lambda.CreationExterior
namespace Lamping.Lambda.Marked

/-- Binder-lifted substitutions retaining passive old names. -/
def liftMarkedSubN : Nat → (Nat → Marked) → Nat → Marked
  | 0, σ => σ
  | n+1, σ => liftSub (liftMarkedSubN n σ)
 theorem liftMarkedSubN_shift (n : Nat) (σ : Nat → Marked) :
     liftMarkedSubN n (liftSub σ) = liftMarkedSubN (n+1) σ := by
   induction n with
   | zero => rfl
   | succ n ih => exact congrArg liftSub ih

/-- Exact old-tag sources, including a concrete substituted-variable instance.
 A source without a tag does not acquire one from a coincidental redex shape. -/
inductive SubstTraceSource (σ : Nat → Marked) (t : Marked) (r q : Path) : Prop where
  | old : q ∈ tracePositions r t → SubstTraceSource σ t r q
  | inserted {site i tail} : subtermAt t.erase site = some (.var i) → q = site ++ tail →
      tail ∈ tracePositions r (liftMarkedSubN (binderDepth site) σ i) →
      SubstTraceSource σ t r q

namespace SubstTraceSource
 theorem fn (h : SubstTraceSource σ f r q) : SubstTraceSource σ (.app l f a) r (.fn :: q) := by
   cases h with
   | old h => exact .old (by simp [tracePositions, h])
   | inserted hp he ht => exact .inserted (site := .fn :: _) hp (congrArg (List.cons .fn) he) ht
 theorem arg (h : SubstTraceSource σ a r q) : SubstTraceSource σ (.app l f a) r (.arg :: q) := by
   cases h with
   | old h => exact .old (by simp [tracePositions, h])
   | inserted hp he ht => exact .inserted (site := .arg :: _) hp (congrArg (List.cons .arg) he) ht
 theorem body (h : SubstTraceSource (liftSub σ) b r q) : SubstTraceSource σ (.lam b) r (.body :: q) := by
   cases h with
   | old h => exact .old (by simp [tracePositions, h])
   | inserted hp he ht =>
     exact .inserted (site := .body :: _) hp (congrArg (List.cons .body) he)
       (by simpa only [binderDepth, liftMarkedSubN_shift] using ht)
 theorem redBody (h : SubstTraceSource (liftSub σ) b r q) :
     SubstTraceSource σ (.red l b a) r (.fn :: .body :: q) := by
   cases h with
   | old h => exact .old (by simp [tracePositions, h])
   | inserted hp he ht =>
     exact .inserted (site := .fn :: .body :: _) hp
       (congrArg (fun q => Step.fn :: Step.body :: q) he)
       (by simpa only [binderDepth, liftMarkedSubN_shift] using ht)
 theorem redArg (h : SubstTraceSource σ a r q) : SubstTraceSource σ (.red l b a) r (.arg :: q) := by
   cases h with
   | old h => exact .old (by simp [tracePositions, h])
   | inserted hp he ht => exact .inserted (site := .arg :: _) hp (congrArg (List.cons .arg) he) ht
end SubstTraceSource

 theorem subst_trace_source (h : q ∈ tracePositions r (subst σ t)) : SubstTraceSource σ t r q := by
   induction t generalizing σ q with
   | var i => exact .inserted (site := []) (i := i) rfl rfl h
   | lam b ih =>
     cases q with
     | nil => simp [subst, tracePositions] at h
     | cons s q => cases s with
       | fn => simp [subst, tracePositions] at h
       | arg => simp [subst, tracePositions] at h
       | body => exact (ih (by simpa [subst, tracePositions] using h)).body
   | app l f a hf ha =>
     cases q with
     | nil => exact .old (by simpa [subst, tracePositions] using h)
     | cons s q => cases s with
       | body => simp [subst, tracePositions] at h
       | fn => exact (hf (by simpa [subst, tracePositions] using h)).fn
       | arg => exact (ha (by simpa [subst, tracePositions] using h)).arg
   | red l b a hb ha =>
     cases q with
     | nil => exact .old (by simpa [subst, tracePositions] using h)
     | cons s q => cases s with
       | body => simp [subst, tracePositions] at h
       | arg => exact (ha (by simpa [subst, tracePositions] using h)).redArg
       | fn => cases q with
         | nil => simp [subst, tracePositions] at h
         | cons s q => cases s with
           | fn => simp [subst, tracePositions] at h
           | arg => simp [subst, tracePositions] at h
           | body => exact (hb (by simpa [subst, tracePositions] using h)).redBody

/-- Every old body occurrence keeps its old name at the same position after
 substitution. Inserted instances may supply additional occurrences. -/
 theorem trace_subst_preserve (h : q ∈ tracePositions r t) (σ : Nat → Marked) :
     q ∈ tracePositions r (subst σ t) := by
   induction t generalizing σ q with
   | var => simp [tracePositions] at h
   | lam b ih =>
     cases q with
     | nil => simp [tracePositions] at h
     | cons s q => cases s with
       | fn => simp [tracePositions] at h
       | arg => simp [tracePositions] at h
       | body => simpa [subst, tracePositions] using ih (by simpa [tracePositions] using h) (liftSub σ)
   | app l f a hf ha =>
     cases q with
     | nil => simpa [subst, tracePositions] using h
     | cons s q => cases s with
       | body => simp [tracePositions] at h
       | fn => simpa [subst, tracePositions] using hf (by simpa [tracePositions] using h) σ
       | arg => simpa [subst, tracePositions] using ha (by simpa [tracePositions] using h) σ
   | red l b a hb ha =>
     cases q with
     | nil => simpa [subst, tracePositions] using h
     | cons s q => cases s with
       | body => simp [tracePositions] at h
       | arg => simpa [subst, tracePositions] using ha (by simpa [tracePositions] using h) σ
       | fn => cases q with
         | nil => simp [tracePositions] at h
         | cons s q => cases s with
           | fn => simp [tracePositions] at h
           | arg => simp [tracePositions] at h
           | body => simpa [subst, tracePositions] using hb (by simpa [tracePositions] using h) (liftSub σ)

/-- Conversely, a concrete tag in a substituted variable instance really
 occurs at the concatenated target position. This supplies actual transport
 for the inserted-source branch of subst_trace_source. -/
 theorem trace_subst_insert (hp : subtermAt t.erase site = some (.var i))
     (ht : tail ∈ tracePositions r (liftMarkedSubN (binderDepth site) σ i)) :
     site ++ tail ∈ tracePositions r (subst σ t) := by
   induction t generalizing σ site with
   | var j =>
     cases site with
     | nil =>
       have hi : j = i := Term.var.inj (Option.some.inj hp)
       cases hi
       exact ht
     | cons s site => cases s <;> simp [erase, subtermAt] at hp
   | lam b ih =>
     cases site with
     | nil => cases hp
     | cons s site => cases s with
       | fn => simp [erase, subtermAt] at hp
       | arg => simp [erase, subtermAt] at hp
       | body =>
         have ht' := ht
         simp only [binderDepth] at ht'
         rw [← liftMarkedSubN_shift] at ht'
         have hh := ih hp ht'
         simp [subst, tracePositions, hh]
   | app l f a hf ha =>
     cases site with
     | nil => cases hp
     | cons s site => cases s with
       | body => simp [erase, subtermAt] at hp
       | fn => have hh := hf hp ht; simp [subst, tracePositions, hh]
       | arg => have hh := ha hp ht; simp [subst, tracePositions, hh]
   | red l b a hb ha =>
     cases site with
     | nil => cases hp
     | cons s site => cases s with
       | body => simp [erase, subtermAt] at hp
       | arg => have hh := ha hp ht; simp [subst, tracePositions, hh]
       | fn => cases site with
         | nil => cases hp
         | cons s site => cases s with
           | fn => simp [erase, subtermAt] at hp
           | arg => simp [erase, subtermAt] at hp
           | body =>
             have ht' := ht
             simp only [binderDepth] at ht'
             rw [← liftMarkedSubN_shift] at ht'
             have hh := hb hp ht'
             simp [subst, tracePositions, hh]

 theorem subst_trace_iff_source : q ∈ tracePositions r (subst σ t) ↔ SubstTraceSource σ t r q := by
   constructor
   · exact subst_trace_source
   · intro h
     cases h with
     | old h => exact trace_subst_preserve h σ
     | inserted hp he ht => rw [he]; exact trace_subst_insert hp ht
end Lamping.Lambda.Marked



