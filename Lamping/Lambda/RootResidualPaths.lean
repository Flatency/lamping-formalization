import Lamping.Lambda.ParallelMovesResidual
import Lamping.Lambda.SubstitutionTraceOrigins
namespace Lamping.Lambda.Marked

 theorem trace_rename (ρ : Nat → Nat) (t : Marked) (r : Path) :
     tracePositions r (rename ρ t) = tracePositions r t := by
   induction t generalizing ρ with
   | var => rfl
   | lam b ih => simp [rename, tracePositions, ih]
   | app l f a hf ha => simp [rename, tracePositions, hf, ha]
   | red l b a hb ha => simp [rename, tracePositions, hb, ha]

 theorem liftMarkedSubN_self (n : Nat) (σ : Nat → Marked) :
     liftMarkedSubN n σ n = rename (fun i => i + n) (σ 0) := by
   induction n with
   | zero => exact (rename_id _).symm
   | succ n ih =>
     simp only [liftMarkedSubN, liftSub, ih, rename_comp]
     apply rename_congr
     intro i
     change Nat.succ (i + n) = i + (n + 1)
     omega
/-- A lifted single substitution has old names only at the removed binder;
 all other variables remain variables and carry no old application tag. -/
 theorem trace_lift_single (n i : Nat) (a : Marked) (r : Path) :
     tracePositions r (liftMarkedSubN n (single a) i) =
       if i = n then tracePositions r a else [] := by
   induction n generalizing i with
   | zero =>
     cases i with
     | zero => exact (if_pos rfl).symm
     | succ i => exact (if_neg (Nat.succ_ne_zero i)).symm
   | succ n ih =>
     cases i with
     | zero => exact (if_neg (Nat.zero_ne_add_one n)).symm
     | succ i =>
       change tracePositions r (rename Nat.succ _) = _
       rw [trace_rename, ih]
       by_cases hi : i = n
       · rw [if_pos hi, if_pos (congrArg Nat.succ hi)]
       · rw [if_neg hi, if_neg (fun hs => hi (Nat.succ.inj hs))]

/-- Exact root-beta old-name sources; freshly created redex shape is excluded. -/
 theorem contract_trace_iff : q ∈ tracePositions r (contract b a) ↔
     q ∈ tracePositions r b ∨
       ∃ site tail, subtermAt b.erase site = some (.var (binderDepth site)) ∧
         q = site ++ tail ∧ tail ∈ tracePositions r a := by
   rw [contract, subst_trace_iff_source]
   constructor
   · intro h
     cases h with
     | old h => exact .inl h
     | @inserted site i tail hp he ht =>
       rw [trace_lift_single] at ht
       split at ht
       next hi => subst i; exact .inr ⟨site, tail, hp, he, ht⟩
       next => simp at ht
   · intro h
     rcases h with h | ⟨site, tail, hp, he, ht⟩
     · exact .old h
     · exact .inserted hp he (by simpa [trace_lift_single] using ht)
end Lamping.Lambda.Marked

namespace Lamping.Lambda
/-- Ordinary root contraction, retaining the actual single path. -/
def rootContraction (b a : Term) : Derivation (.app (.lam b) a) (contract b a) :=
  ⟨[[]], .cons ⟨b, a, rfl, rfl⟩ (.nil _)⟩

 theorem rootContraction_eq_single (h : BetaAt (.app (.lam b) a) [] (contract b a)) :
     rootContraction b a = (singleContraction h).derivation := by
   apply Derivation.ext
   rfl

/-- An old body redex keeps its name and its body-local position through beta. -/
 theorem root_body_residual (r : RedexOcc (.app (.lam b) a))
     (s : RedexOcc (contract b a)) (hp : r.val = [.fn, .body] ++ s.val) :
     (rootContraction b a).Residual r s := by
   let mb := Marked.markAt [] b [.fn, .body]
   let ma := Marked.markAt [] a [.arg]
   have ht : s.val ∈ Marked.tracePositions r.val mb := by
     apply (Marked.trace_markAt [] b r.val [.fn, .body] s.val).mpr
     refine ⟨hp, ?_⟩
     have hr := r.property
     rw [hp] at hr
     simpa [mem_redexPositions, subtermAt] using hr
   refine ⟨Marked.contract mb ma, ?_, ?_, Marked.trace_subst_preserve ht _⟩
   · exact .cons (by simpa [Marked.mark, Marked.markAt, mb, ma] using
       Marked.ReductionAt.appRoot [[]] mb ma) (.nil _)
   · simp [Marked.erase_contract, mb, ma, Marked.erase_markAt]

/-- Each concrete bound-variable instance transports every old argument name
 to its concatenated copy position, including instances below binders. -/
 theorem root_argument_residual (site q : Path)
     (ho : subtermAt b site = some (.var (binderDepth site)))
     (r : RedexOcc (.app (.lam b) a)) (s : RedexOcc (contract b a))
     (hr : r.val = [.arg] ++ q) (hs : s.val = site ++ q) :
     (rootContraction b a).Residual r s := by
   let mb := Marked.markAt [] b [.fn, .body]
   let ma := Marked.markAt [] a [.arg]
   have ht : q ∈ Marked.tracePositions r.val ma := by
     apply (Marked.trace_markAt [] a r.val [.arg] q).mpr
     refine ⟨hr, ?_⟩
     have hh := r.property
     rw [hr] at hh
     simpa [mem_redexPositions, subtermAt] using hh
   have hi : q ∈ Marked.tracePositions r.val
       (Marked.liftMarkedSubN (binderDepth site) (Marked.single ma) (binderDepth site)) := by
     rw [Marked.liftMarkedSubN_self, Marked.trace_rename]
     exact ht
   have hcopy := Marked.trace_subst_insert (t := mb) (σ := Marked.single ma)
     (by simpa [mb, Marked.erase_markAt] using ho) hi
   refine ⟨Marked.contract mb ma, ?_, ?_, ?_⟩
   · exact .cons (by simpa [Marked.mark, Marked.markAt, mb, ma] using
       Marked.ReductionAt.appRoot [[]] mb ma) (.nil _)
   · simp [Marked.erase_contract, mb, ma, Marked.erase_markAt]
   · rw [hs]
     exact hcopy
/-- Exhaustive actual initial-ancestor paths for a root beta step. -/
 theorem root_residual_iff (r : RedexOcc (.app (.lam b) a))
     (s : RedexOcc (contract b a)) :
     (rootContraction b a).Residual r s ↔
       (r.val = [.fn, .body] ++ s.val ∧ s.val ∈ redexPositions b) ∨
       ∃ site tail, subtermAt b site = some (.var (binderDepth site)) ∧
         s.val = site ++ tail ∧ r.val = [.arg] ++ tail ∧ tail ∈ redexPositions a := by
   let mb := Marked.markAt [] b [.fn, .body]
   let ma := Marked.markAt [] a [.arg]
   have hh : Marked.History (rootContraction b a).paths
       (Marked.mark [] (.app (.lam b) a)) (Marked.contract mb ma) :=
     .cons (by simpa [Marked.mark, Marked.markAt, mb, ma] using
       Marked.ReductionAt.appRoot [[]] mb ma) (.nil _)
   rw [Derivation.residual_iff_tracking _ hh, Marked.contract_trace_iff]
   simp only [mb, ma, Marked.trace_markAt, Marked.erase_markAt]
end Lamping.Lambda





