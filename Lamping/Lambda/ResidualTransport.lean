import Lamping.Lambda.Histories
namespace Lamping.Lambda.Marked

/-- Forget only the selected bit, never the old names. This is distinct from
 erasing all annotations and from initializing the endpoint again. -/
def passive : Marked → Marked
  | .var i => .var i
  | .lam b => .lam (passive b)
  | .app l f a => .app l (passive f) (passive a)
  | .red l b a => .app l (.lam (passive b)) (passive a)

 theorem passive_rename (ρ) (t : Marked) : passive (rename ρ t) = rename ρ (passive t) := by
   induction t generalizing ρ with
   | var => rfl
   | lam b ih => simp [rename, passive, ih]
   | app l f a hf ha => simp [rename, passive, hf, ha]
   | red l b a hb ha => simp [rename, passive, hb, ha]
 theorem passive_subst (σ) (t : Marked) :
     passive (subst σ t) = subst (fun i => passive (σ i)) (passive t) := by
   induction t generalizing σ with
   | var => rfl
   | app l f a hf ha => simp [subst, passive, hf, ha]
   | lam b ih =>
     simp only [subst, passive, ih]
     congr 1; congr 1; funext i
     cases i <;> simp [liftSub, passive, passive_rename]
   | red l b a hb ha =>
     simp only [subst, passive, hb, ha]
     congr 1
     congr 1
     congr 1
     funext i
     cases i <;> simp [liftSub, passive, passive_rename]
 theorem passive_contract (b a : Marked) :
     passive (contract b a) = contract (passive b) (passive a) := by
   simp only [contract, passive_subst]
   congr 1; funext i; cases i <;> rfl
 theorem passive_erase (t : Marked) : (passive t).erase = t.erase := by
   induction t <;> simp_all [passive, erase]
 theorem passive_trace (r : Path) (t : Marked) :
     tracePositions r (passive t) = tracePositions r t := by
   induction t with
   | var => rfl
   | lam b ih => simp [passive, tracePositions, ih]
   | app l f a hf ha => simp [passive, tracePositions, hf, ha]
   | red l b a hb ha => simp [passive, tracePositions, hb, ha, List.map_map, Function.comp_def]
 theorem passive_markAt (F : List Path) (t : Term) (p : Path) :
     passive (markAt F t p) = markAt [] t p := by
   induction t generalizing p with
   | var => rfl
   | lam b ih => simp [markAt, passive, ih]
   | app f a hf ha =>
     cases f with
     | var i => simp [markAt, passive, ha]
     | app f b => simp [markAt, passive, ha, hf]
     | lam b =>
       have hb (p : Path) : passive (markAt F b (p ++ [.body])) = markAt [] b (p ++ [.body]) := by
         have hh := hf p
         simpa only [markAt, passive, Marked.lam.injEq] using hh
       simp only [markAt]
       have hb' := hb (p ++ [.fn])
       simp only [List.append_assoc, List.cons_append, List.nil_append] at hb'
       split <;> simp [passive, hb', ha]
 theorem passive_mark (F : List Path) (t : Term) : passive (mark F t) = mark [] t :=
   passive_markAt F t []
 theorem ReductionAt.passive (h : ReductionAt p t u) : ReductionAt p t.passive u.passive := by
   induction h with
   | appRoot l b a => simpa only [Marked.passive, passive_contract] using ReductionAt.appRoot l b.passive a.passive
   | redRoot l b a => simpa only [Marked.passive, passive_contract] using ReductionAt.appRoot l b.passive a.passive
   | lam h ih => exact .lam ih
   | appL h ih => exact .appL ih
   | appR h ih => exact .appR ih
   | redL h ih => exact .appL (.lam ih)
   | redR h ih => exact .appR ih
 theorem History.passive (h : History ps t u) : History ps t.passive u.passive := by
   induction h with
   | nil => exact .nil _
   | cons h hs ih => exact .cons h.passive ih
end Lamping.Lambda.Marked

namespace Lamping.Lambda.ParallelStep
 theorem tracked (h : ParallelStep F t u) :
     Marked.History h.paths (Marked.mark [] t) h.markedTarget.passive := by
   have hh := ((Marked.completeOld_iff F t).mp h.complete).1.general.passive
   rw [Marked.passive_mark] at hh
   exact hh
 theorem residual_iff (h : ParallelStep F t u) (r : RedexOcc t) (s : RedexOcc u) :
     h.derivation.Residual r s ↔ s.val ∈ Marked.tracePositions r.val h.markedTarget := by
   constructor
   · rintro ⟨v, hv, _, hs⟩
     have he := hv.deterministic h.tracked
     subst v
     simpa only [Marked.passive_trace] using hs
   · intro hs
     exact ⟨h.markedTarget.passive, h.tracked,
       (Marked.passive_erase _).trans h.target_eq,
       by simpa only [Marked.passive_trace] using hs⟩
 theorem residual_independent (h k : ParallelStep F t u) (r : RedexOcc t) (s : RedexOcc u) :
     h.derivation.Residual r s ↔ k.derivation.Residual r s := by
   rw [h.residual_iff, k.residual_iff, h.old_residual k r]
end Lamping.Lambda.ParallelStep


