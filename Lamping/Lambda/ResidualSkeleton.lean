import Lamping.Lambda.ParallelDevelopment
namespace Lamping.Lambda.Marked
/-- Keep exactly the selected constructors, forgetting all passive old names. -/
def skeleton : Marked → Marked
  | .var i => .var i
  | .lam b => .lam b.skeleton
  | .app _ f a => .app [] f.skeleton a.skeleton
  | .red _ b a => .red [] b.skeleton a.skeleton
 theorem skeleton_erase (t : Marked) : t.skeleton.erase = t.erase := by
   induction t <;> simp_all [skeleton, erase]
 theorem skeleton_active (t : Marked) : activePositions t.skeleton = activePositions t := by
   induction t <;> simp_all [skeleton, activePositions]
 theorem skeleton_rename (ρ) (t : Marked) : skeleton (rename ρ t) = rename ρ t.skeleton := by
   induction t generalizing ρ <;> simp_all [skeleton, rename]
 theorem skeleton_subst (σ) (t : Marked) :
     skeleton (subst σ t) = subst (fun i => skeleton (σ i)) t.skeleton := by
   induction t generalizing σ with
   | var => rfl
   | app l f a hf ha => simp [skeleton, subst, hf, ha]
   | lam b ih =>
     simp only [skeleton, subst, ih]
     congr 1; congr 1; funext i
     cases i <;> simp [liftSub, skeleton, skeleton_rename]
   | red l b a hb ha =>
     simp only [skeleton, subst, hb, ha]
     congr 1; congr 1; funext i
     cases i <;> simp [liftSub, skeleton, skeleton_rename]
 theorem skeleton_contract (b a : Marked) : (contract b a).skeleton = contract b.skeleton a.skeleton := by
   simp only [contract, skeleton_subst]
   congr 1; funext i; cases i <;> rfl
 theorem ReductionAt.skeleton (h : ReductionAt p t u) : ReductionAt p t.skeleton u.skeleton := by
   induction h with
   | appRoot l b a => simpa only [Marked.skeleton, skeleton_contract] using ReductionAt.appRoot [] b.skeleton a.skeleton
   | redRoot l b a => simpa only [Marked.skeleton, skeleton_contract] using ReductionAt.redRoot [] b.skeleton a.skeleton
   | lam h ih => exact .lam ih
   | appL h ih => exact .appL ih
   | appR h ih => exact .appR ih
   | redL h ih => exact .redL ih
   | redR h ih => exact .redR ih

 theorem skeleton_of_shape (he : t.erase = u.erase)
     (ha : ∀ p, p ∈ activePositions t ↔ p ∈ activePositions u) : t.skeleton = u.skeleton := by
   induction t generalizing u with
   | var i =>
     cases u <;> simp only [erase, Term.var.injEq, reduceCtorEq] at he
     cases he; rfl
   | lam b ih =>
     cases u with
     | var => cases he
     | app => cases he
     | red => cases he
     | lam c =>
       apply congrArg Marked.lam
       apply ih (Term.lam.inj he)
       intro p; simpa [activePositions] using ha (.body :: p)
   | app l f a hf hx =>
     cases u with
     | var => cases he
     | lam => cases he
     | red l' b x =>
       have hh := (ha []).mpr (by simp [activePositions])
       simp [activePositions] at hh
     | app l' g b =>
       obtain ⟨hfg, hab⟩ := Term.app.inj he
       have hF : f.skeleton = g.skeleton := hf hfg (by intro p; simpa [activePositions] using ha (.fn :: p))
       have hA : a.skeleton = b.skeleton := hx hab (by intro p; simpa [activePositions] using ha (.arg :: p))
       simp only [skeleton, hF, hA]
   | red l b a hb hx =>
     cases u with
     | var => cases he
     | lam => cases he
     | app l' f x =>
       have hh := (ha []).mp (by simp [activePositions])
       simp [activePositions] at hh
     | red l' c x =>
       obtain ⟨hbc, hax⟩ := Term.app.inj he
       have hB : b.skeleton = c.skeleton := hb (Term.lam.inj hbc)
         (by intro p; simpa [activePositions] using ha (.fn :: .body :: p))
       have hA : a.skeleton = x.skeleton := hx hax (by intro p; simpa [activePositions] using ha (.arg :: p))
       simp only [skeleton, hB, hA]

 theorem RelativeHistory.lift_skeleton (h : RelativeHistory ps t u)
     (he : t.skeleton = v.skeleton) :
     ∃ w, RelativeHistory ps v w ∧ u.skeleton = w.skeleton := by
   induction h generalizing v with
   | nil => exact ⟨v, .nil _, he⟩
   | @cons p t u ps z h hs ih =>
     have herase : t.erase = v.erase := by
       rw [← skeleton_erase t, ← skeleton_erase v, he]
     have hb := h.betaAt
     rw [herase] at hb
     obtain ⟨w, hw, _⟩ := lift_general_betaAt (t := v) hb
     have hp : p ∈ activePositions v := by
       rw [← skeleton_active v, ← he, skeleton_active t]
       exact h.active
     have hskeleton := h.reductionAt.skeleton
     rw [he] at hskeleton
     have hew := hskeleton.deterministic hw.skeleton
     obtain ⟨q, hq, heq⟩ := ih hew
     exact ⟨q, .cons (hw.active_stepAt hp) hq, heq⟩

 theorem normal_of_skeleton (he : t.skeleton = u.skeleton) (hn : Normal t) : Normal u := by
   rw [normal_iff_active_empty] at hn ⊢
   rw [← skeleton_active u, ← he, skeleton_active t, hn]
end Lamping.Lambda.Marked

