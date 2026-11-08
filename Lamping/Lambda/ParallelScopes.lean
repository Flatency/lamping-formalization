import Lamping.Lambda.ContextualResiduals
namespace Lamping.Lambda.Marked

 theorem normal_markAt_no_selection (hn : ∀ q, pre ++ q ∉ F) :
     Normal (markAt F t pre) := by
   apply (normal_iff_no_step _).mpr
   rintro ⟨u, hu⟩
   obtain ⟨q, hq⟩ := hu.at
   exact hn q ((active_markAt F t pre q).mp hq.active).1

/-- A passive application with a completed argument can develop only its
 function. This extracts the actual local paths and annotated endpoint. -/
 theorem RelativeHistory.app_left_scope (h : RelativeHistory ps (.app l f a) u)
     (ha : Normal a) :
     ∃ qs f', ps = qs.map (Lambda.Step.fn :: ·) ∧
       RelativeHistory qs f f' ∧ u = .app l f' a := by
   induction ps generalizing f u with
   | nil => cases h; exact ⟨[], f, rfl, .nil _, rfl⟩
   | cons p ps ih =>
     cases h with
     | cons h hs => cases h with
       | appL h =>
         obtain ⟨qs, f', hps, hlocal, hu⟩ := ih hs
         exact ⟨_ :: qs, f', by simp [hps], .cons h hlocal, hu⟩
       | appR h => exact False.elim ((normal_iff_no_step a).mp ha ⟨_, h.step⟩)

 theorem RelativeHistory.app_right_scope (h : RelativeHistory ps (.app l f a) u)
     (hf : Normal f) :
     ∃ qs a', ps = qs.map (Lambda.Step.arg :: ·) ∧
       RelativeHistory qs a a' ∧ u = .app l f a' := by
   induction ps generalizing a u with
   | nil => cases h; exact ⟨[], a, rfl, .nil _, rfl⟩
   | cons p ps ih =>
     cases h with
     | cons h hs => cases h with
       | appR h =>
         obtain ⟨qs, a', hps, hlocal, hu⟩ := ih hs
         exact ⟨_ :: qs, a', by simp [hps], .cons h hlocal, hu⟩
       | appL h => exact False.elim ((normal_iff_no_step f).mp hf ⟨_, h.step⟩)

 theorem RelativeHistory.lam_scope (h : RelativeHistory ps (.lam b) u) :
     ∃ qs b', ps = qs.map (Lambda.Step.body :: ·) ∧
       RelativeHistory qs b b' ∧ u = .lam b' := by
   induction ps generalizing b u with
   | nil => cases h; exact ⟨[], b, rfl, .nil _, rfl⟩
   | cons p ps ih =>
     cases h with
     | cons h hs => cases h with
       | lam h =>
         obtain ⟨qs, b', hps, hlocal, hu⟩ := ih hs
         exact ⟨_ :: qs, b', by simp [hps], .cons h hlocal, hu⟩
end Lamping.Lambda.Marked

namespace Lamping.Lambda
/-- A complete development selected entirely in an application's function
 really factors into a complete development of that function. -/
 theorem ParallelStep.app_left_scope (h : ParallelStep (F.map (Step.fn :: ·)) (.app f a) u) :
     ∃ f', ∃ k : ParallelStep F f f',
       u = .app f' a ∧ h.paths = k.paths.map (Step.fn :: ·) := by
   have hn : [] ∉ F.map (Step.fn :: ·) := by simp
   have init : ∃ l, Marked.mark (F.map (Step.fn :: ·)) (.app f a) =
       .app l (Marked.markAt (F.map (Step.fn :: ·)) f [.fn])
         (Marked.markAt (F.map (Step.fn :: ·)) a [.arg]) := by
     cases f with
     | var => exact ⟨[], rfl⟩
     | app => exact ⟨[], rfl⟩
     | lam b => refine ⟨[[]], ?_⟩; simp [Marked.mark, Marked.markAt, hn]
   obtain ⟨l, hl⟩ := init
   have hh := (Marked.completeOld_iff _ _).mp h.complete
   rw [hl] at hh
   have ha : Marked.Normal (Marked.markAt (F.map (Step.fn :: ·)) a [.arg]) :=
     Marked.normal_markAt_no_selection (by intro q; simp)
   obtain ⟨qs, target, hps, hlocal, hout⟩ := hh.1.app_left_scope ha
   have shape : (Marked.markAt (F.map (Step.fn :: ·)) f [.fn]).skeleton = (Marked.mark F f).skeleton := by
     apply Marked.skeleton_of_shape
     · simp only [Marked.erase_markAt, Marked.erase_mark]
     · intro q
       rw [Marked.active_markAt, Marked.active_mark]
       simp
   obtain ⟨target', hlocal', hshape⟩ := hlocal.lift_skeleton shape
   have targetNormal : Marked.Normal target := by
     rw [hout] at hh
     exact hh.2.1
   have hn' := Marked.normal_of_skeleton hshape targetNormal
   have he : target.erase = target'.erase := by
     rw [← Marked.skeleton_erase target, ← Marked.skeleton_erase target', hshape]
   let k : ParallelStep F f target.erase :=
     ⟨qs, target', (Marked.completeOld_iff F f).mpr ⟨hlocal', hn'⟩, he.symm⟩
   refine ⟨target.erase, k, ?_, hps⟩
   rw [← h.target_eq, hout]
   simp [Marked.erase, Marked.erase_markAt]

 theorem ParallelStep.app_right_scope (h : ParallelStep (F.map (Step.arg :: ·)) (.app f a) u) :
     ∃ a', ∃ k : ParallelStep F a a',
       u = .app f a' ∧ h.paths = k.paths.map (Step.arg :: ·) := by
   have hn : [] ∉ F.map (Step.arg :: ·) := by simp
   have init : ∃ l, Marked.mark (F.map (Step.arg :: ·)) (.app f a) =
       .app l (Marked.markAt (F.map (Step.arg :: ·)) f [.fn])
         (Marked.markAt (F.map (Step.arg :: ·)) a [.arg]) := by
     cases f with
     | var => exact ⟨[], rfl⟩
     | app => exact ⟨[], rfl⟩
     | lam b => refine ⟨[[]], ?_⟩; simp [Marked.mark, Marked.markAt, hn]
   obtain ⟨l, hl⟩ := init
   have hh := (Marked.completeOld_iff _ _).mp h.complete
   rw [hl] at hh
   have hf : Marked.Normal (Marked.markAt (F.map (Step.arg :: ·)) f [.fn]) :=
     Marked.normal_markAt_no_selection (by intro q; simp)
   obtain ⟨qs, target, hps, hlocal, hout⟩ := hh.1.app_right_scope hf
   have shape : (Marked.markAt (F.map (Step.arg :: ·)) a [.arg]).skeleton = (Marked.mark F a).skeleton := by
     apply Marked.skeleton_of_shape
     · simp only [Marked.erase_markAt, Marked.erase_mark]
     · intro q
       rw [Marked.active_markAt, Marked.active_mark]
       simp
   obtain ⟨target', hlocal', hshape⟩ := hlocal.lift_skeleton shape
   have targetNormal : Marked.Normal target := by
     rw [hout] at hh
     exact hh.2.2
   have hn' := Marked.normal_of_skeleton hshape targetNormal
   have he : target.erase = target'.erase := by
     rw [← Marked.skeleton_erase target, ← Marked.skeleton_erase target', hshape]
   let k : ParallelStep F a target.erase :=
     ⟨qs, target', (Marked.completeOld_iff F a).mpr ⟨hlocal', hn'⟩, he.symm⟩
   refine ⟨target.erase, k, ?_, hps⟩
   rw [← h.target_eq, hout]
   simp [Marked.erase, Marked.erase_markAt]

 theorem ParallelStep.lam_scope (h : ParallelStep (F.map (Step.body :: ·)) (.lam b) u) :
     ∃ b', ∃ k : ParallelStep F b b',
       u = .lam b' ∧ h.paths = k.paths.map (Step.body :: ·) := by
   have hh := (Marked.completeOld_iff _ _).mp h.complete
   change Marked.RelativeHistory h.paths (.lam (Marked.markAt (F.map (Step.body :: ·)) b [.body]))
       h.markedTarget ∧ Marked.Normal h.markedTarget at hh
   obtain ⟨qs, target, hps, hlocal, hout⟩ := hh.1.lam_scope
   have shape : (Marked.markAt (F.map (Step.body :: ·)) b [.body]).skeleton = (Marked.mark F b).skeleton := by
     apply Marked.skeleton_of_shape
     · simp only [Marked.erase_markAt, Marked.erase_mark]
     · intro q
       rw [Marked.active_markAt, Marked.active_mark]
       simp
   obtain ⟨target', hlocal', hshape⟩ := hlocal.lift_skeleton shape
   have targetNormal : Marked.Normal target := by rw [hout] at hh; exact hh.2
   have hn' := Marked.normal_of_skeleton hshape targetNormal
   have he : target.erase = target'.erase := by
     rw [← Marked.skeleton_erase target, ← Marked.skeleton_erase target', hshape]
   let k : ParallelStep F b target.erase :=
     ⟨qs, target', (Marked.completeOld_iff F b).mpr ⟨hlocal', hn'⟩, he.symm⟩
   refine ⟨target.erase, k, ?_, hps⟩
   rw [← h.target_eq, hout]
   rfl
end Lamping.Lambda
