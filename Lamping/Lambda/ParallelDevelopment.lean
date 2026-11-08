import Lamping.Lambda.ReselectionIdentity
namespace Lamping.Lambda.Marked
 theorem RelativeHistory.reselect_mono (h : RelativeHistory ps t u)
     (ht : Valid t) (hs : Selected F t) (hFG : ∀ r ∈ F, r ∈ G) :
     RelativeHistory ps (reselect G t) (reselect G u) := by
   induction h with
   | nil => exact .nil _
   | @cons p t u ps v h hh ih =>
     have hr := h.reductionAt.reselect ht G
     have hp : p ∈ activePositions (reselect G t) := by
       rw [reselect_active G _ ht]
       obtain ⟨r, hrF, hpr⟩ := (active_iff_selected_trace hs _).mp h.active
       exact ⟨r, hFG r hrF, hpr⟩
     exact .cons (hr.active_stepAt hp)
       (ih (h.reductionAt.valid ht) (h.selected hs))

 theorem reselect_union_of_complete (ht : Selected F t) (hn : Normal t) :
     reselect (F ++ G) t = reselect G t := by
   induction t with
   | var => rfl
   | lam b ih => exact congrArg Marked.lam (ih ht hn)
   | red => exact False.elim hn
   | app l f a hf ha =>
     have he : (∃ r ∈ l, r ∈ F ++ G) ↔ (∃ r ∈ l, r ∈ G) := by
       constructor
       · rintro ⟨r, hr, hFG⟩
         rcases List.mem_append.mp hFG with hF | hG
         · exact False.elim (ht.2.2 r hr hF)
         · exact ⟨r, hr, hG⟩
       · rintro ⟨r, hr, hG⟩; exact ⟨r, hr, List.mem_append_right F hG⟩
     cases f with
     | var => exact congrArg (Marked.app l _) (ha ht.2.1 hn.2)
     | app l' f b =>
       change Marked.app l (reselect (F ++ G) (.app l' f b)) (reselect (F ++ G) a) =
         Marked.app l (reselect G (.app l' f b)) (reselect G a)
       rw [hf ht.1 hn.1, ha ht.2.1 hn.2]
     | red => exact False.elim hn.1
     | lam b =>
       have hb : reselect (F ++ G) b = reselect G b := by
         have hh := hf ht.1 hn.1
         exact Marked.lam.inj hh
       simp only [reselect, he]
       split <;> simp only [hb, ha ht.2.1 hn.2]

 theorem Selected.mem_congr (h : Selected F t) (he : ∀ r, r ∈ F ↔ r ∈ G) : Selected G t := by
   induction t with
   | var => trivial
   | lam b ih => exact ih h
   | app l f a hf ha =>
     exact ⟨hf h.1, ha h.2.1, fun r hr hG => h.2.2 r hr ((he r).mpr hG)⟩
   | red l b a hb ha =>
     obtain ⟨r, hr, hF⟩ := h.2.2
     exact ⟨hb h.1, ha h.2.1, r, hr, (he r).mp hF⟩

 theorem reselect_append_comm (t : Marked) (ht : Valid t) :
     reselect (F ++ G) t = reselect (G ++ F) t := by
   apply selected_passive_injective (selected_reselect (F ++ G) t ht)
   · exact (selected_reselect (G ++ F) t ht).mem_congr (by intro r; simp [or_comm])
   · rw [passive_reselect, passive_reselect]
end Lamping.Lambda.Marked

namespace Lamping.Lambda
 theorem parallel_marked_diamond (h : ParallelStep F t u) (k : ParallelStep G t v) :
     Marked.dev (Marked.reselect G h.markedTarget) =
       Marked.dev (Marked.reselect F k.markedTarget) := by
   have hF := (Marked.completeOld_iff F t).mp h.complete
   have kG := (Marked.completeOld_iff G t).mp k.complete
   have hFU := hF.1.reselect_mono (Marked.valid_mark F t) (Marked.selected_mark F t)
     (G := F ++ G) (fun r hr => List.mem_append_left G hr)
   have kGU := kG.1.reselect_mono (Marked.valid_mark G t) (Marked.selected_mark G t)
     (G := G ++ F) (fun r hr => List.mem_append_left F hr)
   rw [Marked.reselect_mark] at hFU kGU
   have hFS := hF.1.general.selected (Marked.selected_mark F t)
   have kGS := kG.1.general.selected (Marked.selected_mark G t)
   rw [Marked.reselect_union_of_complete hFS hF.2] at hFU
   rw [Marked.reselect_union_of_complete kGS kG.2] at kGU
   have hs := hFU.steps.trans (Marked.steps_to_dev _)
   have ks := kGU.steps.trans (Marked.steps_to_dev _)
   have he : Marked.mark (G ++ F) t = Marked.mark (F ++ G) t := by
     rw [← Marked.reselect_mark (F ++ G) [] t, ← Marked.reselect_mark (G ++ F) [] t]
     exact Marked.reselect_append_comm _ (Marked.valid_mark [] t)
   rw [he] at ks
   exact Marked.complete_unique ⟨hs, Marked.normal_dev _⟩ ⟨ks, Marked.normal_dev _⟩
end Lamping.Lambda

