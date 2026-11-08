import Lamping.Lambda.ParallelMovesResidual
namespace Lamping.Lambda.Marked
 theorem History.skeleton (h : History ps t u) : History ps t.skeleton u.skeleton := by
   induction h with
   | nil => exact .nil _
   | cons h hs ih => exact .cons h.skeleton ih
 theorem History.skeleton_eq (h : History ps t u) (k : History ps v w)
     (he : t.skeleton = v.skeleton) : u.skeleton = w.skeleton := by
   have hh := h.skeleton
   rw [he] at hh
   exact hh.deterministic k.skeleton

 theorem single_residual_skeleton (hv : Valid v) (he : v.erase = u) (r : Path) :
     (reselect [r] v).skeleton = (mark (tracePositions r v) u).skeleton := by
   apply skeleton_of_shape
   · rw [reselect_erase, erase_mark, he]
   · intro p
     rw [reselect_active [r] v hv, active_mark]
     constructor
     · rintro ⟨s, hs, hp⟩
       have hsr := List.mem_singleton.mp hs
       subst s
       refine ⟨hp, (Lambda.mem_redexPositions u p).mpr ?_⟩
       have hred := tracePositions_sound hv hp
       rw [he] at hred
       exact hred
     · rintro ⟨hp, _⟩
       exact ⟨r, List.mem_singleton_self r, hp⟩
end Lamping.Lambda.Marked

namespace Lamping.Lambda
/-- Genuine residual composition across a fresh initialization of the middle
 term. This is stronger than composing histories already carrying old tags. -/
 theorem Derivation.residual_append (h : Derivation t u) (k : Derivation u v)
     (r : RedexOcc t) (q : RedexOcc v) :
     (h.append k).Residual r q ↔
       ∃ s : RedexOcc u, h.Residual r s ∧ k.Residual s q := by
   obtain ⟨a, ha, hea⟩ := h.tracked
   obtain ⟨b, hb, heb⟩ := k.tracked
   have hva := ha.valid (Marked.valid_mark [] t)
   have hvb := hb.valid (Marked.valid_mark [] u)
   obtain ⟨c, hc, hec⟩ := Marked.lift_betaHistory k.valid a hea
   have hvc := hc.valid hva
   let S := Marked.tracePositions r.val a
   have hleft := hc.reselect hva [r.val]
   have hright := hb.reselect (Marked.valid_mark [] u) S
   rw [Marked.reselect_mark] at hright
   have hsk := hleft.skeleton_eq hright (Marked.single_residual_skeleton hva hea r.val)
   have hact : q.val ∈ Marked.activePositions (Marked.reselect [r.val] c) ↔
       q.val ∈ Marked.activePositions (Marked.reselect S b) := by
     rw [← Marked.skeleton_active (Marked.reselect [r.val] c), hsk,
       Marked.skeleton_active (Marked.reselect S b)]
   rw [Marked.reselect_active [r.val] c hvc, Marked.reselect_active S b hvb] at hact
   have htrace : q.val ∈ Marked.tracePositions r.val c ↔
       ∃ s ∈ S, q.val ∈ Marked.tracePositions s b := by
     simpa only [List.mem_singleton, exists_eq_left] using hact
   rw [Derivation.residual_iff_tracking _ (ha.append hc)]
   constructor
   · intro hq
     obtain ⟨s, hs, hsq⟩ := htrace.mp hq
     have hsr : ∃ z, subtermAt u s = some z ∧ IsRedex z := by
       have hh := Marked.tracePositions_sound hva hs
       rw [hea] at hh
       exact hh
     let sr : RedexOcc u := ⟨s, hsr⟩
     exact ⟨sr, (h.residual_iff_tracking ha r sr).mpr hs,
       (k.residual_iff_tracking hb sr q).mpr hsq⟩
   · rintro ⟨s, hrs, hsq⟩
     exact htrace.mpr ⟨s.val, (h.residual_iff_tracking ha r s).mp hrs,
       (k.residual_iff_tracking hb s q).mp hsq⟩
end Lamping.Lambda
