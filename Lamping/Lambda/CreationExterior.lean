import Lamping.Lambda.CreationDisjointResidual
namespace Lamping.Lambda.Marked
/-- A beta step may modify old annotations only at or below its contracted
 subtree. Annotations at strict ancestors survive, too. -/
 theorem ReductionAt.tagsAt_outside (h : ReductionAt p t u)
     (hn : ¬ ∃ x, q = p ++ x) : tagsAt u q = tagsAt t q := by
   induction h generalizing q with
   | appRoot => exact False.elim (hn ⟨q, rfl⟩)
   | redRoot => exact False.elim (hn ⟨q, rfl⟩)
   | lam h ih =>
     cases q with
     | nil => rfl
     | cons s q => cases s with
       | fn => rfl
       | arg => rfl
       | body => exact ih (by rintro ⟨x, hx⟩; exact hn ⟨x, congrArg (List.cons .body) hx⟩)
   | appL h ih =>
     cases q with
     | nil => rfl
     | cons s q => cases s with
       | fn => exact ih (by rintro ⟨x, hx⟩; exact hn ⟨x, congrArg (List.cons .fn) hx⟩)
       | arg => rfl
       | body => rfl
   | appR h ih =>
     cases q with
     | nil => rfl
     | cons s q => cases s with
       | arg => exact ih (by rintro ⟨x, hx⟩; exact hn ⟨x, congrArg (List.cons .arg) hx⟩)
       | fn => rfl
       | body => rfl
   | redR h ih =>
     cases q with
     | nil => rfl
     | cons s q => cases s with
       | arg => exact ih (by rintro ⟨x, hx⟩; exact hn ⟨x, congrArg (List.cons .arg) hx⟩)
       | fn => cases q with
         | nil => rfl
         | cons s q => cases s <;> rfl
       | body => rfl
   | redL h ih =>
     cases q with
     | nil => rfl
     | cons s q => cases s with
       | arg => rfl
       | body => rfl
       | fn => cases q with
         | nil => rfl
         | cons s q => cases s with
           | fn => rfl
           | arg => rfl
           | body => exact ih (by
             rintro ⟨x, hx⟩
             exact hn ⟨x, congrArg (fun q => Step.fn :: Step.body :: q) hx⟩)
end Lamping.Lambda.Marked

namespace Lamping.Lambda
 theorem BetaAt.outside_residual (hb : BetaAt t p u) (r : RedexOcc t)
     (hn : ¬ ∃ x, r.val = p ++ x) :
     ∃ s : RedexOcc u, s.val = r.val ∧ (singleContraction hb).derivation.Residual r s := by
   have ht := (singleContraction hb).tracked
   change Marked.History [p] (Marked.mark [] t) _ at ht
   cases ht with
   | cons hm hs =>
     cases hs
     have htrace : r.val ∈ Marked.tracePositions r.val (singleContraction hb).markedTarget.passive := by
       apply (Marked.mem_tagsAt _ r.val r.val).mp
       rw [hm.tagsAt_outside hn]
       exact (Marked.mem_tagsAt _ r.val r.val).mpr
         ((Marked.initial_residual [] t r r.val).mpr rfl)
     have hv := (Marked.History.valid (.cons hm (.nil _)) (Marked.valid_mark [] t))
     have hred := Marked.tracePositions_sound hv htrace
     have he := (Marked.passive_erase _).trans (singleContraction hb).target_eq
     rw [he] at hred
     exact ⟨⟨r.val, hred⟩, rfl, _, .cons hm (.nil _), he, htrace⟩

/-- A genuinely new redex (no initial ancestor at all) is confined to the
 contractum or the immediate function-parent application. -/
 theorem BetaAt.new_redex_locality (hb : BetaAt t p u) (s : RedexOcc u)
     (hn : ¬ ∃ r : RedexOcc t, (singleContraction hb).derivation.Residual r s) :
     (∃ x, s.val = p ++ x) ∨ p = s.val ++ [.fn] := by
   classical
   by_cases hp : ∃ x, s.val = p ++ x
   · exact .inl hp
   · have hnot : ¬ ∃ z, subtermAt t s.val = some z ∧ IsRedex z := by
       intro hred
       let r : RedexOcc t := ⟨s.val, hred⟩
       obtain ⟨s', hs', hres⟩ := hb.outside_residual r hp
       have he : s' = s := Subtype.ext hs'
       cases he
       exact hn ⟨r, hres⟩
     exact hb.creation_locality s.property hnot
end Lamping.Lambda
