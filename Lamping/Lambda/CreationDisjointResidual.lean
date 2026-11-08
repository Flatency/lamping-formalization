import Lamping.Lambda.ResidualOrigins
import Lamping.Lambda.CreationLocality
import Lamping.Lambda.SingleContraction
namespace Lamping.Lambda.Marked
 theorem ReductionAt.tagsAt_disjoint (h : ReductionAt p t u) (hd : Lambda.DisjointPositions p q) :
     tagsAt u q = tagsAt t q := by
   induction h generalizing q with
   | appRoot => exact False.elim (hd.1 ⟨q, rfl⟩)
   | redRoot => exact False.elim (hd.1 ⟨q, rfl⟩)
   | lam h ih =>
     cases q with
     | nil => exact False.elim (hd.2 ⟨_, rfl⟩)
     | cons s q => cases s with
       | fn => rfl
       | arg => rfl
       | body => exact ih hd.child
   | appL h ih =>
     cases q with
     | nil => exact False.elim (hd.2 ⟨_, rfl⟩)
     | cons s q => cases s with
       | fn => exact ih hd.child
       | arg => rfl
       | body => rfl
   | appR h ih =>
     cases q with
     | nil => exact False.elim (hd.2 ⟨_, rfl⟩)
     | cons s q => cases s with
       | arg => exact ih hd.child
       | fn => rfl
       | body => rfl
   | redR h ih =>
     cases q with
     | nil => exact False.elim (hd.2 ⟨_, rfl⟩)
     | cons s q => cases s with
       | arg => exact ih hd.child
       | fn => cases q with
         | nil => rfl
         | cons s q => cases s <;> rfl
       | body => rfl
   | redL h ih =>
     cases q with
     | nil => exact False.elim (hd.2 ⟨_, rfl⟩)
     | cons s q => cases s with
       | arg => rfl
       | body => rfl
       | fn =>
         cases q with
         | nil => exact False.elim (hd.child.2 ⟨_, rfl⟩)
         | cons s q => cases s with
           | fn => rfl
           | arg => rfl
           | body => exact ih hd.child.child
end Lamping.Lambda.Marked

namespace Lamping.Lambda
/-- A disjoint endpoint redex has its actual initial ancestor at the identical
 position, not merely a coincidentally equal source subterm. -/
 theorem BetaAt.disjoint_initial_ancestor (hb : BetaAt t p u) (s : RedexOcc u)
     (hd : DisjointPositions p s.val) :
     ∃ r : RedexOcc t, r.val = s.val ∧ (singleContraction hb).derivation.Residual r s := by
   have hs := (hb.disjoint_redex_iff hd).mp s.property
   let r : RedexOcc t := ⟨s.val, hs⟩
   refine ⟨r, rfl, ?_⟩
   have ht := (singleContraction hb).tracked
   change Marked.History [p] (Marked.mark [] t) _ at ht
   cases ht with
   | cons hm hs =>
     cases hs
     refine ⟨_, .cons hm (.nil _), ?_, ?_⟩
     · exact ((Marked.passive_erase _).trans (singleContraction hb).target_eq)
     · apply (Marked.mem_tagsAt _ r.val s.val).mp
       rw [hm.tagsAt_disjoint hd]
       exact (Marked.mem_tagsAt _ r.val s.val).mpr
         ((Marked.initial_residual [] t r s.val).mpr rfl)
end Lamping.Lambda

