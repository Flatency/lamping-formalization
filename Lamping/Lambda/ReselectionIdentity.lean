import Lamping.Lambda.ReselectionHistory
namespace Lamping.Lambda.Marked
 theorem passive_eq_lam {t b : Marked} (h : t.passive = .lam b) :
     ∃ c, t = .lam c ∧ c.passive = b := by
   cases t with
   | var i => cases h
   | app => cases h
   | red => cases h
   | lam c => exact ⟨c, rfl, Marked.lam.inj h⟩

 theorem selected_passive_injective (ht : Selected F t) (hu : Selected F u)
     (he : t.passive = u.passive) : t = u := by
   induction t generalizing u with
   | var i =>
     cases u <;> simp only [passive, Marked.var.injEq, reduceCtorEq] at he
     exact congrArg Marked.var he
   | lam b ih =>
     cases u with
     | var => cases he
     | app => cases he
     | red => cases he
     | lam c => exact congrArg Marked.lam (ih ht hu (Marked.lam.inj he))
   | app l f a hf ha =>
     cases u with
     | var => cases he
     | lam => cases he
     | app l' g b =>
       obtain ⟨hl, hfg, hab⟩ := Marked.app.inj he
       cases hl
       rw [hf ht.1 hu.1 hfg, ha ht.2.1 hu.2.1 hab]
     | red l' b x =>
       obtain ⟨hl, hfb, _⟩ := Marked.app.inj he
       cases hl
       obtain ⟨r, hr, hF⟩ := hu.2.2
       exact False.elim (ht.2.2 r hr hF)
   | red l b a hb ha =>
     cases u with
     | var => cases he
     | lam => cases he
     | app l' g x =>
       obtain ⟨hl, _, _⟩ := Marked.app.inj he
       cases hl
       obtain ⟨r, hr, hF⟩ := ht.2.2
       exact False.elim (hu.2.2 r hr hF)
     | red l' c x =>
       obtain ⟨hl, hbc, hax⟩ := Marked.app.inj he
       cases hl
       rw [hb ht.1 hu.1 (Marked.lam.inj hbc), ha ht.2.1 hu.2.1 hax]

 theorem reselect_eq_of_selected (ht : Valid t) (hs : Selected F t) : reselect F t = t :=
   selected_passive_injective (selected_reselect F t ht) hs (passive_reselect F t)

 theorem reselect_congr_passive (ht : Valid t) (hu : Valid u) (he : t.passive = u.passive) :
     reselect F t = reselect F u :=
   selected_passive_injective (selected_reselect F t ht) (selected_reselect F u hu)
     ((passive_reselect F t).trans (he.trans (passive_reselect F u).symm))

 theorem reselect_mark (F G : List Path) (t : Term) : reselect F (mark G t) = mark F t := by
   apply selected_passive_injective (selected_reselect F _ (valid_mark G t)) (selected_mark F t)
   rw [passive_reselect, passive_mark, passive_mark]

 theorem reselect_idem (F G : List Path) (t : Marked) (ht : Valid t) :
     reselect F (reselect G t) = reselect F t := by
   apply reselect_congr_passive (reselect_valid G t ht) ht
   exact passive_reselect G t
end Lamping.Lambda.Marked
