import Lamping.Lambda.ReselectionNaturality
namespace Lamping.Lambda.Marked
 theorem ReductionAt.reselect (h : ReductionAt p t u) (ht : Valid t) (F : List Path) :
     ReductionAt p (reselect F t) (reselect F u) := by
   induction h with
   | appRoot l b a =>
     rw [reselect_contract F b a ht.1]
     simp only [Marked.reselect]
     split
     · exact .redRoot _ _ _
     · exact .appRoot _ _ _
   | redRoot l b a =>
     rw [reselect_contract F b a ht.1]
     simp only [Marked.reselect]
     split
     · exact .redRoot _ _ _
     · exact .appRoot _ _ _
   | lam h ih => exact .lam (ih ht)
   | redL h ih =>
     simp only [Marked.reselect]
     split
     · exact .redL (ih ht.1)
     · exact .appL (.lam (ih ht.1))
   | redR h ih =>
     simp only [Marked.reselect]
     split
     · exact .redR (ih ht.2)
     · exact .appR (ih ht.2)
   | @appR p a a' l f h ih =>
     cases f with
     | lam b =>
       simp only [Marked.reselect]
       split
       · exact .redR (ih ht.2.1)
       · exact .appR (ih ht.2.1)
     | var i => exact .appR (ih ht.2.1)
     | app l' f b => exact .appR (ih ht.2.1)
     | red l' b x => exact .appR (ih ht.2.1)
   | @appL p f f' l a h ih =>
     cases f with
     | var i => cases h
     | lam b =>
       cases h with
       | lam hb =>
         simp only [Marked.reselect]
         split
         · cases ih ht.1 with | lam hh => exact .redL hh
         · exact .appL (ih ht.1)
     | app l' f b =>
       have hl : l = [] := by
         by_cases hn : l = []
         · exact hn
         · obtain ⟨_, he⟩ := ht.2.2 hn; cases he
       subst l
       rw [reselect_empty_app, reselect_empty_app]
       exact .appL (ih ht.1)
     | red l' b x =>
       have hl : l = [] := by
         by_cases hn : l = []
         · exact hn
         · obtain ⟨_, he⟩ := ht.2.2 hn; cases he
       subst l
       rw [reselect_empty_app, reselect_empty_app]
       exact .appL (ih ht.1)
 theorem History.reselect (h : History ps t u) (ht : Valid t) (F : List Path) :
     History ps (reselect F t) (reselect F u) := by
   induction h with
   | nil => exact .nil _
   | cons h hs ih => exact .cons (h.reselect ht F) (ih (h.valid ht))
end Lamping.Lambda.Marked


