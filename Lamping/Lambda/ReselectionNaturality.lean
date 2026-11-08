import Lamping.Lambda.Reselection
namespace Lamping.Lambda.Marked
 theorem reselect_empty_app (F : List Path) (f a : Marked) :
     reselect F (.app [] f a) = .app [] (reselect F f) (reselect F a) := by
   cases f <;> simp [reselect]

 theorem reselect_rename (F : List Path) (ρ) (t : Marked) :
     reselect F (rename ρ t) = rename ρ (reselect F t) := by
   induction t generalizing ρ with
   | var => rfl
   | lam b ih => simp [rename, reselect, ih]
   | red l b a hb ha =>
     simp only [rename, reselect]
     split <;> simp [rename, hb, ha]
   | app l f a hf ha =>
     cases f with
     | var => simp [rename, reselect, ha]
     | app =>
       change Marked.app l (reselect F (rename ρ (.app _ _ _))) (reselect F (rename ρ a)) =
         Marked.app l (rename ρ (reselect F (.app _ _ _))) (rename ρ (reselect F a))
       rw [hf, ha]
     | red =>
       change Marked.app l (reselect F (rename ρ (.red _ _ _))) (reselect F (rename ρ a)) =
         Marked.app l (rename ρ (reselect F (.red _ _ _))) (rename ρ (reselect F a))
       rw [hf, ha]
     | lam b =>
       have hb (ρ) : reselect F (rename (Lambda.liftRen ρ) b) = rename (Lambda.liftRen ρ) (reselect F b) := by
         have hh := hf ρ
         simpa only [rename, reselect, Marked.lam.injEq] using hh
       simp only [rename, reselect]
       split <;> simp [rename, hb, ha]

 theorem reselect_subst (F : List Path) (σ) (t : Marked) (ht : Valid t) :
     reselect F (subst σ t) = subst (fun i => reselect F (σ i)) (reselect F t) := by
   induction t generalizing σ with
   | var => rfl
   | lam b ih =>
     simp only [subst, reselect, ih _ ht]
     congr 1; congr 1; funext i
     cases i <;> simp [liftSub, reselect, reselect_rename]
   | red l b a hb ha =>
     have hb' := hb (liftSub σ) ht.1
     have he : (fun i => reselect F (liftSub σ i)) = liftSub (fun i => reselect F (σ i)) := by
       funext i; cases i <;> simp [liftSub, reselect, reselect_rename]
     rw [he] at hb'
     simp only [subst, reselect]
     split <;> simp [subst, hb', ha _ ht.2]
   | app l f a hf ha =>
     cases f with
     | var i =>
       have hl : l = [] := by
         by_cases hn : l = []
         · exact hn
         · obtain ⟨_, he⟩ := ht.2.2 hn
           cases he
       subst l
       simp only [subst, reselect_empty_app, reselect, ha _ ht.2.1]
     | app l' f b =>
       change Marked.app l (reselect F (subst σ (.app l' f b))) (reselect F (subst σ a)) =
         Marked.app l (subst (fun i => reselect F (σ i)) (reselect F (.app l' f b)))
           (subst (fun i => reselect F (σ i)) (reselect F a))
       rw [hf _ ht.1, ha _ ht.2.1]
     | red l' b x =>
       change Marked.app l (reselect F (subst σ (.red l' b x))) (reselect F (subst σ a)) =
         Marked.app l (subst (fun i => reselect F (σ i)) (reselect F (.red l' b x)))
           (subst (fun i => reselect F (σ i)) (reselect F a))
       rw [hf _ ht.1, ha _ ht.2.1]
     | lam b =>
       have hb : reselect F (subst (liftSub σ) b) =
           subst (liftSub (fun i => reselect F (σ i))) (reselect F b) := by
         have hh := hf σ ht.1
         simpa only [subst, reselect, Marked.lam.injEq] using hh
       simp only [subst, reselect]
       split <;> simp [subst, hb, ha _ ht.2.1]

 theorem reselect_contract (F : List Path) (b a : Marked) (hb : Valid b) :
     reselect F (contract b a) = contract (reselect F b) (reselect F a) := by
   simp only [contract, reselect_subst F _ b hb]
   congr 1; funext i; cases i <;> rfl
end Lamping.Lambda.Marked

