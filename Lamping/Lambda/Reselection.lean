import Lamping.Lambda.ResidualTransport
namespace Lamping.Lambda.Marked

/-- Select a new finite set of old names, preserving all passive annotations.
 Newly created, untagged applications cannot accidentally become selected. -/
def reselect (F : List Path) : Marked → Marked
  | .var i => .var i
  | .lam b => .lam (reselect F b)
  | .app l (.lam b) a =>
      if ∃ r ∈ l, r ∈ F then .red l (reselect F b) (reselect F a)
      else .app l (.lam (reselect F b)) (reselect F a)
  | .app l f a => .app l (reselect F f) (reselect F a)
  | .red l b a =>
      if ∃ r ∈ l, r ∈ F then .red l (reselect F b) (reselect F a)
      else .app l (.lam (reselect F b)) (reselect F a)

 theorem passive_reselect (F : List Path) (t : Marked) :
     passive (reselect F t) = passive t := by
   induction t with
   | var => rfl
   | lam b ih => simp [reselect, passive, ih]
   | red l b a hb ha => simp only [reselect]; split <;> simp [passive, hb, ha]
   | app l f a hf ha =>
     cases f with
     | var => simp [reselect, passive, ha]
     | app => simp [reselect, passive, hf, ha]
     | red l' b x =>
       change Marked.app l (passive (reselect F (.red l' b x))) (passive (reselect F a)) =
         Marked.app l (passive (.red l' b x)) (passive a)
       rw [hf, ha]
     | lam b =>
       have hb : passive (reselect F b) = passive b := by
         simpa only [reselect, passive, Marked.lam.injEq] using hf
       simp only [reselect]; split <;> simp [passive, hb, ha]

 theorem reselect_trace (F : List Path) (t : Marked) (r : Path) :
     tracePositions r (reselect F t) = tracePositions r t := by
   rw [← passive_trace, passive_reselect, passive_trace]

 theorem reselect_erase (F : List Path) (t : Marked) : (reselect F t).erase = t.erase := by
   rw [← passive_erase, passive_reselect, passive_erase]

 theorem selected_reselect (F : List Path) (t : Marked) (ht : Valid t) :
     Selected F (reselect F t) := by
   induction t with
   | var => trivial
   | lam b ih => exact ih ht
   | red l b a hb ha =>
     simp only [reselect]
     split
     · rename_i h; exact ⟨hb ht.1, ha ht.2, h⟩
     · rename_i h
       exact ⟨hb ht.1, ha ht.2, fun r hr hF => h ⟨r, hr, hF⟩⟩
   | app l f a hf ha =>
     cases f with
     | lam b =>
       have hb : Selected F (reselect F b) := hf ht.1
       simp only [reselect]
       split
       · rename_i h; exact ⟨hb, ha ht.2.1, h⟩
       · rename_i h; exact ⟨hb, ha ht.2.1, fun r hr hF => h ⟨r, hr, hF⟩⟩
     | var i =>
       refine ⟨trivial, ha ht.2.1, ?_⟩
       intro r hr _
       obtain ⟨b, he⟩ := ht.2.2 (fun he => by simp [he] at hr)
       cases he
     | app f b =>
       refine ⟨hf ht.1, ha ht.2.1, ?_⟩
       intro r hr _
       obtain ⟨b, he⟩ := ht.2.2 (fun he => by simp [he] at hr)
       cases he
     | red l' b a =>
       refine ⟨hf ht.1, ha ht.2.1, ?_⟩
       intro r hr _
       obtain ⟨b, he⟩ := ht.2.2 (fun he => by simp [he] at hr)
       cases he

 theorem reselect_valid (F : List Path) (t : Marked) (ht : Valid t) : Valid (reselect F t) := by
   induction t with
   | var => trivial
   | lam b ih => exact ih ht
   | red l b a hb ha =>
     simp only [reselect]
     split
     · exact ⟨hb ht.1, ha ht.2⟩
     · exact ⟨hb ht.1, ha ht.2, fun _ => ⟨_, rfl⟩⟩
   | app l f a hf ha =>
     cases f with
     | lam b =>
       have hb : Valid (reselect F b) := hf ht.1
       simp only [reselect]
       split
       · exact ⟨hb, ha ht.2.1⟩
       · exact ⟨hb, ha ht.2.1, fun _ => ⟨_, rfl⟩⟩
     | var i => exact ⟨trivial, ha ht.2.1, by intro hn; obtain ⟨_, he⟩ := ht.2.2 hn; cases he⟩
     | app f b => exact ⟨hf ht.1, ha ht.2.1, by intro hn; obtain ⟨_, he⟩ := ht.2.2 hn; cases he⟩
     | red l' b a => exact ⟨hf ht.1, ha ht.2.1, by intro hn; obtain ⟨_, he⟩ := ht.2.2 hn; cases he⟩

 theorem reselect_active (F : List Path) (t : Marked) (ht : Valid t) (p : Path) :
     p ∈ activePositions (reselect F t) ↔ ∃ r ∈ F, p ∈ tracePositions r t := by
   rw [active_iff_selected_trace (selected_reselect F t ht)]
   simp only [reselect_trace]
end Lamping.Lambda.Marked

