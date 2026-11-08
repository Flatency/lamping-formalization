import Lamping.Lambda.HeadVariableInvariant
import Lamping.Lambda.ResidualSkeleton
namespace Lamping.Lambda.Marked

/-- Give every initial application its unique position identity. Activity
 still marks only the selected actual redexes. Nonredex tags need no Valid. -/
def markAllAt (F : List Path) : Term → Path → Marked
  | .var i, _ => .var i
  | .lam b, p => .lam (markAllAt F b (p ++ [.body]))
  | .app (.lam b) a, p =>
    if p ∈ F then .red [p] (markAllAt F b (p ++ [.fn, .body])) (markAllAt F a (p ++ [.arg]))
    else .app [p] (.lam (markAllAt F b (p ++ [.fn, .body]))) (markAllAt F a (p ++ [.arg]))
  | .app f a, p => .app [p] (markAllAt F f (p ++ [.fn])) (markAllAt F a (p ++ [.arg]))

def markAll (F : List Path) (t : Term) : Marked := markAllAt F t []

 theorem erase_markAllAt (F : List Path) (t : Term) (p : Path) : (markAllAt F t p).erase = t := by
   induction t generalizing p with
   | var => rfl
   | lam b ih => simp [markAllAt, erase, ih]
   | app f a hf ha =>
     cases f with
     | var i => simp [markAllAt, erase, ha]
     | app f c => simp [markAllAt, erase, hf, ha]
     | lam b =>
       have hb := hf (p := p ++ [.fn])
       simp only [markAllAt, erase, Term.lam.injEq] at hb
       simp only [List.append_assoc, List.cons_append, List.nil_append] at hb
       simp only [markAllAt]
       split <;> simp [erase, hb, ha]
 theorem skeleton_markAllAt (F : List Path) (t : Term) (p : Path) :
     (markAllAt F t p).skeleton = (markAt F t p).skeleton := by
   induction t generalizing p with
   | var => rfl
   | lam b ih => simp [markAllAt, markAt, skeleton, ih]
   | app f a hf ha =>
     cases f with
     | var i => simp [markAllAt, markAt, skeleton, ha]
     | app f c => simp [markAllAt, markAt, skeleton, hf, ha]
     | lam b =>
       have hb := hf (p := p ++ [.fn])
       simp only [markAllAt, markAt, skeleton, Marked.lam.injEq] at hb
       simp only [List.append_assoc, List.cons_append, List.nil_append] at hb
       simp only [markAllAt, markAt]
       split <;> simp [skeleton, hb, ha, List.append_assoc]
 theorem erase_markAll (F : List Path) (t : Term) : (markAll F t).erase = t := erase_markAllAt F t []
 theorem skeleton_markAll (F : List Path) (t : Term) :
     (markAll F t).skeleton = (mark F t).skeleton := skeleton_markAllAt F t []
/-- Application identities are initially unique, including nonredex apps. -/
 theorem tagsAt_markAllAt (F : List Path) (t : Term) (pre q : Path) :
     tagsAt (markAllAt F t pre) q =
       match subtermAt t q with
       | some (.app _ _) => [pre ++ q]
       | _ => [] := by
   induction q generalizing t pre with
   | nil =>
     cases t with
     | var => rfl
     | lam => rfl
     | app f a =>
       cases f with
       | var => simp [markAllAt, tagsAt, subtermAt]
       | app => simp [markAllAt, tagsAt, subtermAt]
       | lam => simp only [markAllAt]; split <;> simp [tagsAt, subtermAt]
   | cons s q ih =>
     have hh (v : Term) (pre : Path) (s : Lambda.Step) :
         tagsAt (markAllAt F v (pre ++ [s])) q =
         match subtermAt v q with
         | some (.app _ _) => [pre ++ s :: q]
         | _ => [] := by
       have hh := ih v (pre ++ [s])
       rw [List.append_assoc] at hh
       simp only [List.cons_append, List.nil_append] at hh
       exact hh
     cases t with
     | var i => cases s <;> rfl
     | lam b =>
       cases s with
       | fn => rfl
       | arg => rfl
       | body => simpa [markAllAt, tagsAt, subtermAt, List.append_assoc, List.cons_append, List.nil_append] using hh b pre .body
     | app f a =>
       cases f with
       | var i =>
         cases s with
         | fn => simpa [markAllAt, tagsAt, subtermAt, List.append_assoc, List.cons_append, List.nil_append] using hh (.var i) pre .fn
         | arg => simpa [markAllAt, tagsAt, subtermAt, List.append_assoc, List.cons_append, List.nil_append] using hh a pre .arg
         | body => rfl
       | app f c =>
         cases s with
         | fn => simpa [markAllAt, tagsAt, subtermAt, List.append_assoc, List.cons_append, List.nil_append] using hh (.app f c) pre .fn
         | arg => simpa [markAllAt, tagsAt, subtermAt, List.append_assoc, List.cons_append, List.nil_append] using hh a pre .arg
         | body => rfl
       | lam b =>
         simp only [markAllAt]
         split <;> cases s with
         | body => rfl
         | arg => simpa [tagsAt, subtermAt, List.append_assoc, List.cons_append, List.nil_append] using hh a pre .arg
         | fn =>
           cases q with
           | nil => rfl
           | cons e q => cases e with
             | fn => rfl
             | arg => rfl
             | body => simpa [markAllAt, tagsAt, subtermAt] using hh (.lam b) pre .fn
/-- Reconstruct the structural head-variable invariant from actual tag sites. -/
 theorem headVariable_of_tags
     (h : ∀ q, r ∈ tagsAt t q →
       subtermAt t.erase (q ++ [.fn]) = some (.var (k + binderDepth q))) :
     HeadVariable r k t := by
   induction t generalizing k with
   | var => trivial
   | lam b ih =>
     apply ih
     intro q hq
     have hh := h (.body :: q) hq
     simpa [erase, subtermAt, binderDepth, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hh
   | app l f a hf ha =>
     refine ⟨hf ?_, ha ?_, ?_⟩
     · intro q hq
       exact h (.fn :: q) hq
     · intro q hq
       exact h (.arg :: q) hq
     · intro hr
       have hh := h [] hr
       simp only [List.nil_append, erase, subtermAt, binderDepth, Nat.add_zero, Option.some.injEq] at hh
       cases f <;> simp_all [erase]
   | red l b a hb ha =>
     refine ⟨hb ?_, ha ?_, ?_⟩
     · intro q hq
       have hh := h (.fn :: .body :: q) hq
       simpa [erase, subtermAt, binderDepth, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hh
     · intro q hq
       exact h (.arg :: q) hq
     · intro hr
       have hh := h [] hr
       cases hh
 theorem initial_application_identity (h : r ∈ tagsAt (markAll F t) q) : r = q := by
   change r ∈ tagsAt (markAllAt F t []) q at h
   rw [tagsAt_markAllAt] at h
   cases he : subtermAt t q with
   | none => simp [he] at h
   | some u =>
     cases u with
     | var => simp [he] at h
     | lam => simp [he] at h
     | app f a => simpa [he] using h

/-- The unique identity of a potential application has the designated outer
 free variable as head throughout the whole initial annotated term. -/
 theorem headVariable_markAll
     (hp : subtermAt t site = some (.app (.var (k + binderDepth site)) a)) :
     HeadVariable site k (markAll F t) := by
   apply headVariable_of_tags
   intro q hq
   have he := initial_application_identity hq
   subst q
   rw [erase_markAll, subtermAt_append, hp]
   rfl
/-- Every actual application retains an initial application identity. -/
def EveryApplicationTagged : Marked → Prop
  | .var _ => True
  | .lam b => EveryApplicationTagged b
  | .app l f a => l ≠ [] ∧ EveryApplicationTagged f ∧ EveryApplicationTagged a
  | .red l b a => l ≠ [] ∧ EveryApplicationTagged b ∧ EveryApplicationTagged a

 theorem EveryApplicationTagged.rename (h : EveryApplicationTagged t) (ρ) :
     EveryApplicationTagged (rename ρ t) := by
   induction t generalizing ρ with
   | var => trivial
   | lam b ih => exact ih h _
   | app l f a hf ha => exact ⟨h.1, hf h.2.1 _, ha h.2.2 _⟩
   | red l b a hb ha => exact ⟨h.1, hb h.2.1 _, ha h.2.2 _⟩
 theorem EveryApplicationTagged.subst (h : EveryApplicationTagged t)
     (hσ : ∀ i, EveryApplicationTagged (σ i)) : EveryApplicationTagged (subst σ t) := by
   induction t generalizing σ with
   | var i => exact hσ i
   | app l f a hf ha => exact ⟨h.1, hf h.2.1 hσ, ha h.2.2 hσ⟩
   | lam b ih =>
     apply ih h
     intro i
     cases i with
     | zero => trivial
     | succ i => exact (hσ i).rename _
   | red l b a hb ha =>
     refine ⟨h.1, hb h.2.1 ?_, ha h.2.2 hσ⟩
     intro i
     cases i with
     | zero => trivial
     | succ i => exact (hσ i).rename _
 theorem EveryApplicationTagged.contract (hb : EveryApplicationTagged b)
     (ha : EveryApplicationTagged a) : EveryApplicationTagged (contract b a) := by
   apply hb.subst
   intro i
   cases i with
   | zero => exact ha
   | succ => trivial
 theorem ReductionAt.everyApplicationTagged (h : ReductionAt p t u) (ht : EveryApplicationTagged t) :
     EveryApplicationTagged u := by
   induction h with
   | appRoot l b a => exact EveryApplicationTagged.contract (b := b) ht.2.1 ht.2.2
   | redRoot => exact ht.2.1.contract ht.2.2
   | lam h ih => exact ih ht
   | appL h ih => exact ⟨ht.1, ih ht.2.1, ht.2.2⟩
   | appR h ih => exact ⟨ht.1, ht.2.1, ih ht.2.2⟩
   | redL h ih => exact ⟨ht.1, ih ht.2.1, ht.2.2⟩
   | redR h ih => exact ⟨ht.1, ht.2.1, ih ht.2.2⟩
 theorem History.everyApplicationTagged (h : History ps t u) (ht : EveryApplicationTagged t) :
     EveryApplicationTagged u := by
   induction h with
   | nil => exact ht
   | cons h hs ih => exact ih (h.everyApplicationTagged ht)

 theorem everyApplicationTagged_markAllAt (F : List Path) (t : Term) (p : Path) :
     EveryApplicationTagged (markAllAt F t p) := by
   induction t generalizing p with
   | var => trivial
   | lam b ih => exact ih _
   | app f a hf ha =>
     cases f with
     | var => exact ⟨by simp, trivial, ha _⟩
     | app => exact ⟨by simp, hf _, ha _⟩
     | lam b =>
       have hb := hf (p ++ [.fn])
       simp only [markAllAt, EveryApplicationTagged, List.append_assoc, List.cons_append, List.nil_append] at hb
       simp only [markAllAt]
       split <;> exact ⟨by simp, hb, ha _⟩
 theorem singleTags_markAllAt (F : List Path) (t : Term) (p : Path) :
     SingleTags (markAllAt F t p) := by
   induction t generalizing p with
   | var => trivial
   | lam b ih => exact ih _
   | app f a hf ha =>
     cases f with
     | var => exact ⟨by simp, trivial, ha _⟩
     | app => exact ⟨by simp, hf _, ha _⟩
     | lam b =>
       have hb := hf (p ++ [.fn])
       simp only [markAllAt, SingleTags, List.append_assoc, List.cons_append, List.nil_append] at hb
       simp only [markAllAt]
       split <;> exact ⟨by simp, hb, ha _⟩
 theorem initial_application_identityAt (h : r ∈ tagsAt (markAllAt F t pre) q) :
     r = pre ++ q := by
   rw [tagsAt_markAllAt] at h
   cases he : subtermAt t q with
   | none => simp [he] at h
   | some u =>
     cases u with
     | var => simp [he] at h
     | lam => simp [he] at h
     | app f a => simpa [he] using h

 theorem headVariable_markAllAt
     (hp : subtermAt t site = some (.app (.var (k + binderDepth site)) a)) :
     HeadVariable (pre ++ site) k (markAllAt F t pre) := by
   apply headVariable_of_tags
   intro q hq
   have he := initial_application_identityAt hq
   have hs : site = q := List.append_cancel_left he
   subst q
   rw [erase_markAllAt, subtermAt_append, hp]
   rfl
 theorem EveryApplicationTagged.tags_nonempty (h : EveryApplicationTagged t)
     (hp : subtermAt t.erase q = some (.app f a)) : tagsAt t q ≠ [] := by
   induction t generalizing q with
   | var i => cases q with
     | nil => cases hp
     | cons s q => cases s <;> cases hp
   | lam b ih =>
     cases q with
     | nil => cases hp
     | cons s q => cases s with
       | fn => cases hp
       | arg => cases hp
       | body => exact ih h hp
   | app l g b hg hb =>
     cases q with
     | nil => exact h.1
     | cons s q => cases s with
       | fn => exact hg h.2.1 hp
       | arg => exact hb h.2.2 hp
       | body => cases hp
   | red l b c hb hc =>
     cases q with
     | nil => exact h.1
     | cons s q => cases s with
       | body => cases hp
       | arg => exact hc h.2.2 hp
       | fn => cases q with
         | nil => cases hp
         | cons s q => cases s with
           | fn => cases hp
           | arg => cases hp
           | body => exact hb h.2.1 hp

 theorem EveryApplicationTagged.redex_tag (h : EveryApplicationTagged t)
     (hp : ∃ v, subtermAt t.erase q = some v ∧ IsRedex v) : ∃ r, r ∈ tagsAt t q := by
   obtain ⟨v, hv, hr⟩ := hp
   cases v with
   | var => cases hr
   | lam => cases hr
   | app f a =>
     have hn := h.tags_nonempty hv
     cases he : tagsAt t q with
     | nil => exact False.elim (hn he)
     | cons r rs => exact ⟨r, List.mem_cons_self⟩
end Lamping.Lambda.Marked

















