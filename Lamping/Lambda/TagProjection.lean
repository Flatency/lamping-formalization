import Lamping.Lambda.AppIdentity
import Lamping.Lambda.ResidualTransport
namespace Lamping.Lambda.Marked
/-- Pointwise inclusion of one selected application identity in equally shaped
 annotated terms. Other old names may be unrelated. -/
inductive TagSubset (r s : Path) : Marked → Marked → Prop where
  | var (i) : TagSubset r s (.var i) (.var i)
  | lam : TagSubset r s b c → TagSubset r s (.lam b) (.lam c)
  | app : (r ∈ l → s ∈ k) → TagSubset r s f g → TagSubset r s a b →
      TagSubset r s (.app l f a) (.app k g b)
  | red : (r ∈ l → s ∈ k) → TagSubset r s b c → TagSubset r s a d →
      TagSubset r s (.red l b a) (.red k c d)

 theorem TagSubset.erase (h : TagSubset r s t u) : t.erase = u.erase := by
   induction h <;> simp_all [Marked.erase]
 theorem TagSubset.rename (h : TagSubset r s t u) (ρ) : TagSubset r s (rename ρ t) (rename ρ u) := by
   induction h generalizing ρ with
   | var => exact .var _
   | lam h ih => exact .lam (ih _)
   | app hr hf ha ihf iha => exact .app hr (ihf _) (iha _)
   | red hr hb ha ihb iha => exact .red hr (ihb _) (iha _)
 theorem TagSubset.subst (h : TagSubset r s t u) (hσ : ∀ i, TagSubset r s (σ i) (τ i)) :
     TagSubset r s (subst σ t) (subst τ u) := by
   induction h generalizing σ τ with
   | var i => exact hσ i
   | app hr hf ha ihf iha => exact .app hr (ihf hσ) (iha hσ)
   | lam hb ih =>
     apply TagSubset.lam
     apply ih
     intro i
     cases i with
     | zero => exact .var _
     | succ i => exact (hσ i).rename _
   | red hr hb ha ihb iha =>
     refine .red hr (ihb ?_) (iha hσ)
     intro i
     cases i with
     | zero => exact .var _
     | succ i => exact (hσ i).rename _
 theorem TagSubset.contract (hb : TagSubset r s b c) (ha : TagSubset r s a d) :
     TagSubset r s (contract b a) (contract c d) := by
   apply hb.subst
   intro i
   cases i with
   | zero => exact ha
   | succ i => exact .var _

 theorem TagSubset.tags (h : TagSubset r s t u) (hq : r ∈ tagsAt t q) : s ∈ tagsAt u q := by
   induction h generalizing q with
   | var i => cases q <;> simp [tagsAt] at hq
   | lam hb ih =>
     cases q with
     | nil => simp [tagsAt] at hq
     | cons e q => cases e with
       | fn => simp [tagsAt] at hq
       | arg => simp [tagsAt] at hq
       | body => exact ih hq
   | app hr hf ha ihf iha =>
     cases q with
     | nil => exact hr hq
     | cons e q => cases e with
       | fn => exact ihf hq
       | arg => exact iha hq
       | body => simp [tagsAt] at hq
   | red hr hb ha ihb iha =>
     cases q with
     | nil => exact hr hq
     | cons e q => cases e with
       | body => simp [tagsAt] at hq
       | arg => exact iha hq
       | fn => cases q with
         | nil => simp [tagsAt] at hq
         | cons e q => cases e with
           | fn => simp [tagsAt] at hq
           | arg => simp [tagsAt] at hq
           | body => exact ihb hq

 theorem ReductionAt.tagSubset (h : ReductionAt p t u) (ht : TagSubset r s t v) :
     ∃ w, ReductionAt p v w ∧ TagSubset r s u w := by
   induction h generalizing v with
   | appRoot l b a =>
     cases ht with
     | app hr hf ha => cases hf with
       | lam hb => exact ⟨_, .appRoot _ _ _, hb.contract ha⟩
   | redRoot l b a =>
     cases ht with
     | red hr hb ha => exact ⟨_, .redRoot _ _ _, hb.contract ha⟩
   | lam h ih =>
     cases ht with
     | lam hb => obtain ⟨w, hw, hh⟩ := ih hb; exact ⟨_, .lam hw, .lam hh⟩
   | appL h ih =>
     cases ht with
     | app hr hf ha => obtain ⟨w, hw, hh⟩ := ih hf; exact ⟨_, .appL hw, .app hr hh ha⟩
   | appR h ih =>
     cases ht with
     | app hr hf ha => obtain ⟨w, hw, hh⟩ := ih ha; exact ⟨_, .appR hw, .app hr hf hh⟩
   | redL h ih =>
     cases ht with
     | red hr hb ha => obtain ⟨w, hw, hh⟩ := ih hb; exact ⟨_, .redL hw, .red hr hh ha⟩
   | redR h ih =>
     cases ht with
     | red hr hb ha => obtain ⟨w, hw, hh⟩ := ih ha; exact ⟨_, .redR hw, .red hr hb hh⟩

 theorem History.tagSubset (h : History ps t u) (ht : TagSubset r s t v) :
     ∃ w, History ps v w ∧ TagSubset r s u w := by
   induction h generalizing v with
   | nil => exact ⟨_, .nil _, ht⟩
   | cons h hs ih =>
     obtain ⟨a, ha, hh⟩ := h.tagSubset ht
     obtain ⟨w, hw, hh'⟩ := ih hh
     exact ⟨w, .cons ha hw, hh'⟩
 theorem passive_idempotent (t : Marked) : t.passive.passive = t.passive := by
   induction t <;> simp_all [passive]

private theorem tagSubset_of_passive (ht : t.passive = t) (hu : u.passive = u)
     (he : t.erase = u.erase)
     (hi : ∀ q, r ∈ tagsAt t q → s ∈ tagsAt u q) : TagSubset r s t u := by
   induction t generalizing u with
   | var i =>
     cases u <;> simp only [erase, Term.var.injEq, reduceCtorEq] at he
     cases he
     exact .var _
   | lam b ih =>
     have htb : b.passive = b := Marked.lam.inj ht
     cases u with
     | var => cases he
     | app => cases he
     | red => cases he
     | lam c =>
       have huc : c.passive = c := Marked.lam.inj hu
       apply TagSubset.lam
       exact ih htb huc (Term.lam.inj he) (fun q hq => hi (.body :: q) hq)
   | red => cases ht
   | app l f a hf ha =>
     have htf := (Marked.app.inj ht).2.1
     have hta := (Marked.app.inj ht).2.2
     cases u with
     | var => cases he
     | lam => cases he
     | red => cases hu
     | app k g b =>
       have hug := (Marked.app.inj hu).2.1
       have hub := (Marked.app.inj hu).2.2
       have hes := Term.app.inj he
       exact .app (hi []) (hf htf hug hes.1 (fun q hq => hi (.fn :: q) hq))
         (ha hta hub hes.2 (fun q hq => hi (.arg :: q) hq))

/-- Trace inclusion and equal erased terms determine the structural relation
 after removing activity bits. No Valid premise or single-copy premise occurs. -/
 theorem TagSubset.of_trace (he : t.erase = u.erase)
     (hi : ∀ q, q ∈ tracePositions r t → q ∈ tracePositions s u) :
     TagSubset r s t.passive u.passive := by
   apply tagSubset_of_passive (passive_idempotent t) (passive_idempotent u)
   · simpa only [passive_erase] using he
   · intro q hq
     apply (mem_tagsAt _ s q).mpr
     rw [passive_trace]
     apply hi
     have hh := (mem_tagsAt _ r q).mp hq
     simpa only [passive_trace] using hh

/-- The requested forward inclusion bridge along the very same actual path
 history, allowing an identity to have several middle copies. -/
 theorem History.trace_inclusion (h : History ps t t') (k : History ps u u')
     (he : t.erase = u.erase)
     (hi : ∀ q, q ∈ tracePositions r t → q ∈ tracePositions s u) :
     ∀ q, q ∈ tracePositions r t' → q ∈ tracePositions s u' := by
   obtain ⟨v, hv, hh⟩ := h.passive.tagSubset (TagSubset.of_trace he hi)
   have hvu := hv.deterministic k.passive
   subst v
   intro q hq
   have htag : r ∈ tagsAt t'.passive q := (mem_tagsAt _ r q).mpr (by simpa only [passive_trace] using hq)
   have htag' := hh.tags htag
   have hout := (mem_tagsAt _ s q).mp htag'
   simpa only [passive_trace] using hout
end Lamping.Lambda.Marked

