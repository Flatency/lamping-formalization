import Lamping.Lambda.LabelInitialRelabelling
namespace Lamping.Lambda.Labelled

/-- The syntactic portion of AG6.2.5: generated words begin/end in atoms,
with a barred recursively alternating degree between adjacent atomic pieces.
This says nothing yet about the original edge endpoints. -/
inductive Label.Alternating : Label → Prop where
  | atom (n) : Alternating (Label.atom n)
  | over : Alternating a → Alternating d → Alternating b →
      Alternating ((a.concat d.over).concat b)
  | under : Alternating a → Alternating d → Alternating b →
      Alternating ((a.concat d.under).concat b)

theorem Label.Alternating.outer_length_odd (h : Label.Alternating a) : a.length%2=1 := by
  induction h with
  | atom => rfl
  | over ha hd hb ia id ib => simp only [Label.length_concat,Label.over,Label.length]; omega
  | under ha hd hb ia id ib => simp only [Label.length_concat,Label.under,Label.length]; omega

namespace LTerm
def Alternating : LTerm → Prop
  | .var l _ => l.Alternating
  | .lam l b => l.Alternating ∧ b.Alternating
  | .app l f a => l.Alternating ∧ f.Alternating ∧ a.Alternating

theorem alternating_iff (t : LTerm) : t.Alternating ↔ ∀ l∈t.labels,l.Alternating := by
  induction t with
  | var => simp [Alternating,labels]
  | lam _ _ ih => simp [Alternating,labels,ih]
  | app _ _ _ hf ha => simp [Alternating,labels,hf,ha,or_imp,forall_and]

theorem Alternating.rename {t : LTerm} (h : t.Alternating) (rho : Nat → Nat) :
    (t.rename rho).Alternating := by
  induction t generalizing rho with
  | var => exact h
  | lam _ _ ih => exact ⟨h.1,ih h.2 _⟩
  | app _ _ _ hf ha => exact ⟨h.1,hf h.2.1 _,ha h.2.2 _⟩

theorem Alternating.prepend_over {t : LTerm} {a d : Label} (h : t.Alternating)
    (ha : a.Alternating) (hd : d.Alternating) : (t.prepend (a.concat d.over)).Alternating := by
  cases t with
  | var => exact .over ha hd h
  | lam => exact ⟨.over ha hd h.1,h.2⟩
  | app => exact ⟨.over ha hd h.1,h.2⟩

theorem Alternating.prepend_under {t : LTerm} {a d : Label} (h : t.Alternating)
    (ha : a.Alternating) (hd : d.Alternating) : (t.prepend (a.concat d.under)).Alternating := by
  cases t with
  | var => exact .under ha hd h
  | lam => exact ⟨.under ha hd h.1,h.2⟩
  | app => exact ⟨.under ha hd h.1,h.2⟩

/-- A substituted argument carries one underlined contraction degree at its
root; occurrence labels supply its preceding atomic side. -/
def SubValue.Alternating : SubValue → Prop
  | .keep _ => True
  | .put t => ∃ (d : Label) (a : LTerm), d.Alternating ∧ a.Alternating ∧ t=a.prepend d.under

theorem Alternating.subst {t : LTerm} {sigma : Nat → SubValue} (h : t.Alternating)
    (hs : ∀ i, (sigma i).Alternating) : (t.subst sigma).Alternating := by
  induction t generalizing sigma with
  | var l i =>
    cases ht : sigma i with
    | keep j => simpa only [LTerm.subst,ht,Alternating] using h
    | put u =>
      have hu : ∃ (d : Label) (a : LTerm), d.Alternating ∧ a.Alternating ∧ u=a.prepend d.under := by
        simpa only [SubValue.Alternating,ht] using hs i
      obtain ⟨d,a,hd,ha,rfl⟩ := hu
      simpa only [LTerm.subst,ht,prepend_assoc] using ha.prepend_under h hd
  | app l f a hf ha => exact ⟨h.1,hf h.2.1 hs,ha h.2.2 hs⟩
  | lam l b hb =>
    refine ⟨h.1,hb h.2 ?_⟩
    intro i
    cases i with
    | zero => trivial
    | succ i =>
      cases ht : sigma i with
      | keep j => simp [lift,ht,SubValue.Alternating]
      | put u =>
        obtain ⟨d,a,hd,ha,he⟩ := (show SubValue.Alternating (.put u) from by simpa only [ht] using hs i)
        simp only [lift,ht,SubValue.Alternating]
        exact ⟨d,a.rename Nat.succ,hd,ha.rename _,by rw [he,rename_prepend]⟩

theorem Alternating.contract {b a : LTerm} {beta alpha : Label} (hb : b.Alternating) (ha : a.Alternating)
    (hbeta : beta.Alternating) (halpha : alpha.Alternating) :
    (contract beta alpha b a).Alternating := by
  apply Alternating.prepend_over
  · apply hb.subst
    intro i
    cases i with
    | zero => exact ⟨alpha,a,halpha,ha,rfl⟩
    | succ i => trivial
  · exact hbeta
  · exact halpha
end LTerm

theorem StepAt.alternating (h : StepAt p t u) (ht : t.Alternating) : u.Alternating := by
  induction h with
  | root => exact ht.2.1.2.contract ht.2.2 ht.1 ht.2.1.1
  | fn _ ih => exact ⟨ht.1,ih ht.2.1,ht.2.2⟩
  | arg _ ih => exact ⟨ht.1,ht.2.1,ih ht.2.2⟩
  | body _ ih => exact ⟨ht.1,ih ht.2⟩

theorem History.alternating (h : History ps t u) (ht : t.Alternating) : u.Alternating := by
  induction h with
  | nil => exact ht
  | cons h _ ih => exact ih (h.alternating ht)

theorem INIT.alternating (hi : INIT t) : t.Alternating := by
  rw [LTerm.alternating_iff]
  intro l hl
  obtain ⟨n,rfl⟩ := hi.1 l hl
  exact .atom n

/-- Actual generated labels satisfy the alternating outer-word invariant. -/
theorem History.generated_label_alternating (h : History ps t u) (hi : INIT t)
    (hl : l∈u.labels) : l.Alternating :=
  (LTerm.alternating_iff u).mp (h.alternating hi.alternating) l hl
end Lamping.Lambda.Labelled

