import Lamping.Lambda.LabelSubstitution
import Lamping.Lambda.ApplicationDiamond
namespace Lamping.Lambda.Labelled

/-- Structural evaluation of exactly the active marked redexes. The source
and result carry all real labels; passive applications remain passive. -/
inductive DevelopmentEval : Marked → LTerm → LTerm → Prop where
  | var (l i) : DevelopmentEval (.var i) (.var l i) (.var l i)
  | lam : DevelopmentEval b c c' → DevelopmentEval (.lam b) (.lam alpha c) (.lam alpha c')
  | app : DevelopmentEval f g g' → DevelopmentEval a c c' →
      DevelopmentEval (.app tags f a) (.app beta g c) (.app beta g' c')
  | red : DevelopmentEval b c c' → DevelopmentEval a e e' →
      DevelopmentEval (.red tags b a) (.app beta (.lam alpha c) e) (LTerm.contract beta alpha c' e')

namespace DevelopmentEval
private theorem erase_lam {f : LTerm} (h : f.erase=Term.lam b) :
    ∃ alpha c, f=.lam alpha c ∧ c.erase=b := by
  cases f with
  | var => simp [LTerm.erase] at h
  | app => simp [LTerm.erase] at h
  | lam alpha c => exact ⟨alpha,c,rfl,Term.lam.inj h⟩

theorem exists_eval (m : Marked) (t : LTerm) (same : m.erase=t.erase) :
    ∃ u, DevelopmentEval m t u := by
  induction m generalizing t with
  | var i =>
    cases t with
    | var l j =>
      simp only [Marked.erase,LTerm.erase,Term.var.injEq] at same
      cases same; exact ⟨_,.var _ _⟩
    | app => simp [Marked.erase,LTerm.erase] at same
    | lam => simp [Marked.erase,LTerm.erase] at same
  | lam b hb =>
    obtain ⟨alpha,c,rfl,hc⟩ := erase_lam same.symm
    obtain ⟨u,hu⟩ := hb c hc.symm
    exact ⟨_,.lam hu⟩
  | app tags f a hf ha =>
    cases t with
    | var => simp [Marked.erase,LTerm.erase] at same
    | lam => simp [Marked.erase,LTerm.erase] at same
    | app beta g c =>
      simp only [Marked.erase,LTerm.erase,Term.app.injEq] at same
      obtain ⟨u,hu⟩ := hf g same.1
      obtain ⟨v,hv⟩ := ha c same.2
      exact ⟨_,.app hu hv⟩
  | red tags b a hb ha =>
    cases t with
    | var => simp [Marked.erase,LTerm.erase] at same
    | lam => simp [Marked.erase,LTerm.erase] at same
    | app beta g e =>
      simp only [Marked.erase,LTerm.erase,Term.app.injEq] at same
      obtain ⟨alpha,c,rfl,hc⟩ := erase_lam same.1.symm
      obtain ⟨u,hu⟩ := hb c hc.symm
      obtain ⟨v,hv⟩ := ha e same.2
      exact ⟨_,.red hu hv⟩

theorem deterministic (h : DevelopmentEval m t u) (k : DevelopmentEval m t v) : u=v := by
  induction h generalizing v with
  | var => cases k; rfl
  | lam _ ih => cases k with | lam k => exact congrArg (LTerm.lam _) (ih k)
  | app _ _ hf ha =>
    cases k with | app kf ka => rw [hf kf,ha ka]
  | red _ _ hb ha =>
    cases k with | red kb ka => rw [hb kb,ha ka]

theorem rename (h : DevelopmentEval m t u) (rho : Nat → Nat) :
    DevelopmentEval (m.rename rho) (t.rename rho) (u.rename rho) := by
  induction h generalizing rho with
  | var => exact .var _ _
  | lam _ ih => exact .lam (ih _)
  | app _ _ hf ha => exact .app (hf _) (ha _)
  | red _ _ hb ha => simpa only [LTerm.rename_contract] using
      (DevelopmentEval.red (tags := _) (beta := _) (alpha := _) (hb _) (ha _))

theorem prepend (h : DevelopmentEval m t u) (p : Label) :
    DevelopmentEval m (t.prepend p) (u.prepend p) := by
  cases h with
  | var => exact .var _ _
  | lam h => exact .lam h
  | app hf ha => exact .app hf ha
  | red hb ha => simpa only [← LTerm.contract_prepend_beta] using
      (DevelopmentEval.red (tags := _) (beta := _) (alpha := _) hb ha)

inductive Value : Marked → LTerm.SubValue → LTerm.SubValue → Prop where
  | keep (i) : Value (.var i) (.keep i) (.keep i)
  | put : DevelopmentEval m t u → Value m (.put t) (.put u)

theorem lift_values (h : ∀ i, Value (sigma i) (tau i) (upsilon i)) :
    ∀ i, Value (Marked.liftSub sigma i) (LTerm.lift tau i) (LTerm.lift upsilon i) := by
  intro i
  cases i with
  | zero => exact .keep _
  | succ i =>
    have hi := h i
    simp only [Marked.liftSub,LTerm.lift]
    generalize hm : sigma i=mi at hi ⊢
    generalize ht : tau i=ti at hi ⊢
    generalize hu : upsilon i=ui at hi ⊢
    cases hi with
    | keep => exact .keep _
    | put h => exact .put (h.rename Nat.succ)

theorem subst (h : DevelopmentEval m t u) (hs : ∀ i, Value (sigma i) (tau i) (upsilon i)) :
    DevelopmentEval (m.subst sigma) (t.subst tau) (u.subst upsilon) := by
  induction h generalizing sigma tau upsilon with
  | var l i =>
    have hi := hs i
    simp only [Marked.subst,LTerm.subst]
    generalize hm : sigma i=mi at hi ⊢
    generalize ht : tau i=ti at hi ⊢
    generalize hu : upsilon i=ui at hi ⊢
    cases hi with
    | keep => exact .var _ _
    | put h => exact h.prepend l
  | lam _ ih => exact .lam (ih (lift_values hs))
  | app _ _ hf ha => exact .app (hf hs) (ha hs)
  | red _ _ hb ha => simpa only [LTerm.subst_contract] using
      (DevelopmentEval.red (tags := _) (beta := _) (alpha := _) (hb (lift_values hs)) (ha hs))

theorem contract (hb : DevelopmentEval b c c') (ha : DevelopmentEval a e e') :
    DevelopmentEval (Marked.contract b a) (LTerm.contract beta alpha c e)
      (LTerm.contract beta alpha c' e') := by
  apply DevelopmentEval.prepend
  apply hb.subst
  intro i
  cases i with
  | zero => exact .put (ha.prepend alpha.under)
  | succ i => exact .keep _

theorem of_normal (h : DevelopmentEval m t u) (normal : Marked.Normal m) : t=u := by
  induction h with
  | var => rfl
  | lam _ ih => exact congrArg (LTerm.lam _) (ih normal)
  | app _ _ hf ha => rw [hf normal.1,ha normal.2]
  | red => exact False.elim normal

/-- Every synchronous selected step leaves the evaluated labelled result
unchanged. New redexes have no active constructor and are not contracted. -/
theorem step (evaluation : DevelopmentEval m t result) (hm : Marked.StepAt p m n)
    (hs : StepAt p t u) : DevelopmentEval n u result := by
  induction hm generalizing t u result with
  | root tags b a =>
    cases evaluation with
    | red hb ha => cases hs with | root => exact hb.contract ha
  | lam hm ih =>
    cases evaluation with
    | lam hb => cases hs with | body hs => exact .lam (ih hb hs)
  | appL hm ih =>
    cases evaluation with
    | app hf ha => cases hs with | fn hs => exact .app (ih hf hs) ha
  | appR hm ih =>
    cases evaluation with
    | app hf ha => cases hs with | arg hs => exact .app hf (ih ha hs)
  | redL hm ih =>
    cases evaluation with
    | red hb ha =>
      cases hs with | fn hs => cases hs with | body hs => exact .red (ih hb hs) ha
  | redR hm ih =>
    cases evaluation with
    | red hb ha => cases hs with | arg hs => exact .red hb (ih ha hs)

theorem history (evaluation : DevelopmentEval m t result) (hm : Marked.RelativeHistory ps m n)
    (hs : History ps t u) : DevelopmentEval n u result := by
  induction hm generalizing t u with
  | nil => cases hs; exact evaluation
  | cons hm _ ih =>
    cases hs with | cons hs tail => exact ih (evaluation.step hm hs) tail

/-- Any two actual complete developments from the same marked/labelled
source give literally equal labelled targets, independent of their schedules. -/
theorem complete_unique (hm : Marked.RelativeHistory ps m n) (hn : Marked.Normal n)
    (km : Marked.RelativeHistory qs m n') (kn : Marked.Normal n')
    (source : m.erase=t.erase) (hs : History ps t u) (ks : History qs t v) : u=v := by
  obtain ⟨result,eval⟩ := DevelopmentEval.exists_eval m t source
  exact ((eval.history hm hs).of_normal hn).trans ((eval.history km ks).of_normal kn).symm
end DevelopmentEval
end Lamping.Lambda.Labelled


