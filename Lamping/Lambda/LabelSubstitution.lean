import Lamping.Lambda.LabelRelabelling
namespace Lamping.Lambda.Labelled.LTerm

theorem rename_congr {rho tau : Nat → Nat} (h : ∀ i, rho i=tau i) (t : LTerm) :
    rename rho t=rename tau t := by cases funext h; rfl

theorem rename_id (t : LTerm) : rename id t=t := by
  induction t with
  | var l i => rfl
  | app l f a hf ha => simp [rename,hf,ha]
  | lam l b hb =>
    have he : Lambda.liftRen id=id := by funext i; cases i <;> rfl
    simp [rename,he,hb]

theorem rename_comp (tau rho : Nat → Nat) (t : LTerm) :
    rename tau (rename rho t)=rename (tau ∘ rho) t := by
  induction t generalizing tau rho with
  | var l i => rfl
  | app l f a hf ha => simp [rename,hf,ha]
  | lam l b hb =>
    simp only [rename,hb]
    congr 1; apply rename_congr
    intro i; cases i <;> rfl

theorem rename_prepend (rho : Nat → Nat) (a : Label) (t : LTerm) :
    rename rho (prepend a t)=prepend a (rename rho t) := by cases t <;> rfl

theorem subst_prepend (sigma : Nat → SubValue) (a : Label) (t : LTerm) :
    subst sigma (prepend a t)=prepend a (subst sigma t) := by
  cases t with
  | var l i =>
    cases h : sigma i with
    | keep j => simp [subst,prepend,h]
    | put u => cases u <;> simp [subst,prepend,h,Label.concat_assoc]
  | app _ _ _ => rfl
  | lam _ _ => rfl

/-- Variable renaming of a label-preserving substitution value. -/
def SubValue.rename (rho : Nat → Nat) : SubValue → SubValue
  | .keep i => .keep (rho i)
  | .put t => .put (LTerm.rename rho t)

theorem rename_subst (rho : Nat → Nat) (sigma : Nat → SubValue) (t : LTerm) :
    rename rho (subst sigma t)=subst (fun i => (sigma i).rename rho) t := by
  induction t generalizing rho sigma with
  | var l i => cases h : sigma i <;> simp [subst,rename,SubValue.rename,h,rename_prepend]
  | app l f a hf ha => simp [subst,rename,hf,ha]
  | lam l b hb =>
    simp only [subst,rename,hb]
    congr 1; congr 1; funext i
    cases i with
    | zero => rfl
    | succ i =>
      cases h : sigma i <;> simp [lift,h,SubValue.rename,rename_comp,Lambda.liftRen]
      apply rename_congr
      intro i; rfl

theorem subst_rename (sigma : Nat → SubValue) (rho : Nat → Nat) (t : LTerm) :
    subst sigma (rename rho t)=subst (fun i => sigma (rho i)) t := by
  induction t generalizing sigma rho with
  | var l i => rfl
  | app l f a hf ha => simp [subst,rename,hf,ha]
  | lam l b hb =>
    simp only [rename,subst,hb]
    congr 1; congr 1; funext i
    cases i <;> rfl

theorem subst_id (t : LTerm) : subst SubValue.keep t=t := by
  induction t with
  | var l i => rfl
  | app l f a hf ha => simp [subst,hf,ha]
  | lam l b hb =>
    have he : lift SubValue.keep=SubValue.keep := by funext i; cases i <;> rfl
    simp [subst,he,hb]

/-- Composition retains a variable's existing label for a kept variable. -/
def SubValue.applySub (tau : Nat → SubValue) : SubValue → SubValue
  | .keep i => tau i
  | .put t => .put (subst tau t)

theorem subst_comp (tau sigma : Nat → SubValue) (t : LTerm) :
    subst tau (subst sigma t)=subst (fun i => (sigma i).applySub tau) t := by
  induction t generalizing tau sigma with
  | var l i => cases h : sigma i <;> simp [subst,h,SubValue.applySub,subst_prepend]
  | app l f a hf ha => simp [subst,hf,ha]
  | lam l b hb =>
    simp only [subst,hb]
    congr 1; congr 1; funext i
    cases i with
    | zero => rfl
    | succ i =>
      cases h : sigma i with
      | keep j => simp [lift,h,SubValue.applySub]
      | put t =>
        simp only [lift,h,SubValue.applySub]
        rw [subst_rename,rename_subst]
        congr 1

end Lamping.Lambda.Labelled.LTerm



namespace Lamping.Lambda.Labelled.LTerm
theorem rename_contract (rho) (beta alpha : Label) (b a : LTerm) :
    rename rho (contract beta alpha b a)=
      contract beta alpha (rename (Lambda.liftRen rho) b) (rename rho a) := by
  simp only [contract,rename_prepend,rename_subst,subst_rename]
  congr 1; congr 1; funext i
  cases i <;> simp [single,SubValue.rename,rename_prepend,Lambda.liftRen]

theorem subst_contract (sigma) (beta alpha : Label) (b a : LTerm) :
    subst sigma (contract beta alpha b a)=
      contract beta alpha (subst (lift sigma) b) (subst sigma a) := by
  simp only [contract,subst_prepend,subst_comp]
  congr 1; congr 1; funext i
  cases i with
  | zero => simp [single,SubValue.applySub,subst_prepend,lift]
  | succ i =>
    cases h : sigma i with
    | keep j => simp [single,lift,h,SubValue.applySub]
    | put t =>
      simp only [single,SubValue.applySub,lift,h,subst_rename]
      congr 1
      exact (subst_id t).symm
theorem contract_prepend_beta (p beta alpha : Label) (b a : LTerm) :
    contract (p.concat beta) alpha b a=(contract beta alpha b a).prepend p := by
  simp only [contract,prepend_assoc,Label.concat_assoc]
end Lamping.Lambda.Labelled.LTerm

