import Lamping.Lambda.LabelHistories
namespace Lamping.Lambda.Labelled

-- AG6.2.13 atomic label substitutions preserve over/under structure.
mutual
  def Label.relabel (s : Nat → Label) : Label → Label
    | .single l => l.relabel s
    | .cons l a => (l.relabel s).concat (a.relabel s)
  def Letter.relabel (s : Nat → Label) : Letter → Label
    | .atom n => s n
    | .over a => (a.relabel s).over
    | .under a => (a.relabel s).under
end

@[simp] theorem Label.relabel_atom (s) (n) : (Label.atom n).relabel s=s n := rfl
@[simp] theorem Label.relabel_over (s : Nat → Label) (a : Label) : a.over.relabel s=(a.relabel s).over := rfl
@[simp] theorem Label.relabel_under (s : Nat → Label) (a : Label) : a.under.relabel s=(a.relabel s).under := rfl

theorem Label.relabel_concat (s : Nat → Label) : ∀ (a b : Label),
    (a.concat b).relabel s=(a.relabel s).concat (b.relabel s)
  | .single _, _ => rfl
  | .cons l a, b => by simp [Label.concat,Label.relabel,relabel_concat,Label.concat_assoc]

mutual
  theorem Label.relabel_identity : ∀ (a : Label), a.relabel Label.atom=a
    | .single l => by simpa [Label.relabel] using Letter.relabel_identity l
    | .cons l a => by simp [Label.relabel,Letter.relabel_identity,Label.relabel_identity,Label.concat]
  theorem Letter.relabel_identity : ∀ (l : Letter), l.relabel Label.atom=Label.single l
    | .atom _ => rfl
    | .over a => by simp [Letter.relabel,Label.relabel_identity,Label.over]
    | .under a => by simp [Letter.relabel,Label.relabel_identity,Label.under]
end

mutual
  theorem Label.relabel_comp (s t : Nat → Label) : ∀ (a : Label),
      (a.relabel s).relabel t=a.relabel (fun n => (s n).relabel t)
    | .single l => by simpa [Label.relabel] using Letter.relabel_comp s t l
    | .cons l a => by simp [Label.relabel,Label.relabel_concat,Letter.relabel_comp,Label.relabel_comp]
  theorem Letter.relabel_comp (s t : Nat → Label) : ∀ (l : Letter),
      (l.relabel s).relabel t=l.relabel (fun n => (s n).relabel t)
    | .atom _ => rfl
    | .over a => by simp [Letter.relabel,Label.relabel_comp]
    | .under a => by simp [Letter.relabel,Label.relabel_comp]
end

namespace LTerm
def relabel (s : Nat → Label) : LTerm → LTerm
  | .var l i => .var (l.relabel s) i
  | .app l f a => .app (l.relabel s) (relabel s f) (relabel s a)
  | .lam l b => .lam (l.relabel s) (relabel s b)

@[simp] theorem erase_relabel (s) (t : LTerm) : (t.relabel s).erase=t.erase := by
  induction t <;> simp_all [relabel,erase]

theorem relabel_identity (t : LTerm) : t.relabel Label.atom=t := by
  induction t <;> simp_all [relabel,Label.relabel_identity]

theorem relabel_comp (s t) (u : LTerm) :
    (u.relabel s).relabel t=u.relabel (fun n => (s n).relabel t) := by
  induction u <;> simp_all [relabel,Label.relabel_comp]

theorem relabel_prepend (s) (a : Label) (t : LTerm) :
    (t.prepend a).relabel s=(t.relabel s).prepend (a.relabel s) := by
  cases t <;> simp [prepend,relabel,Label.relabel_concat]

theorem relabel_rename (s) (t : LTerm) (rho : Nat → Nat) :
    (t.rename rho).relabel s=(t.relabel s).rename rho := by
  induction t generalizing rho <;> simp_all [rename,relabel]

namespace SubValue
def relabel (s : Nat → Label) : SubValue → SubValue
  | .keep i => .keep i
  | .put t => .put (t.relabel s)
end SubValue

theorem relabel_lift (s) (sigma : Nat → SubValue) (i : Nat) :
    (lift sigma i).relabel s=lift (fun i => (sigma i).relabel s) i := by
  cases i with
  | zero => rfl
  | succ i => cases h : sigma i <;> simp [lift,h,SubValue.relabel,relabel_rename]

theorem relabel_subst (s) (t : LTerm) (sigma : Nat → SubValue) :
    (t.subst sigma).relabel s=(t.relabel s).subst (fun i => (sigma i).relabel s) := by
  induction t generalizing sigma with
  | var l i => cases h : sigma i <;> simp [subst,h,relabel,SubValue.relabel,relabel_prepend]
  | app l f a hf ha => simp [subst,relabel,hf,ha]
  | lam l b hb =>
    simp only [subst,relabel,hb]
    congr 1; congr 1; funext i
    exact relabel_lift s sigma i

theorem relabel_contract (s) (beta alpha : Label) (b a : LTerm) :
    (contract beta alpha b a).relabel s=
      contract (beta.relabel s) (alpha.relabel s) (b.relabel s) (a.relabel s) := by
  simp only [contract,relabel_prepend,Label.relabel_concat,Label.relabel_over,
    relabel_subst]
  congr 1; congr 1; funext i
  cases i <;> simp [single,SubValue.relabel,relabel_prepend]
end LTerm

theorem StepAt.relabel (h : StepAt p t u) (s : Nat → Label) :
    StepAt p (t.relabel s) (u.relabel s) := by
  induction h with
  | root beta alpha b a => simpa only [LTerm.relabel,LTerm.relabel_contract] using (StepAt.root (beta.relabel s) (alpha.relabel s) (b.relabel s) (a.relabel s))
  | fn _ ih => exact .fn ih
  | arg _ ih => exact .arg ih
  | body _ ih => exact .body ih

/-- AG6.2.13(ii): actual reductions commute with atomic relabelling. -/
theorem History.relabel (h : History ps t u) (s : Nat → Label) :
    History ps (t.relabel s) (u.relabel s) := by
  induction h with
  | nil => exact .nil _
  | cons h _ ih => exact .cons (h.relabel s) ih

end Lamping.Lambda.Labelled


