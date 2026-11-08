import Lamping.Lambda.LabelSubstitution
import Lamping.Lambda.DegreeFamily
import Lamping.Lambda.InitialFamilies
namespace Lamping.Lambda.Labelled

/-- Relates actual old-name syntax to the transported labelled term.
Tags constrain the lambda degree, never the application's exterior label. -/
inductive DegreeAligned (d : Path → Option Label) : Marked → LTerm → Prop where
  | var (l i) : DegreeAligned d (.var i) (.var l i)
  | lam : DegreeAligned d b c → DegreeAligned d (.lam b) (.lam alpha c)
  | app : DegreeAligned d f g → DegreeAligned d a c →
      (∀ r ∈ tags, ∃ alpha b, g=.lam alpha b ∧ d r=some alpha) →
      DegreeAligned d (.app tags f a) (.app beta g c)
  | red : DegreeAligned d b c → DegreeAligned d a e →
      (∀ r ∈ tags, d r=some alpha) →
      DegreeAligned d (.red tags b a) (.app beta (.lam alpha c) e)

private theorem mem_rootTrace {r p : Path} {tags : List Path}
    (h : p ∈ (if r ∈ tags then [[]] else [])) : p=[] ∧ r∈tags := by
  split at h <;> simp_all

namespace DegreeAligned
theorem erase (h : DegreeAligned d m t) : m.erase=t.erase := by
  induction h with
  | var => rfl
  | lam _ ih => exact congrArg Term.lam ih
  | app _ _ _ hf ha => simp only [Marked.erase,LTerm.erase,hf,ha]
  | red _ _ _ hb ha => simp only [Marked.erase,LTerm.erase,hb,ha]

theorem prepend (h : DegreeAligned d m t) (a : Label) : DegreeAligned d m (t.prepend a) := by
  cases h with
  | var => exact .var _ _
  | lam h => exact .lam h
  | app hf ha tags => exact .app hf ha tags
  | red hb ha tags => exact .red hb ha tags

theorem rename (h : DegreeAligned d m t) (rho : Nat → Nat) :
    DegreeAligned d (m.rename rho) (t.rename rho) := by
  induction h generalizing rho with
  | var => exact .var _ _
  | lam _ ih => exact .lam (ih _)
  | app hf ha tags hfi hai =>
    apply DegreeAligned.app (hfi rho) (hai rho)
    intro r hr
    obtain ⟨alpha,b,hb,hd⟩ := tags r hr
    cases hb
    exact ⟨alpha,_,rfl,hd⟩
  | red hb ha tags hbi hai => exact .red (hbi _) (hai _) tags

/-- Kept variables retain their occurrence's own label. -/
def Value (d : Path → Option Label) (m : Marked) : LTerm.SubValue → Prop
  | .keep i => m=.var i
  | .put t => DegreeAligned d m t

theorem lift_values (h : ∀ i, Value d (sigma i) (tau i)) :
    ∀ i, Value d (Marked.liftSub sigma i) (LTerm.lift tau i) := by
  intro i
  cases i with
  | zero => rfl
  | succ i =>
    cases ht : tau i with
    | keep j =>
      have hm : sigma i=.var j := by simpa [Value,ht] using h i
      simp [LTerm.lift,Marked.liftSub,ht,Value,hm,Marked.rename]
    | put t =>
      have hm : DegreeAligned d (sigma i) t := by simpa [Value,ht] using h i
      simpa only [Marked.liftSub,LTerm.lift,ht,Value] using hm.rename Nat.succ

theorem subst (h : DegreeAligned d m t) (hs : ∀ i, Value d (sigma i) (tau i)) :
    DegreeAligned d (m.subst sigma) (t.subst tau) := by
  induction h generalizing sigma tau with
  | var l i =>
    cases ht : tau i with
    | keep j =>
      have hm : sigma i=.var j := by simpa [Value,ht] using hs i
      simpa [Marked.subst,LTerm.subst,ht,hm] using DegreeAligned.var (d := d) l j
    | put u =>
      have hm : DegreeAligned d (sigma i) u := by simpa [Value,ht] using hs i
      simpa only [Marked.subst,LTerm.subst,ht] using hm.prepend l
  | lam h ih => exact .lam (ih (lift_values hs))
  | app hf ha tags hfi hai =>
    apply DegreeAligned.app (hfi hs) (hai hs)
    intro r hr
    obtain ⟨alpha,b,hb,hd⟩ := tags r hr
    cases hb
    exact ⟨alpha,_,rfl,hd⟩
  | red hb ha tags hbi hai => exact .red (hbi (lift_values hs)) (hai hs) tags

theorem contract (hb : DegreeAligned d b c) (ha : DegreeAligned d a e) :
    DegreeAligned d (Marked.contract b a) (LTerm.contract beta alpha c e) := by
  apply DegreeAligned.prepend
  apply hb.subst
  intro i
  cases i with
  | zero => exact ha.prepend alpha.under
  | succ i => rfl

/-- All occurrences of each actual transported old name keep its degree. -/
theorem trace_degree (h : DegreeAligned d m t) (hp : p ∈ m.tracePositions r) :
    t.degreeAt p=d r := by
  induction h generalizing p with
  | var => simp [Marked.tracePositions] at hp
  | lam h ih =>
    simp only [Marked.tracePositions,List.mem_map] at hp
    obtain ⟨q,hq,rfl⟩ := hp
    exact ih hq
  | app hf ha tags hfi hai =>
    simp only [Marked.tracePositions,List.mem_append,List.mem_map] at hp
    rcases hp with root | ⟨q,hq,rfl⟩ | ⟨q,hq,rfl⟩
    · obtain ⟨rfl,hr⟩ := mem_rootTrace root
      obtain ⟨alpha,b,rfl,hd⟩ := tags r hr
      exact hd.symm
    · exact hfi hq
    · exact hai hq
  | red hb ha tags hbi hai =>
    simp only [Marked.tracePositions,List.mem_append,List.mem_map] at hp
    rcases hp with root | ⟨q,hq,rfl⟩ | ⟨q,hq,rfl⟩
    · obtain ⟨rfl,hr⟩ := mem_rootTrace root
      exact (tags r hr).symm
    · exact hbi hq
    · exact hai hq
end DegreeAligned
end Lamping.Lambda.Labelled


namespace Lamping.Lambda.Labelled
private theorem StepAt.lambda_shape (h : StepAt p (.lam alpha b) u) :
    ∃ c, u=.lam alpha c := by cases h with | body _ => exact ⟨_,rfl⟩

/-- Synchronised real contractions preserve the old-name/degree relation. -/
theorem DegreeAligned.step (hm : Marked.ReductionAt p m n)
    (ht : DegreeAligned d m t) (hs : StepAt p t u) : DegreeAligned d n u := by
  induction hm generalizing t u with
  | appRoot tags b a =>
    cases ht with
    | app hf ha old =>
      cases hf with
      | lam hb => cases hs with | root => exact hb.contract ha
  | redRoot tags b a =>
    cases ht with
    | red hb ha old => cases hs with | root => exact hb.contract ha
  | lam hm ih =>
    cases ht with
    | lam hb => cases hs with | body hs => exact .lam (ih hb hs)
  | appL hm ih =>
    cases ht with
    | app hf ha old =>
      cases hs with
      | fn hs =>
        apply DegreeAligned.app (ih hf hs) ha
        intro r hr
        obtain ⟨alpha,b,hb,hd⟩ := old r hr
        cases hb
        obtain ⟨c,hc⟩ := hs.lambda_shape
        exact ⟨alpha,c,hc,hd⟩
  | appR hm ih =>
    cases ht with
    | app hf ha old => cases hs with | arg hs => exact .app hf (ih ha hs) old
  | redL hm ih =>
    cases ht with
    | red hb ha old =>
      cases hs with
      | fn hs => cases hs with | body hs => exact .red (ih hb hs) ha old
  | redR hm ih =>
    cases ht with
    | red hb ha old => cases hs with | arg hs => exact .red hb (ih ha hs) old

/-- Transport refers to the original old names for the entire common schedule. -/
theorem DegreeAligned.history (hm : Marked.History ps m n)
    (ht : DegreeAligned d m t) (hs : History ps t u) : DegreeAligned d n u := by
  induction hm generalizing t u with
  | nil => cases hs; exact ht
  | cons hm _ ih =>
    cases hs with
    | cons hs tail => exact ih (ht.step hm hs) tail
end Lamping.Lambda.Labelled

namespace Lamping.Lambda.Labelled
private theorem subterm_append (t : LTerm) (p q : Path) :
    t.subterm (p++q)=(t.subterm p).bind (fun u => u.subterm q) := by
  induction p generalizing t with
  | nil => simp [LTerm.subterm]
  | cons s p ih => cases t <;> cases s <;> simp [LTerm.subterm,ih]

/-- Initial old names refer to their actual initial lambda labels. -/
theorem DegreeAligned.markAt {original : LTerm} (t : LTerm) (lookup : original.subterm p=some t) (F : List Path) :
    DegreeAligned original.degreeAt (Marked.markAt F t.erase p) t := by
  induction t generalizing p with
  | var l i => exact .var _ _
  | lam alpha b hb =>
    apply DegreeAligned.lam
    apply hb
    rw [subterm_append,lookup]; simp [LTerm.subterm]
  | app beta f a hf ha =>
    have hfa : original.subterm (p++[.fn])=some f := by rw [subterm_append,lookup]; simp [LTerm.subterm]
    have haa : original.subterm (p++[.arg])=some a := by rw [subterm_append,lookup]; simp [LTerm.subterm]
    have hff := hf hfa
    have haa' := ha haa
    cases f with
    | var l i => exact .app hff haa' (by simp)
    | app l g c => exact .app hff haa' (by simp)
    | lam alpha b =>
      cases hff with
      | lam hbb =>
        have hd : original.degreeAt p=some alpha := by simp [LTerm.degreeAt,lookup,LTerm.degree]
        simp only [LTerm.erase,Marked.markAt]
        split
        · exact .red hbb haa' (by intro r hr; simpa only [List.mem_singleton.mp hr] using hd)
        · exact .app (.lam hbb) haa' (by
            intro r hr; exact ⟨alpha,b,rfl,by simpa only [List.mem_singleton.mp hr] using hd⟩)

theorem DegreeAligned.initial (t : LTerm) (F : List Path) :
    DegreeAligned t.degreeAt (Marked.mark F t.erase) t := DegreeAligned.markAt t (by simp [LTerm.subterm]) F

/-- AG5.3.36, for the project's genuine old-name residual relation, for an
arbitrary existing labelling and arbitrary real contraction schedule. -/
theorem Derivation.residual_degree (h : Derivation m n) (t u : LTerm)
    (source : t.erase=m) (transport : History h.paths t u)
    (r : RedexOcc m) (s : RedexOcc n) (residual : h.Residual r s) :
    u.degreeAt s.val=t.degreeAt r.val := by
  obtain ⟨v,hv,_,hs⟩ := residual
  have align := DegreeAligned.initial t []
  rw [source] at align
  exact (align.history hv transport).trace_degree hs
end Lamping.Lambda.Labelled




namespace Lamping.Lambda.Labelled
/-- The forward degree/family result already applies to every member of an
initial redex's family, along arbitrary actual histories and labellings. -/
theorem initial_family_degree (r : RedexOcc m) (a : RedexWithHistory m)
    (family : FamilyEq ⟨m,.nil m,r⟩ a) (t u : LTerm)
    (source : t.erase=m) (transport : History a.history.derivation.paths t u) :
    u.degreeAt a.redex.val=t.degreeAt r.val :=
  Derivation.residual_degree a.history.derivation t u source transport r a.redex
    ((initial_family_iff r a).mp family)
end Lamping.Lambda.Labelled
