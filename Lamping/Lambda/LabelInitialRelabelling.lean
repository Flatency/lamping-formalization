import Lamping.Lambda.LabelResiduals
namespace Lamping.Lambda.Labelled

/-- The local INIT enumeration may be used as a basis for a substitution;
this function recovers the existing target labels, without changing its history. -/
def initialRelabelling : LTerm → Nat → Nat → Label
  | .var l _, k, n => if n=k then l else Label.atom n
  | .lam l b, k, n => if n=k then l else initialRelabelling b (k+1) n
  | .app l f a, k, n => if n=k then l else
      if n<k+1+nodeCount f.erase then initialRelabelling f (k+1) n
      else initialRelabelling a (k+1+nodeCount f.erase) n

/-- INIT labels lie in a known finite interval, so substitutions only need
agree on that interval. -/
theorem relabel_initFrom_congr (t : Term) (k : Nat) (s r : Nat → Label)
    (agree : ∀ n, k≤n → n<k+nodeCount t → s n=r n) :
    (initFrom k t).relabel s=(initFrom k t).relabel r := by
  induction t generalizing k with
  | var i =>
    have hk := agree k (Nat.le_refl _) (by simp [nodeCount])
    simp [initFrom,LTerm.relabel,hk]
  | lam b hb =>
    have hk := agree k (Nat.le_refl _) (by simp [nodeCount])
    simp only [initFrom,LTerm.relabel,Label.relabel_atom,hk]
    congr 1
    apply hb
    intro n hn hlt
    exact agree n (by omega) (by simp only [nodeCount]; omega)
  | app f a hf ha =>
    have hk := agree k (Nat.le_refl _) (by simp [nodeCount])
    simp only [initFrom,LTerm.relabel,Label.relabel_atom,hk]
    congr 1
    · apply hf
      intro n hn hlt
      exact agree n (by omega) (by simp only [nodeCount]; omega)
    · apply ha
      intro n hn hlt
      exact agree n (by omega) (by simp only [nodeCount]; omega)

/-- Every existing labelled term factors through its local INIT enumeration.
This is an explicit construction of the substitution, not a chosen witness. -/
theorem initialRelabelling_factor (t : LTerm) (k : Nat) :
    (initFrom k t.erase).relabel (initialRelabelling t k)=t := by
  induction t generalizing k with
  | var l i => simp [LTerm.erase,initFrom,LTerm.relabel,initialRelabelling]
  | lam l b hb =>
    simp only [LTerm.erase,initFrom,LTerm.relabel,Label.relabel_atom]
    have root : initialRelabelling (.lam l b) k k=l := by simp [initialRelabelling]
    rw [root]
    congr 1
    rw [relabel_initFrom_congr b.erase (k+1) (initialRelabelling (.lam l b) k)
      (initialRelabelling b (k+1)) (by
        intro n hn _
        have ne : n≠k := by omega
        simp [initialRelabelling,ne])]
    exact hb _
  | app l f a hf ha =>
    simp only [LTerm.erase,initFrom,LTerm.relabel,Label.relabel_atom]
    have root : initialRelabelling (.app l f a) k k=l := by simp [initialRelabelling]
    rw [root]
    congr 1
    · rw [relabel_initFrom_congr f.erase (k+1) (initialRelabelling (.app l f a) k)
        (initialRelabelling f (k+1)) (by
          intro n hn hlt
          have ne : n≠k := by omega
          simp [initialRelabelling,ne,hlt])]
      exact hf _
    · rw [relabel_initFrom_congr a.erase (k+1+nodeCount f.erase) (initialRelabelling (.app l f a) k)
        (initialRelabelling a (k+1+nodeCount f.erase)) (by
          intro n hn _
          have ne : n≠k := by omega
          have nt : ¬ n<k+1+nodeCount f.erase := by omega
          simp [initialRelabelling,ne,nt])]
      exact ha _

theorem initialRelabelling_mem (t : LTerm) (k n : Nat)
    (lower : k≤n) (upper : n<k+nodeCount t.erase) : initialRelabelling t k n∈t.labels := by
  induction t generalizing k with
  | var l i =>
    have eq : n=k := by simp only [LTerm.erase,nodeCount] at upper; omega
    simp [initialRelabelling,eq,LTerm.labels]
  | lam l b hb =>
    by_cases eq : n=k
    · simp [initialRelabelling,eq,LTerm.labels]
    · have hn : k+1≤n := by omega
      have hu : n<k+1+nodeCount b.erase := by simp only [LTerm.erase,nodeCount] at upper; omega
      exact List.mem_cons_of_mem _ (by simpa only [initialRelabelling,if_neg eq] using hb (k+1) hn hu)
  | app l f a hf ha =>
    by_cases eq : n=k
    · simp [initialRelabelling,eq,LTerm.labels]
    · by_cases small : n<k+1+nodeCount f.erase
      · have hn : k+1≤n := by omega
        exact List.mem_cons_of_mem _ (List.mem_append_left _ (by
          simpa only [initialRelabelling,if_neg eq,if_pos small] using hf (k+1) hn small))
      · have hn : k+1+nodeCount f.erase≤n := by omega
        have hu : n<k+1+nodeCount f.erase+nodeCount a.erase := by
          simp only [LTerm.erase,nodeCount] at upper; omega
        exact List.mem_cons_of_mem _ (List.mem_append_right _ (by
          simpa only [initialRelabelling,if_neg eq,if_neg small] using ha (k+1+nodeCount f.erase) hn hu))

end Lamping.Lambda.Labelled


namespace Lamping.Lambda.Labelled
mutual
  def Label.Supported (s : Nat → Prop) : Label → Prop
    | .single l => l.Supported s
    | .cons l a => l.Supported s ∧ a.Supported s
  def Letter.Supported (s : Nat → Prop) : Letter → Prop
    | .atom n => s n
    | .over a | .under a => a.Supported s
end

theorem Label.supported_concat (s : Nat → Prop) : ∀ (a b : Label),
    (a.concat b).Supported s ↔ a.Supported s ∧ b.Supported s
  | .single l,b => Iff.rfl
  | .cons l a,b => by simp [Label.concat,Label.Supported,supported_concat,and_assoc]

namespace LTerm
def Supported (s : Nat → Prop) : LTerm → Prop
  | .var l _ => l.Supported s
  | .lam l b => l.Supported s ∧ b.Supported s
  | .app l f a => l.Supported s ∧ f.Supported s ∧ a.Supported s

theorem supported_iff (s) (t : LTerm) :
    t.Supported s ↔ ∀ l∈t.labels, l.Supported s := by
  induction t with
  | var l i => simp [Supported,labels]
  | lam l b hb => simp [Supported,labels,hb]
  | app l f a hf ha => simp [Supported,labels,hf,ha,or_imp,forall_and]

theorem Supported.rename {t : LTerm} {s : Nat → Prop} (h : t.Supported s) (rho : Nat → Nat) : (t.rename rho).Supported s := by
  induction t generalizing rho with
  | var => exact h
  | lam _ _ ih => exact ⟨h.1,ih h.2 _⟩
  | app _ _ _ hf ha => exact ⟨h.1,hf h.2.1 _,ha h.2.2 _⟩

theorem Supported.prepend {t : LTerm} {s : Nat → Prop} (h : t.Supported s) (a : Label) (ha : a.Supported s) :
    (t.prepend a).Supported s := by
  cases t with
  | var => exact (Label.supported_concat _ _ _).mpr ⟨ha,h⟩
  | lam => exact ⟨(Label.supported_concat _ _ _).mpr ⟨ha,h.1⟩,h.2⟩
  | app => exact ⟨(Label.supported_concat _ _ _).mpr ⟨ha,h.1⟩,h.2⟩

def SubValue.Supported (s : Nat → Prop) : SubValue → Prop
  | .keep _ => True
  | .put t => t.Supported s

theorem Supported.subst {t : LTerm} {s : Nat → Prop} {sigma : Nat → SubValue} (h : t.Supported s) (hs : ∀ i, (sigma i).Supported s) :
    (t.subst sigma).Supported s := by
  induction t generalizing sigma with
  | var l i =>
    cases he : sigma i with
    | keep j => simpa only [LTerm.subst,he,Supported] using h
    | put u =>
      have hu : u.Supported s := by simpa [SubValue.Supported,he] using hs i
      simpa only [LTerm.subst,he] using hu.prepend l h
  | app l f a hf ha => exact ⟨h.1,hf h.2.1 hs,ha h.2.2 hs⟩
  | lam l b hb =>
    refine ⟨h.1,hb h.2 ?_⟩
    intro i
    cases i with
    | zero => trivial
    | succ i =>
      cases he : sigma i with
      | keep j => simp [lift,he,SubValue.Supported]
      | put u =>
        have hu : u.Supported s := by simpa [SubValue.Supported,he] using hs i
        simpa only [lift,he,SubValue.Supported] using hu.rename Nat.succ

theorem Supported.contract {b a : LTerm} {s : Nat → Prop} {beta alpha : Label} (hb : b.Supported s) (ha : a.Supported s)
    (hbeta : beta.Supported s) (halpha : alpha.Supported s) :
    (contract beta alpha b a).Supported s := by
  apply Supported.prepend
  · apply hb.subst
    intro i
    cases i with
    | zero => exact ha.prepend alpha.under halpha
    | succ i => trivial
  · exact (Label.supported_concat _ _ _).mpr ⟨hbeta,halpha⟩
end LTerm

theorem StepAt.supported (h : StepAt p t u) (ht : t.Supported s) : u.Supported s := by
  induction h with
  | root => exact ht.2.1.2.contract ht.2.2 ht.1 ht.2.1.1
  | fn _ ih => exact ⟨ht.1,ih ht.2.1,ht.2.2⟩
  | arg _ ih => exact ⟨ht.1,ht.2.1,ih ht.2.2⟩
  | body _ ih => exact ⟨ht.1,ih ht.2⟩

theorem History.supported (h : History ps t u) (ht : t.Supported s) : u.Supported s := by
  induction h with
  | nil => exact ht
  | cons h _ ih => exact ih (h.supported ht)

theorem INIT.supported (hi : INIT t) : t.Supported (fun n => Label.atom n∈t.labels) := by
  rw [LTerm.supported_iff]
  intro l hl
  obtain ⟨n,rfl⟩ := hi.1 l hl
  exact hl

/-- AG6.2.13(i): the explicit reduction-induced target substitution factors
the existing labelling through N^I, with all its relevant atoms in M^I. -/
theorem History.initial_relabelling (h : History ps t u) (hi : INIT t) :
    (initLabels u.erase).relabel (initialRelabelling u 0)=u ∧
      ∀ n, n<nodeCount u.erase →
        (initialRelabelling u 0 n).Supported (fun a => Label.atom a∈t.labels) := by
  refine ⟨initialRelabelling_factor u 0,?_⟩
  intro n hn
  have mem := initialRelabelling_mem u 0 n (Nat.zero_le _) (by simpa using hn)
  exact (LTerm.supported_iff _ u).mp (h.supported hi.supported) _ mem
end Lamping.Lambda.Labelled




namespace Lamping.Lambda.Labelled
/-- An INIT basis determines atomic substitutions on every relevant atom. -/
theorem relabel_initFrom_injective (t : Term) (k : Nat) (s r : Nat → Label)
    (same : (initFrom k t).relabel s=(initFrom k t).relabel r)
    (lower : k≤n) (upper : n<k+nodeCount t) : s n=r n := by
  induction t generalizing k with
  | var i =>
    have eq : n=k := by simp only [nodeCount] at upper; omega
    simpa [initFrom,LTerm.relabel,eq] using same
  | lam b hb =>
    simp only [initFrom,LTerm.relabel,Label.relabel_atom,LTerm.lam.injEq] at same
    by_cases eq : n=k
    · simpa only [eq] using same.1
    · exact hb (k+1) same.2 (by omega) (by simp only [nodeCount] at upper; omega)
  | app f a hf ha =>
    simp only [initFrom,LTerm.relabel,Label.relabel_atom,LTerm.app.injEq] at same
    by_cases eq : n=k
    · simpa only [eq] using same.1
    · by_cases small : n<k+1+nodeCount f
      · exact hf (k+1) same.2.1 (by omega) small
      · exact ha (k+1+nodeCount f) same.2.2 (by omega) (by simp only [nodeCount] at upper; omega)

/-- Natural composition of the concrete induced substitutions, restricted to
the actual atomic basis of the final term. A local INIT basis is only a proof
coordinate system: the global labelled history remains t→u→v throughout. -/
theorem History.initial_relabelling_comp (global : History qs u v)
    (localHistory : History qs (initLabels u.erase) z) :
    z.erase=v.erase ∧ ∀ n, n<nodeCount v.erase →
      initialRelabelling v 0 n=
        (initialRelabelling z 0 n).relabel (initialRelabelling u 0) := by
  have localRelabel := localHistory.relabel (initialRelabelling u 0)
  simp only [initLabels] at localRelabel
  rw [initialRelabelling_factor u 0] at localRelabel
  have he : z.relabel (initialRelabelling u 0)=v := localRelabel.deterministic global
  have erased : z.erase=v.erase := by simpa only [LTerm.erase_relabel] using congrArg LTerm.erase he
  refine ⟨erased,?_⟩
  intro n hn
  have composed := congrArg (LTerm.relabel (initialRelabelling u 0)) (initialRelabelling_factor z 0)
  rw [LTerm.relabel_comp,he,erased] at composed
  apply relabel_initFrom_injective v.erase 0 _ _ _ (Nat.zero_le n) (by simpa using hn)
  exact (initialRelabelling_factor v 0).trans composed.symm

/-- The local coordinate history required above is always a real lift of the
chosen tail schedule; no relabelling or factorization oracle is assumed. -/
theorem History.local_initial_basis (global : History qs u v) :
    ∃ z, History qs (initLabels u.erase) z ∧ z.erase=v.erase ∧
      ∀ n, n<nodeCount v.erase → initialRelabelling v 0 n=
        (initialRelabelling z 0 n).relabel (initialRelabelling u 0) := by
  obtain ⟨z,hz,_⟩ := lift_history global.betaHistory (initLabels u.erase) (erase_initLabels _)
  obtain ⟨he,composition⟩ := global.initial_relabelling_comp hz
  exact ⟨z,hz,he,composition⟩
end Lamping.Lambda.Labelled

