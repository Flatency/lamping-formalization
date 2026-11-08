import Lamping.Lambda.LabelPermutation
import Lamping.Lambda.ResidualSetComposition
namespace Lamping.Lambda.Labelled

/-- A nonempty prefix makes a word compound; atomicity uses outer length,
not the separate atomic-path norm of later chapters. -/
theorem Label.concat_not_atomic (a b : Label) : ¬ IsAtomic (a.concat b) := by
  rintro ⟨n,eq⟩
  have lengths := congrArg Label.length eq
  have ha := a.length_pos
  have hb := b.length_pos
  simp only [Label.length_concat,Label.atom,Label.length] at lengths
  omega

/-- Every atomic-degree redex still carries at least one genuine old tag.
The condition is one-way: compound degrees can also be old residuals. -/
inductive AtomicOrigins : Marked → LTerm → Prop where
  | var (l i) : AtomicOrigins (.var i) (.var l i)
  | lam : AtomicOrigins b c → AtomicOrigins (.lam b) (.lam l c)
  | app : AtomicOrigins f g → AtomicOrigins a b →
      (∀ l c,g=.lam l c → IsAtomic l → tags≠[]) →
      AtomicOrigins (.app tags f a) (.app beta g b)
  | red : AtomicOrigins b c → AtomicOrigins a e → tags≠[] →
      AtomicOrigins (.red tags b a) (.app beta (.lam alpha c) e)

namespace AtomicOrigins

theorem prepend (h : AtomicOrigins m t) (a : Label) : AtomicOrigins m (t.prepend a) := by
  cases h with
  | var => exact .var _ _
  | lam body => exact .lam body
  | app fn arg tags => exact .app fn arg tags
  | red body arg tags => exact .red body arg tags

theorem rename (h : AtomicOrigins m t) (rho : Nat → Nat) :
    AtomicOrigins (m.rename rho) (t.rename rho) := by
  induction h generalizing rho with
  | var => exact .var _ _
  | lam _ ih => exact .lam (ih _)
  | app fn arg tags hf ha =>
    apply AtomicOrigins.app (hf rho) (ha rho)
    intro l c eq atomic
    cases fn with
    | var => cases eq
    | lam body => cases eq; exact tags _ _ rfl atomic
    | app => cases eq
    | red => cases eq
  | red body arg tags hb ha => exact .red (hb _) (ha _) tags

def Value (m : Marked) : LTerm.SubValue → Prop
  | .keep i => m=.var i
  | .put t => AtomicOrigins m t

theorem lift_values (h : ∀ i, Value (sigma i) (tau i)) :
    ∀ i,Value (Marked.liftSub sigma i) (LTerm.lift tau i) := by
  intro i
  cases i with
  | zero => rfl
  | succ i =>
    cases ht : tau i with
    | keep j =>
      have hm : sigma i=.var j := by simpa [Value,ht] using h i
      simp [LTerm.lift,Marked.liftSub,ht,Value,hm,Marked.rename]
    | put t =>
      have hm : AtomicOrigins (sigma i) t := by simpa [Value,ht] using h i
      simpa only [Marked.liftSub,LTerm.lift,ht,Value] using hm.rename Nat.succ

theorem subst (h : AtomicOrigins m t) (values : ∀ i,Value (sigma i) (tau i)) :
    AtomicOrigins (m.subst sigma) (t.subst tau) := by
  induction h generalizing sigma tau with
  | var l i =>
    cases ht : tau i with
    | keep j =>
      have hm : sigma i=.var j := by simpa [Value,ht] using values i
      simpa [Marked.subst,LTerm.subst,ht,hm] using AtomicOrigins.var l j
    | put t =>
      have hm : AtomicOrigins (sigma i) t := by simpa [Value,ht] using values i
      simpa only [Marked.subst,LTerm.subst,ht] using hm.prepend l
  | lam body ih => exact .lam (ih (lift_values values))
  | @app f g a b tags beta fn arg old hf ha =>
    apply AtomicOrigins.app (hf values) (ha values)
    intro l c eq atomic
    cases fn with
    | var label i =>
      cases hv : tau i with
      | keep j => simp [LTerm.subst,hv] at eq
      | put t =>
        cases t with
        | var => simp [LTerm.subst,hv,LTerm.prepend] at eq
        | app => simp [LTerm.subst,hv,LTerm.prepend] at eq
        | lam alpha body =>
          simp only [LTerm.subst,hv,LTerm.prepend] at eq
          cases eq
          exact False.elim (Label.concat_not_atomic label alpha atomic)
    | lam body => cases eq; exact old _ _ rfl atomic
    | app => cases eq
    | red => cases eq
  | red body arg tags hb ha => exact .red (hb (lift_values values)) (ha values) tags

theorem contract (body : AtomicOrigins b c) (arg : AtomicOrigins a e) :
    AtomicOrigins (Marked.contract b a) (LTerm.contract beta alpha c e) := by
  apply AtomicOrigins.prepend
  apply body.subst
  intro i
  cases i with
  | zero => exact arg.prepend alpha.under
  | succ i => rfl
end AtomicOrigins

theorem StepAt.atomic_lambda_reflect {body : LTerm} (step : StepAt p t u)
    (shape : u=.lam l body) (atomic : IsAtomic l) : ∃ sourceBody,t=.lam l sourceBody := by
  cases step with
  | root beta alpha b a =>
    have labelEq := congrArg LTerm.label shape
    rw [LTerm.contract,label_prepend] at labelEq
    change ((beta.concat alpha.over).concat (b.subst (LTerm.single (a.prepend alpha.under))).label)=l at labelEq
    exact False.elim (Label.concat_not_atomic _ _ (labelEq ▸ atomic))
  | fn => cases shape
  | arg => cases shape
  | body => cases shape; exact ⟨_,rfl⟩

theorem AtomicOrigins.step (marked : Marked.ReductionAt p m n)
    (source : AtomicOrigins m t) (step : StepAt p t u) : AtomicOrigins n u := by
  induction marked generalizing t u with
  | appRoot tags b a =>
    cases source with
    | app fn arg old =>
      cases fn with
      | lam body => cases step with | root => exact body.contract arg
  | redRoot tags b a =>
    cases source with
    | red body arg old => cases step with | root => exact body.contract arg
  | lam marked ih =>
    cases source with
    | lam body => cases step with | body step => exact .lam (ih body step)
  | appL marked ih =>
    cases source with
    | app fn arg old =>
      cases step with
      | fn step =>
        apply AtomicOrigins.app (ih fn step) arg
        intro l body shape atomic
        obtain ⟨sourceBody,sourceShape⟩ := step.atomic_lambda_reflect shape atomic
        exact old l sourceBody sourceShape atomic
  | appR marked ih =>
    cases source with
    | app fn arg old => cases step with | arg step => exact .app fn (ih arg step) old
  | redL marked ih =>
    cases source with
    | red body arg old =>
      cases step with
      | fn step => cases step with | body step => exact .red (ih body step) arg old
  | redR marked ih =>
    cases source with
    | red body arg old => cases step with | arg step => exact .red body (ih arg step) old

theorem AtomicOrigins.history (marked : Marked.History ps m n)
    (source : AtomicOrigins m t) (history : History ps t u) : AtomicOrigins n u := by
  induction marked generalizing t u with
  | nil => cases history; exact source
  | cons head tail ih =>
    cases history with
    | cons step rest => exact ih (source.step head step) rest

theorem AtomicOrigins.markAt (t : LTerm) (selected : List Path) (p : Path) :
    AtomicOrigins (Marked.markAt selected t.erase p) t := by
  induction t generalizing p with
  | var l i => exact .var _ _
  | lam l b ih => exact .lam (ih _)
  | app l f a hf ha =>
    cases f with
    | var label i => exact .app (hf _) (ha _) (by intro l b eq; cases eq)
    | app label g b => exact .app (hf _) (ha _) (by intro l b eq; cases eq)
    | lam label b =>
      have body := hf (p++[.fn])
      cases body with
      | lam body =>
        simp only [LTerm.erase,Marked.markAt]
        split
        · exact .red body (ha _) (by simp)
        · exact .app (.lam body) (ha _) (by simp)

theorem AtomicOrigins.initial (t : LTerm) : AtomicOrigins (Marked.mark [] t.erase) t :=
  AtomicOrigins.markAt t [] []

theorem AtomicOrigins.atomic_trace (aligned : AtomicOrigins m t)
    (degree : t.degreeAt p=some l) (atomic : IsAtomic l) :
    ∃ r,p∈Marked.tracePositions r m := by
  induction p generalizing m t with
  | nil =>
    cases aligned with
    | var => simp [LTerm.degreeAt,LTerm.subterm,LTerm.degree] at degree
    | lam => simp [LTerm.degreeAt,LTerm.subterm,LTerm.degree] at degree
    | app fn arg old =>
      cases fn with
      | var => simp [LTerm.degreeAt,LTerm.subterm,LTerm.degree] at degree
      | app => simp [LTerm.degreeAt,LTerm.subterm,LTerm.degree] at degree
      | red => simp [LTerm.degreeAt,LTerm.subterm,LTerm.degree] at degree
      | lam body =>
        simp only [LTerm.degreeAt,LTerm.subterm,Option.bind_some,LTerm.degree,Option.some.injEq] at degree
        cases degree
        obtain ⟨r,member⟩ := List.exists_mem_of_ne_nil _ (old _ _ rfl atomic)
        exact ⟨r,by simp [Marked.tracePositions,member]⟩
    | red body arg old =>
      obtain ⟨r,member⟩ := List.exists_mem_of_ne_nil _ old
      exact ⟨r,by simp [Marked.tracePositions,member]⟩
  | cons s p ih =>
    cases aligned with
    | var => cases s <;> simp [LTerm.degreeAt,LTerm.subterm] at degree
    | lam body =>
      cases s with
      | fn => simp [LTerm.degreeAt,LTerm.subterm] at degree
      | arg => simp [LTerm.degreeAt,LTerm.subterm] at degree
      | body =>
        obtain ⟨r,member⟩ := ih body degree
        exact ⟨r,List.mem_map_of_mem member⟩
    | app fn arg old =>
      cases s with
      | body => simp [LTerm.degreeAt,LTerm.subterm] at degree
      | fn =>
        obtain ⟨r,member⟩ := ih fn degree
        exact ⟨r,List.mem_append_right _ (List.mem_append_left _ (List.mem_map_of_mem member))⟩
      | arg =>
        obtain ⟨r,member⟩ := ih arg degree
        exact ⟨r,List.mem_append_right _ (List.mem_append_right _ (List.mem_map_of_mem member))⟩
    | red body arg old =>
      cases s with
      | body => simp [LTerm.degreeAt,LTerm.subterm] at degree
      | fn =>
        cases p with
        | nil => simp [LTerm.degreeAt,LTerm.subterm,LTerm.degree] at degree
        | cons s p =>
          cases s with
          | fn => simp [LTerm.degreeAt,LTerm.subterm] at degree
          | arg => simp [LTerm.degreeAt,LTerm.subterm] at degree
          | body =>
            obtain ⟨r,member⟩ := ih (.lam (l := Label.atom 0) body) degree
            simp only [Marked.tracePositions,List.mem_map] at member
            obtain ⟨q,member,eq⟩ := member
            have same : q=p := (List.cons.inj eq).2
            cases same
            exact ⟨r,List.mem_append_right _ (List.mem_append_left _ (List.mem_map_of_mem member))⟩
      | arg =>
        obtain ⟨r,member⟩ := ih arg degree
        exact ⟨r,List.mem_append_right _ (List.mem_append_right _ (List.mem_map_of_mem member))⟩

/-- An atomic degree can only belong to a genuine residual of an initial
redex. This holds for arbitrary source labels; INIT is not used. -/
theorem History.atomic_degree_residual (history : History ps t u)
    (s : RedexOcc u.erase) (l : Label) (degree : u.degreeAt s.val=some l)
    (atomic : IsAtomic l) :
    ∃ r : RedexOcc t.erase,
      (⟨ps,history.betaHistory⟩ : Derivation t.erase u.erase).Residual r s := by
  let derivation : Derivation t.erase u.erase := ⟨ps,history.betaHistory⟩
  obtain ⟨target,tracked,erased⟩ := derivation.tracked
  have aligned := (AtomicOrigins.initial t).history tracked history
  obtain ⟨r,trace⟩ := aligned.atomic_trace degree atomic
  have valid : ∃ z,subtermAt t.erase r=some z ∧ IsRedex z := by
    by_cases found : r∈redexPositions t.erase
    · exact (mem_redexPositions t.erase r).mp found
    · have empty : Marked.tracePositions r (Marked.mark [] t.erase)=[] := by
        apply List.eq_nil_iff_forall_not_mem.mpr
        intro p member
        obtain ⟨same,redex⟩ := (Marked.trace_mark [] t.erase r p).mp member
        exact found (same ▸ redex)
      have finalEmpty := tracked.trace_empty empty
      exact False.elim (List.not_mem_nil (finalEmpty ▸ trace))
  exact ⟨⟨r,valid⟩,target,tracked,erased,trace⟩
end Lamping.Lambda.Labelled

