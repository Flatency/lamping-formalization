import Lamping.Lambda.BetaPaths
namespace Lamping.Lambda.Labelled

/- Canonical nonempty words: concatenation is associative by theorem, without
quotienting arbitrary binary concatenation trees. No empty source label exists. -/
mutual
  inductive Label where
    | single : Letter → Label
    | cons : Letter → Label → Label
    deriving DecidableEq, Repr
  inductive Letter where
    | atom : Nat → Letter
    | over : Label → Letter
    | under : Label → Letter
    deriving DecidableEq, Repr
end

def Label.atom (n : Nat) : Label := .single (.atom n)
def Label.over (a : Label) : Label := .single (.over a)
def Label.under (a : Label) : Label := .single (.under a)
def Label.concat : Label → Label → Label
  | .single l, b => .cons l b
  | .cons l a, b => .cons l (concat a b)

theorem Label.concat_assoc : ∀ (a b c : Label), (a.concat b).concat c = a.concat (b.concat c)
  | .single _, _, _ => rfl
  | .cons l a, b, c => congrArg (Label.cons l) (concat_assoc a b c)

/-- Outer word length (one per Letter), used only for atomicity. This is not
the total atomic-occurrence norm used in later labelled-calculus theorems. -/
def Label.length : Label → Nat
  | .single _ => 1
  | .cons _ a => a.length + 1
theorem Label.length_pos : ∀ (a : Label), 0 < a.length
  | .single _ => Nat.zero_lt_succ 0
  | .cons _ _ => Nat.zero_lt_succ _
theorem Label.length_concat : ∀ (a b : Label), (a.concat b).length = a.length + b.length
  | .single _, b => by simp [concat,length,Nat.add_comm]
  | .cons _ a, b => by simp [concat,length,length_concat,Nat.add_assoc,Nat.add_comm]

inductive LTerm where
  | var : Label → Nat → LTerm
  | app : Label → LTerm → LTerm → LTerm
  | lam : Label → LTerm → LTerm
  deriving DecidableEq, Repr

namespace LTerm
def erase : LTerm → Lambda.Term
  | .var _ i => .var i
  | .app _ f a => .app (erase f) (erase a)
  | .lam _ b => .lam (erase b)
def label : LTerm → Label
  | .var l _ | .app l _ _ | .lam l _ => l
def prepend (a : Label) : LTerm → LTerm
  | .var l i => .var (a.concat l) i
  | .app l f b => .app (a.concat l) f b
  | .lam l b => .lam (a.concat l) b
@[simp] theorem erase_prepend (a : Label) (t : LTerm) : (prepend a t).erase = t.erase := by
  cases t <;> rfl
theorem prepend_assoc (a b : Label) (t : LTerm) : prepend a (prepend b t) = prepend (a.concat b) t := by
  cases t <;> simp [prepend,Label.concat_assoc]
def rename (ρ : Nat → Nat) : LTerm → LTerm
  | .var l i => .var l (ρ i)
  | .app l f a => .app l (rename ρ f) (rename ρ a)
  | .lam l b => .lam l (rename (Lambda.liftRen ρ) b)
@[simp] theorem erase_rename (ρ) (t : LTerm) : (rename ρ t).erase = Lambda.rename ρ t.erase := by
  induction t generalizing ρ with
  | var l i => rfl
  | app l f a hf ha => simp [rename,erase,Lambda.rename,hf,ha]
  | lam l b hb => simp [rename,erase,Lambda.rename,hb]

/-- A kept variable preserves its existing label. This avoids inventing an
empty label merely to express the identity substitution. -/
inductive SubValue where
  | keep : Nat → SubValue
  | put : LTerm → SubValue
def SubValue.erase : SubValue → Lambda.Term
  | .keep i => .var i
  | .put t => t.erase
def lift (σ : Nat → SubValue) : Nat → SubValue
  | 0 => .keep 0
  | i+1 => match σ i with
    | .keep j => .keep (j+1)
    | .put t => .put (rename Nat.succ t)
def subst (σ : Nat → SubValue) : LTerm → LTerm
  | .var l i => match σ i with
    | .keep j => .var l j
    | .put t => prepend l t
  | .app l f a => .app l (subst σ f) (subst σ a)
  | .lam l b => .lam l (subst (lift σ) b)
theorem erase_lift (σ : Nat → SubValue) (i : Nat) :
    (lift σ i).erase = Lambda.liftSub (fun i => (σ i).erase) i := by
  cases i with
  | zero => rfl
  | succ i => cases h : σ i <;> simp [lift,h,SubValue.erase,Lambda.liftSub,Lambda.rename]
theorem erase_subst (σ : Nat → SubValue) (t : LTerm) :
    (subst σ t).erase = Lambda.subst (fun i => (σ i).erase) t.erase := by
  induction t generalizing σ with
  | var l i => cases h : σ i <;> simp [subst,h,SubValue.erase,erase,Lambda.subst]
  | app l f a hf ha => simp [subst,erase,Lambda.subst,hf,ha]
  | lam l b hb =>
    simp only [subst,erase,Lambda.subst,hb]
    congr 1; congr 1; funext i; exact erase_lift σ i
def single (a : LTerm) : Nat → SubValue
  | 0 => .put a
  | i+1 => .keep i
def contract (beta alpha : Label) (b a : LTerm) : LTerm :=
  prepend (beta.concat alpha.over) (subst (single (prepend alpha.under a)) b)
theorem erase_contract (beta alpha : Label) (b a : LTerm) :
    (contract beta alpha b a).erase = Lambda.contract b.erase a.erase := by
  simp only [contract,erase_prepend,erase_subst,Lambda.contract]
  congr 1; funext i; cases i <;> simp [single,SubValue.erase,Lambda.singleSub]

/-- Degree is the function-lambda label, never the surrounding app label. -/
def degree : LTerm → Option Label
  | .app _ (.lam alpha _) _ => some alpha
  | _ => none
end LTerm

inductive LBETA : LTerm → LTerm → Prop where
  | root (beta alpha : Label) (b a : LTerm) :
      LBETA (.app beta (.lam alpha b) a) (LTerm.contract beta alpha b a)
  | fn : LBETA f f' → LBETA (.app beta f a) (.app beta f' a)
  | arg : LBETA a a' → LBETA (.app beta f a) (.app beta f a')
  | body : LBETA b b' → LBETA (.lam alpha b) (.lam alpha b')
theorem LBETA.erase (h : LBETA t u) : Lambda.Beta t.erase u.erase := by
  induction h with
  | root beta alpha b a => simpa only [LTerm.erase_contract] using Lambda.Beta.root b.erase a.erase
  | fn h ih => exact .fn ih
  | arg h ih => exact .arg ih
  | body h ih => exact .body ih

def LTerm.labels : LTerm → List Label
  | .var l _ => [l]
  | .app l f a => l :: (f.labels ++ a.labels)
  | .lam l b => l :: b.labels
def IsAtomic (l : Label) : Prop := ∃ n, l = Label.atom n
def INIT (t : LTerm) : Prop := (∀ l ∈ t.labels, IsAtomic l) ∧ t.labels.Nodup

def nodeCount : Lambda.Term → Nat
  | .var _ => 1
  | .lam b => nodeCount b + 1
  | .app f a => nodeCount f + nodeCount a + 1

/-- Preorder atomic labels in a fresh interval, assigned once at the initial term. -/
def initFrom (k : Nat) : Lambda.Term → LTerm
  | .var i => .var (Label.atom k) i
  | .lam b => .lam (Label.atom k) (initFrom (k+1) b)
  | .app f a => .app (Label.atom k) (initFrom (k+1) f) (initFrom (k+1+nodeCount f) a)
def initLabels (t : Lambda.Term) : LTerm := initFrom 0 t

theorem erase_initFrom (t : Lambda.Term) (k : Nat) : (initFrom k t).erase = t := by
  induction t generalizing k with
  | var i => rfl
  | lam b hb => simp [initFrom,LTerm.erase,hb]
  | app f a hf ha => simp [initFrom,LTerm.erase,hf,ha]

theorem labels_initFrom (t : Lambda.Term) (k : Nat) :
    (initFrom k t).labels = (List.range' k (nodeCount t)).map Label.atom := by
  induction t generalizing k with
  | var i => rfl
  | lam b hb => simp [initFrom,LTerm.labels,nodeCount,List.range'_succ,hb]
  | app f a hf ha =>
    simp only [initFrom,LTerm.labels,hf,ha,nodeCount,List.range'_succ,List.map_cons]
    congr 1
    rw [← List.map_append]
    congr 1
    simpa only [Nat.one_mul] using
      (List.range'_append (s := k+1) (m := nodeCount f) (n := nodeCount a) (step := 1))

theorem initFrom_is_INIT (t : Lambda.Term) (k : Nat) : INIT (initFrom k t) := by
  constructor
  · intro l hl
    rw [labels_initFrom] at hl
    obtain ⟨a,_,rfl⟩ := List.mem_map.mp hl
    exact ⟨a,rfl⟩
  · rw [labels_initFrom]
    exact List.Pairwise.map Label.atom (R := fun a b : Nat => a ≠ b)
      (fun a b hab he => by
        simp only [Label.atom,Label.single.injEq,Letter.atom.injEq] at he
        exact hab he)
      List.nodup_range'

theorem init_is_INIT (t : Lambda.Term) : INIT (initLabels t) := initFrom_is_INIT t 0
theorem erase_initLabels (t : Lambda.Term) : (initLabels t).erase = t := erase_initFrom t 0

theorem label_mem_labels (t : LTerm) : t.label ∈ t.labels := by
  cases t <;> exact List.mem_cons_self
theorem label_prepend (a : Label) (t : LTerm) : (t.prepend a).label = a.concat t.label := by
  cases t <;> rfl

/-- INIT is an initial condition: even one root beta creates a compound root label. -/
theorem root_contract_not_INIT (beta alpha : Label) (b a : LTerm) :
    ¬ INIT (LTerm.contract beta alpha b a) := by
  intro hi
  obtain ⟨k,hk⟩ := hi.1 _ (label_mem_labels _)
  have hn := congrArg Label.length hk
  have hp := Label.length_pos beta
  have hq := Label.length_pos
    (LTerm.subst (LTerm.single (LTerm.prepend alpha.under a)) b).label
  simp only [LTerm.contract,label_prepend,Label.length_concat,Label.over,Label.length,
    Label.atom] at hn
  omega

end Lamping.Lambda.Labelled
