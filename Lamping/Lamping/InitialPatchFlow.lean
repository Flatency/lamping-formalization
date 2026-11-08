import Lamping.Lamping.InitialFlow
namespace Lamping.AG
open Graph Lambda

/-- Variable wires and proper-node wires form separate components inside
each translation patch. A lambda binding port is on the variable side. -/
def variablePort : (k : Kind) → Port k → Bool
  | .op .app,_ => false
  | .op .lam,.inr false => true
  | .op .lam,_ => false
  | .op .fan,_ | .op .cro,_ | .op .bra,_ | .garbage,_ => true

def variableEnd {N B W : Type} {l : N → Label signature}
    (bp : B → Bool) (wp : W → Bool) : End signature N B W l → Bool
  | .inl ⟨n,p⟩ => variablePort (l n).sort p
  | .inr (.inl b) => bp b
  | .inr (.inr (w,_)) => wp w

def VariableSeparated {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
    (g : Net signature N B W) (bp : B → Bool) (wp : W → Bool) : Prop :=
  ∀ e, variableEnd bp wp (g.wire e)=variableEnd bp wp e

theorem Passage.variableSide (h : Passage i k p q a b) : variablePort k p=variablePort k q := by
  cases h <;> rfl

theorem Traversal.variableSide (h : Traversal i k p q a b) : variablePort k p=variablePort k q := by
  cases h with
  | direct h => exact h.variableSide
  | inverse h => exact h.variableSide.symm

section Paths
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable {g : Net signature N B W} {bp : B → Bool} {wp : W → Bool}
theorem LabelledTurn.variableSide (h : LabelledTurn g e f a b) :
    variableEnd bp wp e=variableEnd bp wp f := by
  cases h with
  | node n p q h => exact h.variableSide
  | transparent => rfl

theorem Labelling.variableSide (h : Labelling g es a b) (separated : VariableSeparated g bp wp) :
    ∃ s : Bool, ∀ e ∈ es, variableEnd bp wp e=s := by
  induction h with
  | single e a => exact ⟨variableEnd bp wp e,by simp⟩
  | @cons e f es a b c turn rest ih =>
    obtain ⟨s,hs⟩ := ih
    refine ⟨s,?_⟩
    intro x hx
    rcases List.mem_cons.mp hx with eq | hx
    · subst x
      exact (separated e).symm.trans (turn.variableSide.trans (hs f (by simp)))
    · exact hs x hx

theorem Labelling.no_variable_exit (h : Labelling g es a b)
    (separated : VariableSeparated g bp wp)
    (start : es.head?=some e) (isVariable : variableEnd bp wp e=true)
    (finish : es.getLast?=some (g.wire f)) (proper : variableEnd bp wp f=false) : False := by
  obtain ⟨s,hs⟩ := h.variableSide separated
  have first := hs e (List.mem_of_head? start)
  have last := hs (g.wire f) (List.mem_of_getLast? finish)
  rw [separated f,proper] at last
  rw [isVariable] at first
  exact Bool.noConfusion (first.trans last.symm)

theorem Labelling.no_proper_visit (h : Labelling g es a b)
    (separated : VariableSeparated g bp wp)
    (start : es.head?=some e) (isVariable : variableEnd bp wp e=true)
    (visit : f ∈ es) (proper : variableEnd bp wp f=false) : False := by
  obtain ⟨s,hs⟩ := h.variableSide separated
  have first := hs e (List.mem_of_head? start)
  have last := hs f visit
  rw [isVariable] at first
  rw [proper] at last
  exact Bool.noConfusion (first.trans last.symm)
end Paths

/-- FV boundary ends are variable components; every subterm root is proper. -/
def variableBoundary {t : Term} : Boundary t → Bool
  | .inl _ => false
  | .inr _ => true

theorem lambdaUsed_variableSeparated (n : Nat) (b : Term) (used : free b 0) :
    VariableSeparated (lambdaUsed n b used)
      (Sum.elim variableBoundary variableBoundary) Empty.elim := by
  rintro (⟨u,p⟩ | (((u | x) | (v | ⟨k,h⟩)) | ⟨w,d⟩))
  · cases p with | inl u => rfl | inr p => cases p <;> rfl
  · rfl
  · rfl
  · rfl
  · cases k <;> rfl
  · exact nomatch w

theorem lambdaUnused_variableSeparated (n : Nat) (b : Term) (unused : ¬free b 0) :
    VariableSeparated (lambdaUnused n b unused)
      (Sum.elim variableBoundary variableBoundary) Empty.elim := by
  rintro (⟨u | v,p⟩ | (((u | x) | (v | ⟨k,h⟩)) | ⟨w,d⟩))
  · cases p with | inl u => rfl | inr p => cases p <;> rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · cases k with | zero => exact False.elim (unused h) | succ k => rfl
  · exact nomatch w

theorem appPatch_variableSeparated (n : Nat) (f a : Term) :
    VariableSeparated (appPatch n f a)
      (Sum.elim variableBoundary (Sum.elim variableBoundary variableBoundary)) Empty.elim := by
  rintro (⟨u | (x | x),p⟩ | (((u | x) | ((v | x) | (z | x))) | ⟨w,d⟩))
  · cases p with | inl u => rfl | inr p => cases p <;> rfl
  · cases p with
    | inl u => dsimp only [appPatch,appMate]; split <;> rfl
    | inr u => rfl
  · cases p with | inl u => rfl | inr p => cases p <;> rfl
  · rfl
  · dsimp only [appPatch,appMate]; split <;> (try split) <;> rfl
  · rfl
  · dsimp only [appPatch,appMate]; split <;> rfl
  · rfl
  · rfl
  · exact nomatch w

theorem lambdaUsed_FV_no_child_root (n : Nat) (b : Term) (used : free b 0) (x : FV b)
    (p : LocalPath (lambdaUsed n b used) (.inr (.inr x)) (.inr (.inl ())) A B) : False := by
  exact p.labeling.no_variable_exit (lambdaUsed_variableSeparated n b used) p.start rfl p.finish rfl

theorem lambdaUnused_FV_no_child_root (n : Nat) (b : Term) (unused : ¬free b 0) (x : FV b)
    (p : LocalPath (lambdaUnused n b unused) (.inr (.inr x)) (.inr (.inl ())) A B) : False := by
  exact p.labeling.no_variable_exit (lambdaUnused_variableSeparated n b unused) p.start rfl p.finish rfl

def appChildVariable {f a : Term} : FV f ⊕ FV a → Boundary (.app f a) ⊕ (Boundary f ⊕ Boundary a)
  | .inl x => .inr (.inl (.inr x))
  | .inr x => .inr (.inr (.inr x))

def appChildRoot (f a : Term) : Bool → Boundary (.app f a) ⊕ (Boundary f ⊕ Boundary a)
  | false => .inr (.inl (.inl ()))
  | true => .inr (.inr (.inl ()))

/-- An actual application-patch path leaving either child's FV cannot enter
the root of either child, even after arbitrary revisits to control wires. -/
theorem appPatch_FV_no_child_root (n : Nat) (f a : Term) (x : FV f ⊕ FV a) (side : Bool)
    (p : LocalPath (appPatch n f a) (appChildVariable x) (appChildRoot f a side) A B) : False := by
  apply p.labeling.no_variable_exit (appPatch_variableSeparated n f a) p.start _ p.finish
  · cases side <;> rfl
  · cases x <;> rfl

theorem variableBoundary_complement (x : Boundary t) :
    variableBoundary x = !(initialBoundaryPolarity x) := by cases x <;> rfl

/-- The source-patch premise consumed by the generic no-escape lemmas,
with every boundary polarity case discharged for the actual lambda patch. -/
theorem lambdaUsed_noReturn (n : Nat) (b : Term) (used : free b 0)
    (z z' : Boundary b) (A B : Context)
    (hz : initialBoundaryPolarity z=false) (hz' : initialBoundaryPolarity z'=true)
    (p : LocalPath (lambdaUsed n b used) (.inr z) (.inr z') A B) : False := by
  apply p.labeling.no_variable_exit (lambdaUsed_variableSeparated n b used) p.start _ p.finish
  · change variableBoundary z'=false
    rw [variableBoundary_complement,hz']; rfl
  · change variableBoundary z=true
    rw [variableBoundary_complement,hz]; rfl

theorem lambdaUnused_noReturn (n : Nat) (b : Term) (unused : ¬free b 0)
    (z z' : Boundary b) (A B : Context)
    (hz : initialBoundaryPolarity z=false) (hz' : initialBoundaryPolarity z'=true)
    (p : LocalPath (lambdaUnused n b unused) (.inr z) (.inr z') A B) : False := by
  apply p.labeling.no_variable_exit (lambdaUnused_variableSeparated n b unused) p.start _ p.finish
  · change variableBoundary z'=false
    rw [variableBoundary_complement,hz']; rfl
  · change variableBoundary z=true
    rw [variableBoundary_complement,hz]; rfl

theorem appPatch_noReturn (n : Nat) (f a : Term) (z z' : Boundary f ⊕ Boundary a) (A B : Context)
    (hz : Sum.elim initialBoundaryPolarity initialBoundaryPolarity z=false)
    (hz' : Sum.elim initialBoundaryPolarity initialBoundaryPolarity z'=true)
    (p : LocalPath (appPatch n f a) (.inr z) (.inr z') A B) : False := by
  apply p.labeling.no_variable_exit (appPatch_variableSeparated n f a) p.start _ p.finish
  · change Sum.elim variableBoundary variableBoundary z'=false
    cases z' <;> simpa only [Sum.elim_inl,Sum.elim_inr,variableBoundary_complement,Bool.not_true] using congrArg Bool.not hz'
  · change Sum.elim variableBoundary variableBoundary z=true
    cases z <;> simpa only [Sum.elim_inl,Sum.elim_inr,variableBoundary_complement,Bool.not_false] using congrArg Bool.not hz
end Lamping.AG


