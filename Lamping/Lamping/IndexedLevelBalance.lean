import Lamping.Lamping.EncodedBalance
namespace Lamping.AG
open Graph Lambda

/-- Controls act strictly below their principal-side tail, except Cro whose
auxiliary base is one lower. Proper nodes and garbage impose no extra bound. -/
def ControlIndexBound (actual : Label signature) (base : Int) : Prop :=
  match actual.sort with
  | .op .fan => (actual.index : Int) < base
  | .op .cro => (actual.index : Int) ≤ base
  | .op .bra => (actual.index : Int) < base
  | _ => True

section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable (g : Net signature N B W) (boundary : B → Int)

/-- A structural strengthening of integer balance, without path semantics. -/
structure IndexedLevelBalance extends LevelBalance g boundary where
  bounded : ∀ node, ControlIndexBound (g.label node) (nodes node)
end

section
variable {N M B C W V : Type} [FiniteNames N] [FiniteNames M]
  [FiniteNames B] [FiniteNames C] [FiniteNames W] [FiniteNames V]
variable (g : Net signature N B W) (h : Net signature M C V)
variable (bp : B → Int) (cp : C → Int)

def IndexedLevelBalance.union (left : IndexedLevelBalance g bp)
    (right : IndexedLevelBalance h cp) :
    IndexedLevelBalance (unionNet g h) (Sum.elim bp cp) where
  toLevelBalance := LevelBalance.union g h bp cp left.toLevelBalance right.toLevelBalance
  bounded := by rintro (n | m); exact left.bounded n; exact right.bounded m
end

section
variable {K R B F W V : Type} [FiniteNames K] [FiniteNames R]
  [FiniteNames B] [FiniteNames F] [FiniteNames W] [FiniteNames V]
variable (c : Net signature K (B⊕F) W) (r : Net signature R F V)
variable (bp : B → Int) (fp : F → Int)

def IndexedLevelBalance.plug (left : IndexedLevelBalance c (Sum.elim bp fp))
    (right : IndexedLevelBalance r fp) : IndexedLevelBalance (Graph.plug c r) bp where
  toLevelBalance := LevelBalance.plug c r bp fp left.toLevelBalance right.toLevelBalance
  bounded := by rintro (n | m); exact left.bounded n; exact right.bounded m
end

def varNet_indexed_balance (n k : Nat) :
    IndexedLevelBalance (varNet n k) (boundaryDepthAt n) where
  toLevelBalance := varNet_balance n k
  bounded := by intro node; exact Int.le_refl _

def lambdaUsed_indexed_balance (n : Nat) (body : Term) (used : free body 0) :
    IndexedLevelBalance (lambdaUsed n body used)
      (Sum.elim (boundaryDepthAt n) (boundaryDepthAt n)) where
  toLevelBalance := lambdaUsed_balance n body used
  bounded := by intro node; trivial

def lambdaUnused_indexed_balance (n : Nat) (body : Term) (unused : ¬free body 0) :
    IndexedLevelBalance (lambdaUnused n body unused)
      (Sum.elim (boundaryDepthAt n) (boundaryDepthAt n)) where
  toLevelBalance := lambdaUnused_balance n body unused
  bounded := by rintro (node | node) <;> trivial

def appPatch_indexed_balance (n : Nat) (f arg : Term) :
    IndexedLevelBalance (appPatch n f arg) (Sum.elim (boundaryDepthAt n)
      (Sum.elim (boundaryDepthAt n) (boundaryDepthAt (n+1)))) where
  toLevelBalance := appPatch_balance n f arg
  bounded := by
    rintro (node | (node | node))
    · trivial
    · change (n : Int) < (n : Int)+1; omega
    · change (n : Int) < (n : Int)+1; omega

/-- All actual encoding patches supply the strict Fan/Bra and weak Cro bounds. -/
theorem encode_indexed_balance (t : Term) (n : Nat) :
    Nonempty (IndexedLevelBalance (encode n t).net (boundaryDepthAt n)) := by
  induction t generalizing n with
  | var k => exact ⟨varNet_indexed_balance n k⟩
  | lam body ih =>
    obtain ⟨child⟩ := ih n
    dsimp only [encode]
    by_cases used : free body 0
    · rw [dif_pos used]
      exact ⟨IndexedLevelBalance.plug _ _ _ _ (lambdaUsed_indexed_balance n body used) child⟩
    · rw [dif_neg used]
      exact ⟨IndexedLevelBalance.plug _ _ _ _ (lambdaUnused_indexed_balance n body used) child⟩
  | app f arg hf ha =>
    obtain ⟨left⟩ := hf n
    obtain ⟨right⟩ := ha (n+1)
    exact ⟨IndexedLevelBalance.plug _ _ _ _ (appPatch_indexed_balance n f arg)
      (IndexedLevelBalance.union _ _ _ _ left right)⟩
end Lamping.AG
