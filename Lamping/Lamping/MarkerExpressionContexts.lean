import Lamping.Lamping.MarkerExpressions
namespace Lamping.AG.Marker

/-- A finite expression prefix followed by a shifted input tail. The eventual
variable equation is a representation invariant, not a path-labelling oracle. -/
structure ExprContext where
  get : Nat → LevelExpr
  cutoff : Nat
  offset : Nat
  tail : ∀ k, cutoff≤k → get k=.var (offset+(k-cutoff))

namespace ExprContext
def initial : ExprContext where
  get := .var
  cutoff := 0
  offset := 0
  tail k _ := by simp

def eval (a : ExprContext) (input : Context) : Context where
  get k := (a.get k).eval input.get
  finite := by
    obtain ⟨n,finite⟩ := input.finite
    refine ⟨a.cutoff+n,?_⟩
    intro k hk
    rw [a.tail k (by omega)]
    exact finite _ (by omega)

@[simp] theorem eval_get (a : ExprContext) (input : Context) (k : Nat) :
    (a.eval input).get k=(a.get k).eval input.get := rfl

@[simp] theorem eval_initial (input : Context) : initial.eval input=input := by ext k; rfl

def cons (a : ExprContext) (head : LevelExpr) : ExprContext where
  get k := match k with | 0 => head | k+1 => a.get k
  cutoff := a.cutoff+1
  offset := a.offset
  tail k hk := by
    cases k with
    | zero => omega
    | succ k =>
      change a.get k=.var (a.offset+(k+1-(a.cutoff+1)))
      rw [a.tail k (by omega)]
      congr 1
      omega

def drop (a : ExprContext) (n : Nat) : ExprContext where
  get k := a.get (n+k)
  cutoff := a.cutoff
  offset := a.offset+n
  tail k hk := by
    rw [a.tail (n+k) (by omega)]
    congr 1
    omega

def replace (a : ExprContext) (n : Nat) (b : ExprContext) : ExprContext where
  get k := if k<n then a.get k else b.get (k-n)
  cutoff := n+b.cutoff
  offset := b.offset
  tail k hk := by
    simp only [if_neg (by omega : ¬k<n)]
    rw [b.tail (k-n) (by omega)]
    congr 1
    omega

@[simp] theorem eval_cons (a : ExprContext) (head : LevelExpr) (input : Context) :
    (a.cons head).eval input=(a.eval input).cons (head.eval input.get) := by
  ext k
  cases k <;> rfl

@[simp] theorem eval_drop (a : ExprContext) (n : Nat) (input : Context) :
    (a.drop n).eval input=(a.eval input).tail n := by ext k; rfl

@[simp] theorem eval_replace (a b : ExprContext) (n : Nat) (input : Context) :
    (a.replace n b).eval input=(a.eval input).replace n (b.eval input) := by
  ext k
  change (if k<n then a.get k else b.get (k-n)).eval input.get =
    if k<n then (a.get k).eval input.get else (b.get (k-n)).eval input.get
  split <;> rfl

/-- Finite named equations for exactly the lower n levels. -/
def shellEquations (a b : ExprContext) (n : Nat) : List (LevelExpr×LevelExpr) :=
  (List.range n).map (fun k => (a.get k,b.get k))

theorem shellEquations_eval (a b : ExprContext) (n : Nat) (input : Context) :
    (∀ pair∈a.shellEquations b n, pair.1.eval input.get=pair.2.eval input.get) ↔
      Context.SameShell n (a.eval input) (b.eval input) := by
  constructor
  · intro equations k low
    exact equations (a.get k,b.get k) (List.mem_map.mpr ⟨k,List.mem_range.mpr low,rfl⟩)
  · intro shell pair member
    obtain ⟨k,inRange,equal⟩ := List.mem_map.mp member
    cases equal
    exact shell k (List.mem_range.mp inRange)

theorem shellEquations_identity (a b : ExprContext) (n : Nat)
    (identities : ∀ pair∈a.shellEquations b n, pair.1=pair.2) (input : Context) :
    Context.SameShell n (a.eval input) (b.eval input) := by
  apply (a.shellEquations_eval b n input).mp
  intro pair member
  rw [identities pair member]
end ExprContext
end Lamping.AG.Marker
