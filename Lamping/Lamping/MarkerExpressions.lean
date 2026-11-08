import Lamping.Lamping.Context
namespace Lamping.AG.Marker

/-- Finite constructor expressions in whole input levels. Variables name
input-level positions; they are not graph nodes or binder occurrences. -/
inductive LevelExpr where
  | empty | o (a : LevelExpr) | star (a : LevelExpr) | pair (a b : LevelExpr) | var (index : Nat)
  deriving DecidableEq, Repr

namespace LevelExpr
def eval (valuation : Nat → Level) : LevelExpr → Level
  | .empty => .empty
  | .o a => .o (eval valuation a)
  | .star a => .star (eval valuation a)
  | .pair a b => .pair (eval valuation a) (eval valuation b)
  | .var k => valuation k

def height : LevelExpr → Nat
  | .empty | .var _ => 0
  | .o a | .star a => height a+1
  | .pair a b => max (height a) (height b)+1

def leadingO : LevelExpr → Nat
  | .o a => leadingO a+1
  | _ => 0

/-- Zero distinguishes a constructor head from a variable head; i+1 retains
the actual variable name after stripping only the leading O constructors. -/
def headVariable : LevelExpr → Nat
  | .o a => headVariable a
  | .var i => i+1
  | _ => 0

theorem leadingO_le_height (a : LevelExpr) : a.leadingO ≤ a.height := by
  induction a <;> simp_all [leadingO,height]

def code : Nat → Level
  | 0 => .star .empty
  | n+1 => .o (code n)

def oDepth : Level → Nat
  | .o a => oDepth a+1
  | _ => 0

theorem oDepth_code (n : Nat) : oDepth (code n)=n := by
  induction n with
  | zero => rfl
  | succ n ih => simpa only [code,oDepth] using congrArg Nat.succ ih

/-- A gap larger than the expression height distinguishes old variable codes
from any bounded number of freshly written leading O constructors. -/
def valuation (gap : Nat) (index : Nat) : Level := code (gap*(index+1))

theorem eval_oDepth (gap : Nat) (a : LevelExpr) :
    oDepth (a.eval (valuation gap)) = a.leadingO+gap*a.headVariable := by
  induction a with
  | empty => rfl
  | o a ih => simp only [eval,oDepth,leadingO,headVariable,ih]; omega
  | star a ih => rfl
  | pair a b ia ib => rfl
  | var k => simpa only [eval,valuation,leadingO,headVariable,Nat.zero_add] using oDepth_code (gap*(k+1))

theorem eval_leading_equal {gap : Nat} {a b : LevelExpr}
    (ha : a.height<gap) (hb : b.height<gap)
    (equal : a.eval (valuation gap)=b.eval (valuation gap)) :
    a.leadingO=b.leadingO ∧ a.headVariable=b.headVariable := by
  have lowA : a.leadingO<gap := Nat.lt_of_le_of_lt a.leadingO_le_height ha
  have lowB : b.leadingO<gap := Nat.lt_of_le_of_lt b.leadingO_le_height hb
  have depths := congrArg oDepth equal
  rw [eval_oDepth,eval_oDepth] at depths
  have residues := congrArg (fun n => n%gap) depths
  simp only [Nat.add_mod,Nat.mul_mod,Nat.mod_self,Nat.zero_mul,Nat.zero_mod,Nat.add_zero,
    Nat.mod_eq_of_lt lowA,Nat.mod_eq_of_lt lowB] at residues
  refine ⟨residues,?_⟩
  rw [residues] at depths
  exact Nat.mul_left_cancel (by omega) (Nat.add_left_cancel depths)

theorem eval_codes_injective {gap : Nat} {a b : LevelExpr}
    (ha : a.height<gap) (hb : b.height<gap)
    (equal : a.eval (valuation gap)=b.eval (valuation gap)) : a=b := by
  induction a generalizing b with
  | empty =>
    cases b with
    | empty => rfl
    | o b => cases equal
    | star b => cases equal
    | pair b c => cases equal
    | var k => have impossible := (eval_leading_equal ha hb equal).2; simp [headVariable] at impossible
  | o a ih =>
    cases b with
    | empty => cases equal
    | star b => cases equal
    | pair b c => cases equal
    | var k => have impossible := (eval_leading_equal ha hb equal).1; simp [leadingO] at impossible
    | o b =>
      apply congrArg LevelExpr.o
      exact ih (by change a.height+1<gap at ha; omega) (by change b.height+1<gap at hb; omega) (Level.o.inj equal)
  | star a ih =>
    cases b with
    | empty => cases equal
    | o b => cases equal
    | pair b c => cases equal
    | var k => have impossible := (eval_leading_equal ha hb equal).2; simp [headVariable] at impossible
    | star b =>
      apply congrArg LevelExpr.star
      exact ih (by change a.height+1<gap at ha; omega) (by change b.height+1<gap at hb; omega) (Level.star.inj equal)
  | pair a c ia ic =>
    cases b with
    | empty => cases equal
    | o b => cases equal
    | star b => cases equal
    | var k => have impossible := (eval_leading_equal ha hb equal).2; simp [headVariable] at impossible
    | pair b d =>
      obtain ⟨left,right⟩ := Level.pair.inj equal
      have habound : a.height<gap := by change max a.height c.height+1<gap at ha; omega
      have hcbound : c.height<gap := by change max a.height c.height+1<gap at ha; omega
      have hbbound : b.height<gap := by change max b.height d.height+1<gap at hb; omega
      have hdbound : d.height<gap := by change max b.height d.height+1<gap at hb; omega
      rw [ia habound hbbound left,ic hcbound hdbound right]
  | var k =>
    cases b with
    | var j =>
      have names := (eval_leading_equal ha hb equal).2
      simp only [headVariable,Nat.add_left_inj] at names
      rw [names]
    | o b => have impossible := (eval_leading_equal ha hb equal).1; simp [leadingO] at impossible
    | empty => have impossible := (eval_leading_equal ha hb equal).2; simp [headVariable] at impossible
    | star b => have impossible := (eval_leading_equal ha hb equal).2; simp [headVariable] at impossible
    | pair b c => have impossible := (eval_leading_equal ha hb equal).2; simp [headVariable] at impossible

def supportBound : LevelExpr → Nat
  | .empty => 0
  | .o a | .star a => a.supportBound
  | .pair a b => max a.supportBound b.supportBound
  | .var k => k+1

theorem eval_agree {left right : Nat → Level} (a : LevelExpr)
    (agree : ∀ k, k<a.supportBound → left k=right k) : a.eval left=a.eval right := by
  induction a with
  | empty => rfl
  | o a ih => exact congrArg Level.o (ih agree)
  | star a ih => exact congrArg Level.star (ih agree)
  | pair a b ia ib =>
    have first := ia (by intro k hk; exact agree k (Nat.lt_of_lt_of_le hk (Nat.le_max_left _ _)))
    have second := ib (by intro k hk; exact agree k (Nat.lt_of_lt_of_le hk (Nat.le_max_right _ _)))
    change Level.pair (a.eval left) (b.eval left)=Level.pair (a.eval right) (b.eval right)
    rw [first,second]
  | var k => exact agree k (by change k<k+1; omega)

/-- A genuine finitely supported root context. The infinite coding valuation
above is used only as a finite-expression calculation, never as graph input. -/
def codeContext (gap bound : Nat) : Context :=
  ⟨fun k => if k<bound then valuation gap k else .empty,
    ⟨bound,by intro k hk; simp only [if_neg (by omega : ¬k<bound)]⟩⟩

theorem eval_codeContext (gap bound : Nat) (a : LevelExpr) (support : a.supportBound≤bound) :
    a.eval (codeContext gap bound).get=a.eval (valuation gap) := by
  apply a.eval_agree
  intro k hk
  exact if_pos (Nat.lt_of_lt_of_le hk support)

theorem finite_codes_injective {gap bound : Nat} {a b : LevelExpr}
    (ha : a.height<gap) (hb : b.height<gap) (sa : a.supportBound≤bound) (sb : b.supportBound≤bound)
    (equal : a.eval (codeContext gap bound).get=b.eval (codeContext gap bound).get) : a=b := by
  rw [eval_codeContext gap bound a sa,eval_codeContext gap bound b sb] at equal
  exact eval_codes_injective ha hb equal

/-- Finite constructor equations that cover every REAL context contain a
uniform identity. No choice of a binder occurrence is assumed: a single
finite separating input supplies the actual candidate. -/
theorem uniform_candidate (candidates : List (LevelExpr×LevelExpr)) (gap bound : Nat)
    (bounds : ∀ p∈candidates, p.1.height<gap ∧ p.2.height<gap ∧
      p.1.supportBound≤bound ∧ p.2.supportBound≤bound)
    (covers : ∀ input : Context, ∃ p∈candidates, p.1.eval input.get=p.2.eval input.get) :
    ∃ p∈candidates, p.1=p.2 := by
  obtain ⟨p,member,equal⟩ := covers (codeContext gap bound)
  obtain ⟨ha,hb,sa,sb⟩ := bounds p member
  exact ⟨p,member,finite_codes_injective ha hb sa sb equal⟩

theorem uniform_system_candidate (candidates : List (List (LevelExpr×LevelExpr))) (gap bound : Nat)
    (bounds : ∀ system∈candidates, ∀ p∈system, p.1.height<gap ∧ p.2.height<gap ∧
      p.1.supportBound≤bound ∧ p.2.supportBound≤bound)
    (covers : ∀ input : Context, ∃ system∈candidates,
      ∀ p∈system, p.1.eval input.get=p.2.eval input.get) :
    ∃ system∈candidates, ∀ p∈system, p.1=p.2 := by
  obtain ⟨system,member,equations⟩ := covers (codeContext gap bound)
  refine ⟨system,member,?_⟩
  intro p inSystem
  obtain ⟨ha,hb,sa,sb⟩ := bounds system member p inSystem
  exact finite_codes_injective ha hb sa sb (equations p inSystem)

theorem finite_pair_bounds (pairs : List (LevelExpr×LevelExpr)) :
    ∃ gap bound, ∀ p∈pairs, p.1.height<gap ∧ p.2.height<gap ∧
      p.1.supportBound≤bound ∧ p.2.supportBound≤bound := by
  induction pairs with
  | nil => exact ⟨1,0,by simp⟩
  | cons p pairs ih =>
    obtain ⟨gap,bound,bounds⟩ := ih
    refine ⟨max gap (max p.1.height p.2.height+1), max bound (max p.1.supportBound p.2.supportBound),?_⟩
    intro q member
    rcases List.mem_cons.mp member with same | member
    · subst q
      omega
    · obtain ⟨ha,hb,sa,sb⟩ := bounds q member
      omega

/-- The separation bounds are constructed from the finite candidate list,
so callers need no unproved fresh-marker or height certificate. -/
theorem uniform_system_candidate_finite (candidates : List (List (LevelExpr×LevelExpr)))
    (covers : ∀ input : Context, ∃ system∈candidates,
      ∀ p∈system, p.1.eval input.get=p.2.eval input.get) :
    ∃ system∈candidates, ∀ p∈system, p.1=p.2 := by
  obtain ⟨gap,bound,bounds⟩ := finite_pair_bounds candidates.flatten
  apply uniform_system_candidate candidates gap bound _ covers
  intro system member p inSystem
  exact bounds p (List.mem_flatten.mpr ⟨system,member,inSystem⟩)
end LevelExpr
end Lamping.AG.Marker
