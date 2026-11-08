import Lamping.Lambda.StandardizationWeight
import Lamping.Lambda.StandardizationHistoryPull
namespace Lamping.Lambda
/-- Fixed-dimensional natural costs. Fixing the dimension is essential:
unbounded list lexicographic order alone would not be well founded. -/
def HistoryCost : Nat → Type
  | 0 => Unit
  | n+1 => Nat × HistoryCost n

def HistoryCost.Lt : (n : Nat) → HistoryCost n → HistoryCost n → Prop
  | 0,_,_ => False
  | n+1,a,b => Prod.Lex Nat.lt (HistoryCost.Lt n) a b

theorem HistoryCost.wellFounded (n : Nat) : WellFounded (HistoryCost.Lt n) := by
  induction n with
  | zero => exact ⟨fun x => .intro x (by intro y hy; cases hy)⟩
  | succ n ih =>
    change WellFounded (Prod.Lex Nat.lt (HistoryCost.Lt n))
    exact ⟨fun p => Prod.lexAccessible (Nat.lt_wfRel.wf.apply p.1) ih.apply p.2⟩

def HistoryCost.ofList : (n : Nat) → (xs : List Nat) → xs.length=n → HistoryCost n
  | 0,[],_ => ()
  | 0,_::_,h => False.elim (Nat.noConfusion h)
  | Nat.succ _,[],h => False.elim (Nat.noConfusion h)
  | n+1,a::xs,h => (a,ofList n xs (Nat.succ.inj h))

/-- Ordinary lexicographic decrease; well-foundedness below explicitly fixes
both list lengths, so no unbounded-prefix argument is smuggled in. -/
inductive HistoryCost.ListLt : List Nat → List Nat → Prop where
  | head (xs ys : List Nat) (lt : a<b) : ListLt (a::xs) (b::ys)
  | tail (a : Nat) : ListLt xs ys → ListLt (a::xs) (a::ys)

theorem HistoryCost.ListLt.toCost (h : HistoryCost.ListLt xs ys)
    (n : Nat) (lx : xs.length=n) (ly : ys.length=n) :
    HistoryCost.Lt n (HistoryCost.ofList n xs lx) (HistoryCost.ofList n ys ly) := by
  induction h generalizing n with
  | head xs ys lt =>
    cases n with
    | zero => cases lx
    | succ n => exact .left _ _ lt
  | tail a h ih =>
    cases n with
    | zero => cases lx
    | succ n => exact .right a (ih n (Nat.succ.inj lx) (Nat.succ.inj ly))

theorem HistoryCost.ListLt.prefix (h : HistoryCost.ListLt xs ys) (common : List Nat) :
    HistoryCost.ListLt (common++xs) (common++ys) := by
  induction common with
  | nil => exact h
  | cons a common ih => exact .tail a ih

namespace ParallelHistory
/-- Later parallel steps are more significant than earlier steps. -/
def costs : ParallelHistory t u → List Nat
  | .nil _ => []
  | @cons t _ _ F h tail => tail.costs ++ [Marked.weight (fun _ => 1) (Marked.mark F t)]
@[simp] theorem costs_length (h : ParallelHistory t u) : h.costs.length=h.length := by
  induction h with
  | nil => rfl
  | cons h tail ih => simp [costs,List.length_append,ih,length]; omega

theorem costs_append (h : ParallelHistory t u) (k : ParallelHistory u v) :
    (h.append k).costs=k.costs++h.costs := by
  induction h with
  | nil => simp [append,costs]
  | cons h tail ih => simp [append,costs,ih,List.append_assoc]
end ParallelHistory
end Lamping.Lambda
