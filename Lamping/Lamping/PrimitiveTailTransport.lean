import Lamping.Lamping.InitialOffsets
import Lamping.Lamping.LocalTransport
namespace Lamping.AG
open Graph
namespace Context

theorem tail_replace_offset (a b : Context) (n k : Nat) :
    (a.replace (n+k) b).tail n=(a.tail n).replace k b := by
  ext t
  by_cases low : t<k
  · simp [tail,replace,low]
  · simp [tail,replace,low,show n+t-(n+k)=t-k by omega]

theorem replace_same_shell {a b : Context} {n : Nat} (same : SameShell n a b) (c : Context) :
    a.replace n c=b.replace n c := by
  ext k
  by_cases low : k<n
  · simpa only [replace_low _ _ low] using same k low
  · simp only [replace_high _ _ (by omega : n≤k)]
end Context

/-- Cutting actual low levels preserves each primitive passage at the exact
decreased index; the supplied source and target tails are retained. -/
theorem Passage.cut_prefix {n k kind p q a b}
    (rule : Passage (n+k) kind p q a b) :
    Passage k kind p q (a.tail n) (b.tail n) := by
  cases rule with
  | fanO shell tail x =>
    simpa only [Context.tail_replace_offset] using Passage.fanO (i:=k) (shell.tail n) tail x
  | fanStar shell tail x =>
    simpa only [Context.tail_replace_offset] using Passage.fanStar (i:=k) (shell.tail n) tail x
  | cro shell tail =>
    simpa only [Context.tail_replace_offset] using Passage.cro (i:=k) (shell.tail n) tail
  | bra shell tail x y =>
    simpa only [Context.tail_replace_offset] using Passage.bra (i:=k) (shell.tail n) tail x y
  | appFun a => exact .appFun _
  | appArg a => exact .appArg _
  | lamBody a => exact .lamBody _

theorem Traversal.cut_prefix {index kind p q a b} (rule : Traversal index kind p q a b)
    (n : Nat) (bounded : n≤index) :
    Traversal (index-n) kind p q (a.tail n) (b.tail n) := by
  have indexEq : index=n+(index-n) := by omega
  rw [indexEq] at rule
  cases rule with
  | direct passage => exact .direct passage.cut_prefix
  | inverse passage => exact .inverse passage.cut_prefix

/-- Changing one genuinely lower level in both contexts leaves a high
primitive traversal valid, with all other supplied levels fixed. -/
theorem Traversal.set_level_below {index kind p q a b} (rule : Traversal index kind p q a b)
    (n : Nat) (bounded : n<index) (x : Level) :
    Traversal index kind p q
      (a.replace n ((a.tail (n+1)).cons x)) (b.replace n ((b.tail (n+1)).cons x)) := by
  have lifted := (rule.cut_prefix (n+1) (by omega)).lift (a.replace n (Context.empty.cons x)) (n+1)
  have indexEq : n+1+(index-(n+1))=index := by omega
  rw [indexEq,←Context.replace_cons,←Context.replace_cons] at lifted
  have low : Context.SameShell n a b := fun k hk => rule.low k (by omega)
  rw [Context.replace_same_shell low ((b.tail (n+1)).cons x)] at lifted
  exact lifted

theorem Traversal.fan_below {index kind p q a b} (rule : Traversal index kind p q a b)
    (n : Nat) (bounded : n<index) (branch : Bool) :
    Traversal index kind p q (InitialOffsets.fanAt n branch a) (InitialOffsets.fanAt n branch b) := by
  have same : a.get n=b.get n := rule.low n bounded
  simpa only [InitialOffsets.fanAt,same] using
    rule.set_level_below n bounded (InitialOffsets.mark branch (a.get n))

/-- Inserting a low empty level raises the actual passive traversal index. -/
theorem Traversal.cro_below {index kind p q a b} (rule : Traversal index kind p q a b)
    (n : Nat) (bounded : n≤index) :
    Traversal (index+1) kind p q (InitialOffsets.croAt n a) (InitialOffsets.croAt n b) := by
  have lifted := ((rule.cut_prefix n bounded).cons .empty).lift a n
  have indexEq : n+(1+(index-n))=index+1 := by omega
  rw [indexEq] at lifted
  have low : Context.SameShell n a b := fun k hk => rule.low k (by omega)
  change Traversal (index+1) kind p q (a.replace n ((a.tail n).cons .empty))
    (a.replace n ((b.tail n).cons .empty)) at lifted
  rw [Context.replace_same_shell low ((b.tail n).cons .empty)] at lifted
  exact lifted

/-- Packing two low levels lowers the actual high traversal index by one. -/
theorem Traversal.bra_below {index kind p q a b} (rule : Traversal index kind p q a b)
    (n : Nat) (bounded : n+1<index) :
    Traversal (index-1) kind p q (InitialOffsets.braAt n a) (InitialOffsets.braAt n b) := by
  have lifted := ((rule.cut_prefix (n+2) (by omega)).cons (.pair (a.get (n+1)) (a.get n))).lift a n
  have indexEq : n+(1+(index-(n+2)))=index-1 := by omega
  rw [indexEq] at lifted
  have low : Context.SameShell n a b := fun k hk => rule.low k (by omega)
  have first : a.get n=b.get n := rule.low n (by omega)
  have second : a.get (n+1)=b.get (n+1) := rule.low (n+1) bounded
  change Traversal (index-1) kind p q
    (a.replace n ((a.tail (n+2)).cons (.pair (a.get (n+1)) (a.get n))))
    (a.replace n ((b.tail (n+2)).cons (.pair (a.get (n+1)) (a.get n)))) at lifted
  rw [Context.replace_same_shell low ((b.tail (n+2)).cons (.pair (a.get (n+1)) (a.get n)))] at lifted
  simpa only [InitialOffsets.braAt,first,second] using lifted
end Lamping.AG

