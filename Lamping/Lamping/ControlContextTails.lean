import Lamping.Lamping.InitialOffsets
import Lamping.Lamping.PathLabelDeterminism
namespace Lamping.AG.InitialOffsets

/-- A strictly lower fan changes no level of the high terminal tail. -/
theorem fanAt_high_tail (a : Context) (n width : Nat) (low : n<width) (branch : Bool) :
    (fanAt n branch a).tail width=a.tail width := by
  apply Context.ext
  intro k
  change (a.replace n ((a.tail (n+1)).cons (mark branch (a.get n)))).get (width+k)=a.get (width+k)
  rw [Context.replace_high _ _ (by omega : n≤width+k)]
  have diff : width+k-n=(width+k-(n+1))+1 := by omega
  rw [diff,Context.cons_succ]
  change a.get (n+1+(width+k-(n+1)))=a.get (width+k)
  congr 1
  omega

/-- The old high index is one above the copied index after cro action. -/
theorem croAt_high_tail (a : Context) (n width : Nat) (low : n<width) :
    (croAt n a).tail width=a.tail (width-1) := by
  apply Context.ext
  intro k
  change (a.replace n ((a.tail n).cons .empty)).get (width+k)=a.get (width-1+k)
  rw [Context.replace_high _ _ (by omega : n≤width+k)]
  have diff : width+k-n=(width+k-(n+1))+1 := by omega
  rw [diff,Context.cons_succ]
  change a.get (n+(width+k-(n+1)))=a.get (width-1+k)
  congr 1
  omega

/-- The old high index is one below the copied index after bra action. -/
theorem braAt_high_tail (a : Context) (n width : Nat) (low : n<width) :
    (braAt n a).tail width=a.tail (width+1) := by
  apply Context.ext
  intro k
  change (a.replace n ((a.tail (n+2)).cons (.pair (a.get (n+1)) (a.get n)))).get (width+k)=a.get (width+1+k)
  rw [Context.replace_high _ _ (by omega : n≤width+k)]
  have diff : width+k-n=(width+k-(n+1))+1 := by omega
  rw [diff,Context.cons_succ]
  change a.get (n+2+(width+k-(n+1)))=a.get (width+1+k)
  congr 1
  omega
end Lamping.AG.InitialOffsets

namespace Lamping.AG
open Graph

theorem Traversal.fan_inverse_high_tail {i width : Nat} {branch : Bool} {a b : Context}
    (rule : Traversal i (.op .fan) (.inl ()) (.inr branch) a b) (low : i<width) :
    a.tail width=b.tail width := by
  have actual := InitialOffsets.Event.apply_rel (.fan i branch) b
  have same : a=InitialOffsets.fanAt i branch b := rule.reverse.output_unique (.direct actual)
  rw [same]
  exact InitialOffsets.fanAt_high_tail b i width low branch

theorem Traversal.cro_inverse_high_tail {i width : Nat} {a b : Context}
    (rule : Traversal i (.op .cro) (.inl ()) (.inr ()) a b) (low : i<width) :
    a.tail width=b.tail (width-1) := by
  have actual := InitialOffsets.Event.apply_rel (.cro i) b
  have same : a=InitialOffsets.croAt i b := rule.reverse.output_unique (.direct actual)
  rw [same]
  exact InitialOffsets.croAt_high_tail b i width low

theorem Traversal.bra_inverse_high_tail {i width : Nat} {a b : Context}
    (rule : Traversal i (.op .bra) (.inl ()) (.inr ()) a b) (low : i<width) :
    a.tail width=b.tail (width+1) := by
  have actual := InitialOffsets.Event.apply_rel (.bra i) b
  have same : a=InitialOffsets.braAt i b := rule.reverse.output_unique (.direct actual)
  rw [same]
  exact InitialOffsets.braAt_high_tail b i width low
end Lamping.AG
