import Lamping.Lambda.ParallelMoves
namespace Lamping.Lambda
namespace ParallelHistory
 def length : ParallelHistory t u → Nat
   | .nil _ => 0
   | .cons _ hs => 1 + hs.length
 theorem length_append (h : ParallelHistory t u) (k : ParallelHistory u v) :
     (h.append k).length = h.length + k.length := by
   induction h with
   | nil => simp [append, length]
   | cons h hs ih => simp only [append, length, ih]; omega
end ParallelHistory

/-- One row of the genuine residual tile grid. Each tile is a complete-
 development parallel-moves square, including the cases with empty residues. -/
inductive StepProjection : {F : List Path} → {t u v w : Term} →
    ParallelStep F t u → ParallelHistory t v → ParallelHistory u w →
    {F' : List Path} → ParallelStep F' v w → Prop where
  | nil (h : ParallelStep F t u) : StepProjection h (.nil t) (.nil u) h
  | cons (sq : ParallelMovesSquare F G t u v w)
      (tail : StepProjection sq.afterSecond σ σ' last) :
      StepProjection sq.first (.cons sq.second σ) (.cons sq.afterFirst σ') last

namespace StepProjection
 theorem exists_projection (h : ParallelStep F t u) (σ : ParallelHistory t v) :
     ∃ (w : Term) (F' : List Path) (σ' : ParallelHistory u w)
       (last : ParallelStep F' v w), StepProjection h σ σ' last := by
   induction σ generalizing u F with
   | nil => exact ⟨_, _, .nil _, h, .nil h⟩
   | cons k ks ih =>
     obtain ⟨w, afterH, afterK, _⟩ := parallel_moves h k
     obtain ⟨z, H, τ, last, htail⟩ := ih afterK
     exact ⟨z, H, .cons afterH τ, last, .cons ⟨h, k, afterH, afterK⟩ htail⟩

 theorem length (h : StepProjection step σ σ' last) : σ'.length = σ.length := by
   induction h with
   | nil => rfl
   | cons sq tail ih => simp only [ParallelHistory.length, ih]

 theorem permutation (h : StepProjection step σ σ' last) :
     PermEq ((ParallelHistory.single step).append σ')
       (σ.append (.single last)) := by
   induction h with
   | nil step =>
     simp only [ParallelHistory.append_nil, ParallelHistory.append]
     exact .refl _
   | cons sq tail ih =>
     have ht := PermEq.prepend (ParallelHistory.single sq.second) ih
     refine .trans ?_ ht
     simpa only [ParallelHistory.append_assoc] using (PermEq.moves sq).append _
end StepProjection
end Lamping.Lambda


