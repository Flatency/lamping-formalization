import Lamping.Lamping.InitialOffsetFormula
namespace Lamping.AG.InitialOffsets

/-- The inserted binder level reads only input levels strictly below the
first Cro index; its fan word may be nonempty even when the offset is zero. -/
theorem Shape.level_replace (shape : Shape) (n : Nat) (a y : Context) :
    shape.level (a.replace (n+shape.offset) y) n=shape.level a n := by
  induction shape generalizing n with
  | base w => rfl
  | lower h w ih =>
    change marks w (.pair (h.level (a.replace (n+(h.offset+1)) y) (n+1))
      ((a.replace (n+(h.offset+1)) y).get n))=marks w (.pair (h.level a (n+1)) (a.get n))
    have indices : n+(h.offset+1)=(n+1)+h.offset := by omega
    rw [Context.replace_low _ _ (by omega : n<n+(h.offset+1)),indices,ih]

theorem Shape.execute_tail (shape : Shape) (n : Nat) (a : Context) :
    (shape.execute n a).tail (n+1)=a.tail (n+shape.offset) := by
  rw [corrected_program_formula,tail_replace,tail_cons_one]

/-- Uniform tail transport for the actual descending control program. -/
theorem Shape.execute_replace (shape : Shape) (n : Nat) (a y : Context) :
    shape.execute n (a.replace (n+shape.offset) y)=(shape.execute n a).replace (n+1) y := by
  rw [corrected_program_formula,corrected_program_formula,shape.level_replace]
  have inputTail : (a.replace (n+shape.offset) y).tail (n+shape.offset)=y := by
    simpa only [Nat.add_zero,tail_zero] using tail_replace a y (n+shape.offset) 0
  rw [inputTail]
  ext k
  by_cases low : k<n
  · simp only [Context.replace_low _ _ low,Context.replace_low _ _ (by omega : k<n+shape.offset),
      Context.replace_low _ _ (by omega : k<n+1)]
  · by_cases equal : k=n
    · subst k
      simp only [Context.replace_high _ _ (Nat.le_refl n),Nat.sub_self,Context.cons_zero,
        Context.replace_low _ _ (Nat.lt_succ_self n)]
    · have diff : k-n=(k-(n+1))+1 := by omega
      simp only [Context.replace_high _ _ (by omega : n≤k),
        Context.replace_high _ _ (by omega : n+1≤k),diff,Context.cons_succ]
end Lamping.AG.InitialOffsets
