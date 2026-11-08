import Lamping.Lamping.ControlContextTails
namespace Lamping.AG.InitialOffsets

theorem fanAt_get (a : Context) (i : Nat) (branch : Bool) (k : Nat) :
    (fanAt i branch a).get k=if k=i then mark branch (a.get i) else a.get k := by
  by_cases low : k<i
  · simp [fanAt,Context.replace,low,show k≠i by omega]
  · by_cases same : k=i
    · subst k; simp [fanAt,Context.replace]
    · rw [if_neg same]
      unfold fanAt
      rw [Context.replace_high _ _ (by omega : i≤k),show k-i=(k-(i+1))+1 by omega,Context.cons_succ]
      change a.get (i+1+(k-(i+1)))=a.get k
      congr 1
      omega

theorem croAt_get (a : Context) (i k : Nat) :
    (croAt i a).get k=if k<i then a.get k else if k=i then .empty else a.get (k-1) := by
  by_cases low : k<i
  · simp [croAt,Context.replace,low]
  · by_cases same : k=i
    · subst k; simp [croAt,Context.replace]
    · simp only [if_neg low,if_neg same]
      unfold croAt
      rw [Context.replace_high _ _ (by omega : i≤k),show k-i=(k-i-1)+1 by omega,Context.cons_succ]
      change a.get (i+(k-i-1))=a.get (k-1)
      congr 1
      omega

theorem braAt_get (a : Context) (i k : Nat) :
    (braAt i a).get k=if k<i then a.get k else if k=i then .pair (a.get (i+1)) (a.get i) else a.get (k+1) := by
  by_cases low : k<i
  · simp [braAt,Context.replace,low]
  · by_cases same : k=i
    · subst k; simp [braAt,Context.replace]
    · simp only [if_neg low,if_neg same]
      unfold braAt
      rw [Context.replace_high _ _ (by omega : i≤k),show k-i=(k-i-1)+1 by omega,Context.cons_succ]
      change a.get (i+2+(k-i-1))=a.get (k+1)
      congr 1
      omega

private theorem mark_unique {left right : Bool} {a b : Level} (same : mark left a=mark right b) :
    left=right ∧a=b := by
  cases left <;> cases right <;> simp only [mark,Bool.false_eq_true,if_false,if_true] at same ⊢
  all_goals cases same <;> exact ⟨True.intro,rfl⟩

/-- A copied fan branch is recoverable from any shell above its index.
The underlying shell is also recovered, not merely the branch name. -/
theorem fanAt_same_shell_iff (a b : Context) (i width : Nat) (below : i<width) (left right : Bool) :
    Context.SameShell width (fanAt i left a) (fanAt i right b) ↔
      left=right ∧Context.SameShell width a b := by
  constructor
  · intro shell
    have marked := shell i below
    simp only [fanAt_get] at marked
    obtain ⟨branch,level⟩ := mark_unique marked
    refine ⟨branch,?_⟩
    intro k bounded
    by_cases same : k=i
    · subst k; exact level
    · simpa only [fanAt_get,if_neg same] using shell k bounded
  · rintro ⟨rfl,shell⟩ k bounded
    simp only [fanAt_get]
    by_cases same : k=i
    · subst k; rw [shell i below]
    · simp only [if_neg same]; exact shell k bounded

theorem croAt_same_shell_iff (a b : Context) (i width : Nat) (below : i<width) :
    Context.SameShell width (croAt i a) (croAt i b) ↔Context.SameShell (width-1) a b := by
  constructor
  · intro shell k bounded
    by_cases low : k<i
    · simpa only [croAt_get,if_pos low] using shell k (by omega)
    · have high := shell (k+1) (by omega)
      simpa only [croAt_get,if_neg (show ¬k+1<i by omega),if_neg (show k+1≠i by omega),Nat.add_sub_cancel] using high
  · intro shell k bounded
    simp only [croAt_get]
    by_cases low : k<i
    · simp only [if_pos low]; exact shell k (by omega)
    · simp only [if_neg low]
      by_cases same : k=i
      · simp only [if_pos same]
      · simp only [if_neg same]; exact shell (k-1) (by omega)

theorem braAt_same_shell_iff (a b : Context) (i width : Nat) (below : i<width) :
    Context.SameShell width (braAt i a) (braAt i b) ↔Context.SameShell (width+1) a b := by
  constructor
  · intro shell k bounded
    have pair := shell i below
    simp only [braAt_get,if_neg (Nat.lt_irrefl i)] at pair
    have parts := Level.pair.inj pair
    by_cases low : k<i
    · simpa only [braAt_get,if_pos low] using shell k (by omega)
    · by_cases same : k=i
      · subst k; exact parts.2
      · by_cases next : k=i+1
        · subst k; exact parts.1
        · have high := shell (k-1) (by omega)
          simpa only [braAt_get,if_neg (show ¬k-1<i by omega),if_neg (show k-1≠i by omega),
            show k-1+1=k by omega] using high
  · intro shell k bounded
    simp only [braAt_get]
    by_cases low : k<i
    · simp only [if_pos low]; exact shell k (by omega)
    · simp only [if_neg low]
      by_cases same : k=i
      · subst k
        rw [shell (i+1) (by omega),shell i (by omega)]
      · simp only [if_neg same]; exact shell (k+1) (by omega)
end Lamping.AG.InitialOffsets

