import Lamping.Lamping.System
namespace Lamping.AG
/-- AG98 Definition 3.4.1. Pair is a level constructor, not context cons. -/
inductive Level where
  | empty | o (a : Level) | star (a : Level) | pair (a b : Level)
  deriving DecidableEq, Repr
/-- Extensional infinite lists with finite support: trailing empty levels are invisible. -/
structure Context where
  get : Nat → Level
  finite : ∃ n, ∀ k, n ≤ k → get k = .empty
namespace Context
@[ext] theorem ext {a b : Context} (h : ∀ k, a.get k = b.get k) : a = b := by
  cases a; cases b; congr; funext k; exact h k
def empty : Context := ⟨fun _ => .empty, ⟨0,by intros; rfl⟩⟩
def cons (a : Context) (x : Level) : Context :=
  ⟨fun k => match k with | 0 => x | n+1 => a.get n,
   by obtain ⟨n,hn⟩ := a.finite; exact ⟨n+1,by intro k hk; cases k with
        | zero => omega
        | succ k => exact hn k (by omega)⟩⟩
@[simp] theorem cons_zero (a : Context) (x : Level) : (cons a x).get 0 = x := rfl
@[simp] theorem cons_succ (a : Context) (x : Level) (k) : (cons a x).get (k+1) = a.get k := rfl
@[simp] theorem empty_at (k) : empty.get k = .empty := rfl
@[simp] theorem cons_empty : cons empty .empty = empty := by ext k; cases k <;> rfl
/-- Replace the subcontext at width n, preserving exactly the lower n levels. -/
def replace (a : Context) (n : Nat) (b : Context) : Context :=
  ⟨fun k => if k < n then a.get k else b.get (k-n),
   by obtain ⟨m,hm⟩ := b.finite; refine ⟨n+m,?_⟩; intro k hk
      simp only [if_neg (by omega : ¬k<n)]; exact hm _ (by omega)⟩
def tail (a : Context) (n : Nat) : Context :=
  ⟨fun k => a.get (n+k),by obtain ⟨m,hm⟩ := a.finite; exact ⟨m,by intro k hk; exact hm _ (by omega)⟩⟩
@[simp] theorem replace_low (a b : Context) {k n : Nat} (h : k<n) :
    (a.replace n b).get k = a.get k := by simp [replace,h]
@[simp] theorem replace_high (a b : Context) {k n : Nat} (h : n≤k) :
    (a.replace n b).get k = b.get (k-n) := by simp [replace,Nat.not_lt.mpr h]
@[simp] theorem replace_zero (a b : Context) : a.replace 0 b = b := by ext k; simp [replace]
@[simp] theorem replace_tail (a : Context) (n : Nat) : a.replace n (a.tail n) = a := by
  ext k; simp only [replace]; split
  · rfl
  · simp only [tail]; congr 1; omega
@[simp] theorem replace_replace (a b c : Context) (n : Nat) :
    (a.replace n b).replace n c = a.replace n c := by
  ext k; simp only [replace]; split <;> simp_all
/-- Low shell equality, used for binding loops; it is not full context equality. -/
def SameShell (n : Nat) (a b : Context) : Prop := ∀ k, k<n → a.get k=b.get k
theorem sameShell_replace (a b : Context) (n : Nat) : SameShell n a (a.replace n b) := by
  intro k hk; exact (replace_low a b hk).symm
end Context
end Lamping.AG


namespace Lamping.AG.Context
/-- Composition of two independently chosen low shells. -/
theorem replace_nested (s a b : Context) (n k : Nat) :
    (s.replace n a).replace (n+k) b = s.replace n (a.replace k b) := by
  ext t
  by_cases h : t<n
  · simp [replace,h,show t<n+k by omega]
  · by_cases j : t<n+k
    · simp [replace,h,j,show t-n<k by omega]
    · simp [replace,h,j,show ¬t-n<k by omega,show t-(n+k)=t-n-k by omega]
/-- A context's low prefix can be extended by one level without normalization choices. -/
theorem replace_cons (s a : Context) (n : Nat) (x : Level) :
    s.replace n (a.cons x) = (s.replace n (empty.cons x)).replace (n+1) a := by
  ext t
  by_cases h : t<n
  · simp [replace,h,show t<n+1 by omega]
  · by_cases e : t=n
    · subst t; simp [replace,cons]
    · have ht : ¬t<n+1 := by omega
      have hd : t-n=(t-(n+1))+1 := by omega
      simp [replace,h,ht,hd,cons]
end Lamping.AG.Context
namespace Lamping.AG.Context
@[simp] theorem cons_replace_one (a : Context) (x : Level) :
    (empty.cons x).replace 1 a = a.cons x := by
  ext k; cases k with
  | zero => rfl
  | succ k => simp [replace,cons]
end Lamping.AG.Context
namespace Lamping.AG.Context
/-- Finite input notation; tail empties have no semantic identity. -/
def ofList : List Level → Context
  | [] => empty
  | x::xs => (ofList xs).cons x
/-- Computable canonicalisation of finite notation, removing exactly trailing empties. -/
def normalise : List Level → List Level
  | [] => []
  | x::xs => let tail := normalise xs
             if tail=[] ∧ x=.empty then [] else x::tail
@[simp] theorem ofList_nil : ofList []=empty := rfl
@[simp] theorem ofList_cons (x : Level) (xs : List Level) : ofList (x::xs)=(ofList xs).cons x := rfl
theorem cons_injective {a b : Context} {x y : Level} (h : a.cons x=b.cons y) : a=b ∧ x=y := by
  refine ⟨?_,?_⟩
  · ext k; exact congrArg (fun c : Context => c.get (k+1)) h
  · exact congrArg (fun c : Context => c.get 0) h
@[simp] theorem ofList_normalise (xs : List Level) : ofList (normalise xs)=ofList xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [normalise]
    split
    · rename_i h
      obtain ⟨ht,hx⟩ := h
      rw [ofList_cons,←ih,ht,hx]
      exact cons_empty.symm
    · simpa only [ofList_cons] using congrArg (fun c => c.cons x) ih
@[simp] theorem normalise_idempotent (xs : List Level) : normalise (normalise xs)=normalise xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [normalise]
    split
    · rfl
    · rename_i hn
      simp only [normalise,ih,if_neg hn]
theorem normalise_empty_ofList_empty (xs : List Level) (h : ofList xs=empty) : normalise xs=[] := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    have hx : x=.empty := congrArg (fun c : Context => c.get 0) h
    have ht : ofList xs=empty := by
      ext k; exact congrArg (fun c : Context => c.get (k+1)) h
    simp [normalise,ih ht,hx]
/-- Canonical finite notation is unique: equality is extensional finite-support equality,
not equality of the input list or of its arbitrarily padded representation. -/
theorem normalise_unique (xs ys : List Level) (h : ofList xs=ofList ys) : normalise xs=normalise ys := by
  induction xs generalizing ys with
  | nil => exact (normalise_empty_ofList_empty ys h.symm).symm
  | cons x xs ih =>
    cases ys with
    | nil => exact normalise_empty_ofList_empty (x::xs) h
    | cons y ys =>
      obtain ⟨tails,heads⟩ := cons_injective h
      subst y
      simp only [normalise,ih ys tails]
end Lamping.AG.Context
namespace Lamping.AG.Context
def snapshot (a : Context) : Nat → List Level
  | 0 => []
  | n+1 => a.get 0 :: snapshot (a.tail 1) n
theorem snapshot_get (a : Context) (n k : Nat) :
    (ofList (snapshot a n)).get k = if k<n then a.get k else .empty := by
  induction n generalizing a k with
  | zero => simp [snapshot]
  | succ n ih =>
    cases k with
    | zero => simp [snapshot]
    | succ k => simpa [snapshot,tail,Nat.add_comm] using ih (a.tail 1) k
theorem finite_representation (a : Context) : ∃ xs, ofList xs=a := by
  obtain ⟨n,hn⟩ := a.finite
  refine ⟨snapshot a n,?_⟩
  ext k
  rw [snapshot_get]
  split
  · rfl
  · exact (hn k (by omega)).symm
/-- Every finite-support context has a unique normalized finite representative. -/
theorem canonical_representation (a : Context) :
    ∃ xs, normalise xs=xs ∧ ofList xs=a ∧ ∀ ys, normalise ys=ys → ofList ys=a → ys=xs := by
  obtain ⟨xs,hxs⟩ := finite_representation a
  refine ⟨normalise xs,normalise_idempotent xs,by simpa using hxs,?_⟩
  intro ys hyn hya
  have eq := normalise_unique ys xs (hya.trans hxs.symm)
  simpa only [hyn] using eq
end Lamping.AG.Context

namespace Lamping.AG.Context
def SupportBound (a : Context) (n : Nat) : Prop := ∀ k, n≤k → a.get k=.empty
theorem least_support_bound (a : Context) : ∃ n, SupportBound a n ∧ ∀ m, SupportBound a m → n≤m := by
  obtain ⟨n,hn⟩ := a.finite
  suffices ∀ n, SupportBound a n → ∃ k, SupportBound a k ∧ ∀ m, SupportBound a m → k≤m from this n hn
  intro n
  induction n with
  | zero => intro h; exact ⟨0,h,by intros; omega⟩
  | succ n ih =>
    intro h
    classical
    by_cases lower : SupportBound a n
    · exact ih lower
    · refine ⟨n+1,h,?_⟩
      intro m hm
      by_cases large : n+1≤m
      · exact large
      exfalso
      apply lower
      intro k hk
      exact hm k (by omega)
/-- Least support bound on the semantic representation; list normalise is computable. -/
noncomputable def width (a : Context) : Nat := Classical.choose (least_support_bound a)
theorem width_bound (a : Context) (k : Nat) (h : a.width≤k) : a.get k=.empty :=
  (Classical.choose_spec (least_support_bound a)).1 k h
theorem width_least (a : Context) (n : Nat) (h : SupportBound a n) : a.width≤n :=
  (Classical.choose_spec (least_support_bound a)).2 n h
end Lamping.AG.Context

