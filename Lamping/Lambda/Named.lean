import Lamping.Lambda.Occurrences
namespace Lamping.Lambda
namespace Named

inductive Term where
  | var : String → Term
  | app : Term → Term → Term
  | lam : String → Term → Term
  deriving DecidableEq, Repr

def findName : List String → String → Option Nat
  | [], _ => none
  | y :: ys, x => if x = y then some 0 else (findName ys x).map Nat.succ

/-- Nearest binder: passing a binder is permitted only when its name differs. -/
inductive Binding : List String → String → Nat → Prop
  | here : Binding (x :: Γ) x 0
  | there : x ≠ y → Binding Γ x i → Binding (y :: Γ) x (i+1)

theorem findName_iff_binding (Γ : List String) (x : String) (i : Nat) :
    findName Γ x = some i ↔ Binding Γ x i := by
  induction Γ generalizing i with
  | nil => simp only [findName, reduceCtorEq, false_iff]; intro h; cases h
  | cons y Γ ih =>
    by_cases h : x = y
    · subst y
      simp only [findName, ↓reduceIte, Option.some.injEq]
      constructor
      · intro hi; subst i; exact .here
      · intro hb; cases hb with
        | here => rfl
        | there hn _ => exact False.elim (hn rfl)
    · simp only [findName, if_neg h]
      constructor
      · intro hi
        cases he : findName Γ x with
        | none => simp [he] at hi
        | some j =>
          simp only [he, Option.map_some, Option.some.injEq] at hi
          subst i
          exact .there h ((ih j).mp he)
      · intro hb
        cases hb with
        | here => exact False.elim (h rfl)
        | there _ hj => simp [(ih _).mpr hj]

theorem binding_lt {Γ : List String} {x : String} {i : Nat} (h : Binding Γ x i) : i < Γ.length := by
  induction h with
  | here => exact Nat.zero_lt_succ _
  | there _ _ ih => exact Nat.succ_lt_succ ih

/-- Total on open named syntax; unbound names map to the first index beyond Γ.
    The `Resolved` predicate rules out this sentinel in all correctness uses. -/
def erase (Γ : List String) : Term → Lamping.Lambda.Term
  | .var x => .var ((findName Γ x).getD Γ.length)
  | .app f a => .app (erase Γ f) (erase Γ a)
  | .lam x b => .lam (erase (x :: Γ) b)

def Resolved (Γ : List String) : Term → Prop
  | .var x => ∃ i, Binding Γ x i
  | .app f a => Resolved Γ f ∧ Resolved Γ a
  | .lam x b => Resolved (x :: Γ) b

theorem erase_var_binding {Γ : List String} {x : String} {i : Nat} (h : Binding Γ x i) :
    erase Γ (.var x) = .var i := by simp [erase, (findName_iff_binding Γ x i).mpr h]

theorem erase_scoped {Γ : List String} {t : Term} (h : Resolved Γ t) : Scoped Γ.length (erase Γ t) := by
  induction t generalizing Γ with
  | var x => obtain ⟨i, hi⟩ := h; rw [erase_var_binding hi]; exact binding_lt hi
  | app f a hf ha => exact ⟨hf h.1, ha h.2⟩
  | lam x b hb => exact hb h

/-- Access paths retain the exact binder environment at their endpoint. -/
def access (t : Term) (Γ : List String) : Path → Option (Term × List String)
  | [] => some (t, Γ)
  | s :: p => match t, s with
    | .app f _, .fn => access f Γ p
    | .app _ a, .arg => access a Γ p
    | .lam x b, .body => access b (x :: Γ) p
    | _, _ => none

theorem access_erase {t u : Term} {Γ Δ : List String} {p : Path}
    (h : access t Γ p = some (u, Δ)) : subtermAt (erase Γ t) p = some (erase Δ u) := by
  induction p generalizing t Γ with
  | nil => simp only [access, Option.some.injEq, Prod.mk.injEq] at h; rcases h with ⟨rfl, rfl⟩; simp [subtermAt]
  | cons s p ih =>
    cases t with
    | var x => cases s <;> simp [access] at h
    | app f a => cases s with
      | fn => exact ih h
      | arg => exact ih h
      | body => simp [access] at h
    | lam x b => cases s with
      | fn => simp [access] at h
      | arg => simp [access] at h
      | body => exact ih h

theorem access_depth {t u : Term} {Γ Δ : List String} {p : Path}
    (h : access t Γ p = some (u, Δ)) : Δ.length = Γ.length + binderDepth p := by
  induction p generalizing t Γ with
  | nil => simp only [access, Option.some.injEq, Prod.mk.injEq] at h; rcases h with ⟨rfl, rfl⟩; simp [binderDepth]
  | cons s p ih =>
    cases t with
    | var x => cases s <;> simp [access] at h
    | app f a => cases s with
      | fn => exact ih h
      | arg => exact ih h
      | body => simp [access] at h
    | lam x b => cases s with
      | fn => simp [access] at h
      | arg => simp [access] at h
      | body => simpa [List.length_cons, binderDepth, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ih h

theorem access_binding {t : Term} {Γ Δ : List String} {p : Path} {x : String} {i : Nat}
    (hp : access t Γ p = some (.var x, Δ)) (hb : Binding Δ x i) :
    subtermAt (erase Γ t) p = some (.var i) := by
  rw [access_erase hp, erase_var_binding hb]

/-- Alpha comparison matches binding indices in related contexts, not spellings. -/
inductive Alpha : List String → Term → List String → Term → Prop
  | var : Binding Γ x i → Binding Δ y i → Alpha Γ (.var x) Δ (.var y)
  | app : Alpha Γ f Δ f' → Alpha Γ a Δ a' → Alpha Γ (.app f a) Δ (.app f' a')
  | lam : Alpha (x :: Γ) b (y :: Δ) b' → Alpha Γ (.lam x b) Δ (.lam y b')

theorem alpha_erase {Γ Δ : List String} {t u : Term} (h : Alpha Γ t Δ u) : erase Γ t = erase Δ u := by
  induction h with
  | var hx hy => rw [erase_var_binding hx, erase_var_binding hy]
  | app _ _ hf ha => simp [erase, hf, ha]
  | lam _ hb => simp [erase, hb]
/-- On resolved syntax the independent binding-based Alpha relation exactly
    characterizes equality of de Bruijn compilation. -/
theorem alpha_iff_erase {Γ Δ : List String} {t u : Term}
    (ht : Resolved Γ t) (hu : Resolved Δ u) :
    Alpha Γ t Δ u ↔ erase Γ t = erase Δ u := by
  constructor
  · exact alpha_erase
  · intro he
    induction t generalizing Γ Δ u with
    | var x =>
      cases u with
      | var y =>
        obtain ⟨i, hi⟩ := ht
        obtain ⟨j, hj⟩ := hu
        rw [erase_var_binding hi, erase_var_binding hj] at he
        cases he
        exact .var hi hj
      | app f a => cases he
      | lam y b => cases he
    | app f a hf ha =>
      cases u with
      | var y => cases he
      | app f' a' =>
        simp only [erase, Lamping.Lambda.Term.app.injEq] at he
        exact .app (hf ht.1 hu.1 he.1) (ha ht.2 hu.2 he.2)
      | lam y b => cases he
    | lam x b hb =>
      cases u with
      | var y => cases he
      | app f a => cases he
      | lam y b' =>
        simp only [erase, Lamping.Lambda.Term.lam.injEq] at he
        exact .lam (hb ht hu he)
end Named
end Lamping.Lambda


