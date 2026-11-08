import Lamping.Lambda.Substitution
namespace Lamping.Lambda

inductive Step where
  | fn | arg | body
  deriving DecidableEq, Repr
abbrev Path := List Step

def subtermAt (t : Term) : Path → Option Term
  | [] => some t
  | s :: p => match t, s with
    | .app f _, .fn => subtermAt f p
    | .app _ a, .arg => subtermAt a p
    | .lam b, .body => subtermAt b p
    | _, _ => none
abbrev Position (t : Term) := {p : Path // (subtermAt t p).isSome}

def IsRedex : Term → Prop
  | .app (.lam _) _ => True
  | _ => False
instance (t : Term) : Decidable (IsRedex t) := by cases t with
  | var _ => exact isFalse id
  | lam _ => exact isFalse id
  | app f _ => cases f <;> simp [IsRedex] <;> infer_instance
abbrev RedexOcc (t : Term) := {p : Path // ∃ u, subtermAt t p = some u ∧ IsRedex u}

def binderDepth : Path → Nat
  | [] => 0
  | .body :: p => binderDepth p + 1
  | _ :: p => binderDepth p

theorem subtermAt_append (t : Term) (p q : Path) :
    subtermAt t (p ++ q) = (subtermAt t p).bind (fun u => subtermAt u q) := by
  induction p generalizing t with
  | nil => simp [subtermAt]
  | cons s p ih => cases t <;> cases s <;> simp [subtermAt, ih]

theorem prefix_exists {t u : Term} {p q : Path} (h : subtermAt t (p ++ q) = some u) :
    ∃ v, subtermAt t p = some v ∧ subtermAt v q = some u := by
  rw [subtermAt_append] at h
  cases hp : subtermAt t p with
  | none => simp [hp] at h
  | some v => exact ⟨v, rfl, by simpa [hp] using h⟩

theorem binderDepth_append (p q : Path) : binderDepth (p ++ q) = binderDepth p + binderDepth q := by
  induction p with
  | nil => simp [binderDepth]
  | cons s p ih => cases s <;> simp [binderDepth, ih, Nat.add_comm, Nat.add_left_comm]

theorem scoped_subterm {t u : Term} {p : Path} {n : Nat}
    (ht : Scoped n t) (hp : subtermAt t p = some u) : Scoped (n + binderDepth p) u := by
  induction p generalizing n t with
  | nil => simp only [subtermAt, Option.some.injEq] at hp; subst u; simpa [binderDepth] using ht
  | cons s p ih =>
    cases t with
    | var i => cases s <;> simp [subtermAt] at hp
    | app f a =>
      cases s with
      | fn => exact ih ht.1 hp
      | arg => exact ih ht.2 hp
      | body => simp [subtermAt] at hp
    | lam b =>
      cases s with
      | fn => simp [subtermAt] at hp
      | arg => simp [subtermAt] at hp
      | body => simpa [binderDepth, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using (ih (t := b) ht hp)

def replaceAt : Term → Path → Term → Option Term
  | _, [], u => some u
  | .app f a, .fn :: p, u => (replaceAt f p u).map (fun f' => .app f' a)
  | .app f a, .arg :: p, u => (replaceAt a p u).map (Term.app f)
  | .lam b, .body :: p, u => (replaceAt b p u).map Term.lam
  | _, _, _ => none

theorem replaceAt_lookup {t v : Term} {p : Path} (hp : subtermAt t p = some v) (u : Term) :
    ∃ t', replaceAt t p u = some t' ∧ subtermAt t' p = some u := by
  induction p generalizing t with
  | nil => exact ⟨u, by simp [replaceAt], by simp [subtermAt]⟩
  | cons s p ih =>
    cases t with
    | var i => cases s <;> simp [subtermAt] at hp
    | app f a =>
      cases s with
      | fn =>
        obtain ⟨f', hr, hl⟩ := ih hp
        exact ⟨.app f' a, by simp [replaceAt, hr], hl⟩
      | arg =>
        obtain ⟨a', hr, hl⟩ := ih hp
        exact ⟨.app f a', by simp [replaceAt, hr], hl⟩
      | body => simp [subtermAt] at hp
    | lam b =>
      cases s with
      | fn => simp [subtermAt] at hp
      | arg => simp [subtermAt] at hp
      | body =>
        obtain ⟨b', hr, hl⟩ := ih hp
        exact ⟨.lam b', by simp [replaceAt, hr], hl⟩

def positions : Term → List Path
  | .var _ => [[]]
  | .app f a => [] :: ((positions f).map (.fn :: ·) ++ (positions a).map (.arg :: ·))
  | .lam b => [] :: (positions b).map (.body :: ·)

theorem mem_positions (t : Term) (p : Path) : p ∈ positions t ↔ ∃ u, subtermAt t p = some u := by
  induction t generalizing p with
  | var i => cases p with
    | nil => simp [positions, subtermAt]
    | cons s p => cases s <;> simp [positions, subtermAt]
  | app f a hf ha => cases p with
    | nil => simp [positions, subtermAt]
    | cons s p => cases s <;> simp [positions, subtermAt, hf, ha]
  | lam b hb => cases p with
    | nil => simp [positions, subtermAt]
    | cons s p => cases s <;> simp [positions, subtermAt, hb]

def redexPositions (t : Term) : List Path :=
  (positions t).filter (fun p => ((subtermAt t p).map (fun u => decide (IsRedex u))).getD false)

theorem mem_redexPositions (t : Term) (p : Path) :
    p ∈ redexPositions t ↔ ∃ u, subtermAt t p = some u ∧ IsRedex u := by
  simp only [redexPositions, List.mem_filter]
  cases h : subtermAt t p with
  | none => simp
  | some u => simp [(mem_positions t p).mpr ⟨u, h⟩]
/-- Replacing a selected subterm by itself reconstructs the entire term. -/
theorem replaceAt_self {t v : Term} {p : Path} (h : subtermAt t p = some v) :
    replaceAt t p v = some t := by
  induction p generalizing t with
  | nil => simp only [subtermAt, Option.some.injEq] at h; subst v; cases t <;> rfl
  | cons s p ih =>
    cases t with
    | var i => cases s <;> simp [subtermAt] at h
    | app f a => cases s with
      | fn => simp [replaceAt, ih h]
      | arg => simp [replaceAt, ih h]
      | body => simp [subtermAt] at h
    | lam b => cases s with
      | fn => simp [subtermAt] at h
      | arg => simp [subtermAt] at h
      | body => simp [replaceAt, ih h]

/-- Structural replacement preserves scope when the inserted term has the scope
    available at that occurrence; replacement itself performs no index shift. -/
theorem scoped_replaceAt {t t' u : Term} {p : Path} {n : Nat}
    (ht : Scoped n t) (hu : Scoped (n + binderDepth p) u)
    (hr : replaceAt t p u = some t') : Scoped n t' := by
  induction p generalizing t t' n with
  | nil => cases t <;> simp only [replaceAt, Option.some.injEq] at hr <;> subst t' <;> simpa [binderDepth] using hu
  | cons s p ih =>
    cases t with
    | var i => cases s <;> simp [replaceAt] at hr
    | app f a => cases s with
      | fn =>
        simp only [replaceAt] at hr
        cases he : replaceAt f p u with
        | none => simp [he] at hr
        | some f' => simp only [he, Option.map_some, Option.some.injEq] at hr; subst t'; exact ⟨ih ht.1 hu he, ht.2⟩
      | arg =>
        simp only [replaceAt] at hr
        cases he : replaceAt a p u with
        | none => simp [he] at hr
        | some a' => simp only [he, Option.map_some, Option.some.injEq] at hr; subst t'; exact ⟨ht.1, ih ht.2 hu he⟩
      | body => simp [replaceAt] at hr
    | lam b => cases s with
      | fn => simp [replaceAt] at hr
      | arg => simp [replaceAt] at hr
      | body =>
        simp only [replaceAt] at hr
        cases he : replaceAt b p u with
        | none => simp [he] at hr
        | some b' =>
          simp only [he, Option.map_some, Option.some.injEq] at hr
          subst t'
          apply ih (t := b) (n := n+1) ht _ he
          simpa [binderDepth, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hu
end Lamping.Lambda




