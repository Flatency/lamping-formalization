import Lamping.Lambda.Substitution
import Lamping.Lambda.Occurrences
import Lamping.Lambda.Named
open Lamping.Lambda
-- Capture avoidance: a free substituted variable remains free under one/two binders.
example : subst (fun _ => Term.var 0) (.lam (.var 1)) = .lam (.var 1) := rfl
example : subst (fun _ => Term.var 0) (.lam (.lam (.var 2))) = .lam (.lam (.var 2)) := rfl
example : subst (fun _ => Term.var 7) (.lam (.var 0)) = .lam (.var 0) := rfl
example (t : Term) : subst Term.var t = t := subst_id t
example (t : Term) (σ τ : Nat → Term) : subst τ (subst σ t) = subst (fun i => subst τ (σ i)) t := subst_comp τ σ t
example (t : Term) (ρ τ : Nat → Nat) : rename τ (rename ρ t) = rename (τ ∘ ρ) t := rename_comp τ ρ t
example : subtermAt (.lam (.app (.var 0) (.var 1))) [.body, .arg] = some (.var 1) := rfl
example : subtermAt (.lam (.var 0)) [.fn] = none := rfl
example : binderDepth [.body, .fn, .body, .arg] = 2 := rfl
example : redexPositions (.app (.lam (.var 0)) (.app (.lam (.var 0)) (.var 2))) = [[], [.arg]] := rfl
example : replaceAt (.lam (.app (.var 0) (.var 1))) [.body, .arg] (.var 3) = some (.lam (.app (.var 0) (.var 3))) := rfl
-- Shadowing must choose the nearest same-name binder.
example : Named.findName ["x", "y", "x"] "x" = some 0 := by decide
example : Named.erase [] (.lam "x" (.lam "y" (.var "x"))) = .lam (.lam (.var 1)) := by decide
example : Named.erase [] (.lam "x" (.lam "x" (.var "x"))) = .lam (.lam (.var 0)) := by decide
example : Named.Alpha [] (.lam "x" (.lam "y" (.var "x"))) [] (.lam "z" (.lam "w" (.var "z"))) :=
  .lam (.lam (.var (.there (by decide) .here) (.there (by decide) .here)))
example : Named.access (.lam "x" (.lam "y" (.var "x"))) [] [.body, .body] = some (.var "x", ["y", "x"]) := rfl
#print axioms rename_comp
#print axioms rename_subst
#print axioms subst_rename
#print axioms subst_comp
#print axioms scoped_subst
#print axioms scoped_subterm
#print axioms subtermAt_append
#print axioms mem_redexPositions
#print axioms replaceAt_lookup
#print axioms Named.findName_iff_binding
#print axioms Named.access_binding
#print axioms Named.alpha_erase
example {t v : Term} {p : Path} (h : subtermAt t p = some v) : replaceAt t p v = some t := replaceAt_self h
example {t t' u : Term} {p : Path} {n : Nat} (ht : Scoped n t) (hu : Scoped (n + binderDepth p) u) (hr : replaceAt t p u = some t') : Scoped n t' := scoped_replaceAt ht hu hr
example {Γ Δ : List String} {t u : Named.Term} (ht : Named.Resolved Γ t) (hu : Named.Resolved Δ u) : Named.Alpha Γ t Δ u ↔ Named.erase Γ t = Named.erase Δ u := Named.alpha_iff_erase ht hu
#print axioms scoped_replaceAt
#print axioms replaceAt_self
#print axioms Named.alpha_iff_erase
