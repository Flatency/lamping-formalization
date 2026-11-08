import Lamping.Lambda.BetaPaths
import Lamping.Lamping.FreeVars
import Lamping.Lamping.Compose
import Lamping.Lambda.ResidualInit
import Lamping.Lambda.ResidualSelection
open Lamping.Lambda Lamping.AG

example : contract (.lam (.var 1)) (.var 0) = .lam (.var 1) := rfl
example : BetaAt (.lam (.app (.lam (.var 0)) (.var 0))) [.body] (.lam (.var 0)) :=
  ⟨.var 0, .var 0, rfl, rfl⟩
example (h : Beta t u) : ∃ p, BetaAt t p u := beta_iff_betaAt.mp h
example (h : BetaAt t p u) : Beta t u := h.beta
example (h : Betas t u) (ht : Closed t) : Closed u := h.scoped ht

example : free (.lam (.app (.var 0) (.var 2))) 1 := by decide
example : ¬ free (.lam (.app (.var 0) (.var 2))) 0 := by decide
example (h : Closed t) (x : FV t) : False := closed_fv_empty h x
example (t : Term) : Scoped n t ↔ ∀ k, free t k → k < n := scoped_iff_free_lt t n
example : freeList (.app (.var 1) (.var 1)) = [1,1] := rfl

#print axioms Lamping.Lambda.beta_iff_betaAt
#print axioms Lamping.Lambda.Betas.scoped
#print axioms Lamping.AG.mem_freeList
#print axioms Lamping.AG.scoped_iff_free_lt
#print axioms Lamping.AG.closed_fv_empty

open Lamping.Lambda.Marked
example (F : List Path) (t : Term) : (mark F t).erase = t := erase_mark F t
example (F : List Path) (t : Term) : Valid (mark F t) := valid_mark F t
example (F : List Path) (t : Term) (p : Path) :
    p ∈ activePositions (mark F t) ↔ p ∈ F ∧ p ∈ redexPositions t := active_mark F t p
example (F : List Path) (t : Term) (r p : Path) :
    p ∈ tracePositions r (mark F t) ↔ r = p ∧ p ∈ redexPositions t := trace_mark F t r p
example : activePositions (mark [[]] (.var 0)) = [] := rfl
example : tracePositions [] (mark [] (.app (.lam (.var 0)) (.var 1))) = [[]] := rfl
example : activePositions (mark [] (.app (.lam (.var 0)) (.var 1))) = [] := rfl

#print axioms Lamping.AG.union_left
#print axioms Lamping.AG.union_right
#print axioms Lamping.Lambda.Marked.erase_mark
#print axioms Lamping.Lambda.Marked.valid_mark
#print axioms Lamping.Lambda.Marked.active_mark
#print axioms Lamping.Lambda.Marked.trace_mark

example (F : List Path) (t : Term) : Selected F (mark F t) := selected_mark F t
example (hs : Selected F t) (h : History ps t u) : Selected F u := h.selected hs
example (hs : Selected F t) (p : Path) :
    p ∈ activePositions t ↔ ∃ r, r ∈ F ∧ p ∈ tracePositions r t := active_iff_selected_trace hs p
example : ¬ Selected [] (.red [[]] (.var 0) (.var 0)) := by simp [Selected]
example : Selected [[]] (.red [[]] (.var 0) (.var 0)) := by simp [Selected]
#print axioms Lamping.Lambda.Marked.Selected.subst
#print axioms Lamping.Lambda.Marked.ReductionAt.selected
#print axioms Lamping.Lambda.Marked.selected_mark
#print axioms Lamping.Lambda.Marked.active_iff_selected_trace
