import Lamping.Lamping.PathDefinitions
namespace Lamping.AG
open Graph
section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable {g : Net signature N B W}

theorem Labelling.walk (h : Labelling g es a b) : Walk g es := by
  induction h with
  | single e a => exact .single e
  | cons h _ ih => exact .cons h.turn ih

theorem ProperPath.walk (h : ProperPath g es) : Walk g es := by
  obtain ⟨a,b,h⟩ := h; exact h.walk

theorem Labelling.nonempty (h : Labelling g es a b) : es ≠ [] := by
  cases h <;> simp
theorem Walk.nonempty (h : Walk g es) : es ≠ [] := by
  cases h <;> simp

/-- Overlap at one shared directed segment; that segment is kept once. -/
theorem Labelling.join {xs ys : List (Endpoint g)} {e : Endpoint g}
    (h : Labelling g (xs ++ [e]) a b) (k : Labelling g (e :: ys) b c) :
    Labelling g (xs ++ e :: ys) a c := by
  induction xs generalizing a with
  | nil => cases h with | single _ _ => exact k
  | cons x xs ih =>
    cases xs with
    | nil =>
      cases h with
      | cons ht hs => cases hs with | single _ _ => exact .cons ht k
    | cons y xs =>
      cases h with
      | cons ht hs => exact .cons ht (ih hs)

theorem Walk.join {xs ys : List (Endpoint g)} {e : Endpoint g}
    (h : Walk g (xs ++ [e])) (k : Walk g (e :: ys)) : Walk g (xs ++ e :: ys) := by
  induction xs with
  | nil => exact k
  | cons x xs ih =>
    cases xs with
    | nil => cases h with | cons ht _ => exact .cons ht k
    | cons y xs => cases h with | cons ht hs => exact .cons ht (ih hs)

theorem Forward.join {xs ys : List (Endpoint g)} {e : Endpoint g}
    (h : Forward g (xs ++ [e])) (k : Forward g (e :: ys)) : Forward g (xs ++ e :: ys) := by
  induction xs with
  | nil => exact k
  | cons x xs ih =>
    cases xs with
    | nil =>
      cases h with
      | node n p q ha hl hd _ => exact .node n p q ha hl hd k
      | transparent w d ha hl _ => exact .transparent w d ha hl k
    | cons y xs =>
      cases h with
      | node n p q ha hl hd hs => exact .node n p q ha hl hd (ih hs)
      | transparent w d ha hl hs => exact .transparent w d ha hl (ih hs)

/-- Non-overlapping pieces require an actual AG-labelled seam turn. -/
theorem Labelling.splice {xs ys : List (Endpoint g)} {e f : Endpoint g}
    (h : Labelling g (xs ++ [e]) a b) (k : Labelling g (f :: ys) c d)
    (seam : LabelledTurn g (g.wire e) f b c) :
    Labelling g (xs ++ e :: f :: ys) a d :=
  h.join (.cons seam k)

end

/-- Lambda binding ports may end a path, but are never traversed by an ordinary
proper turn, in either direction. -/
theorem Traversal.no_binding {i : Nat} {p q : Port (.op .lam)} {a b : Context}
    (h : Traversal i (.op .lam) p q a b) : p ≠ lamBind ∧ q ≠ lamBind := by
  cases h with
  | direct h => cases h; exact ⟨(by intro e; cases e),(by intro e; cases e)⟩
  | inverse h => cases h; exact ⟨(by intro e; cases e),(by intro e; cases e)⟩

theorem ForwardPorts.lam_roles {p q : Port (.op .lam)}
    (h : ForwardPorts (.op .lam) p q) : p = .inl () ∧ q = lamBody := h

end Lamping.AG
