import Lamping.Lamping.MarkerExpressionOutput
import Lamping.Lamping.GlobalPathInvariants
namespace Lamping.AG.Marker
open Graph
section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable {g : Net signature N B W}

private theorem node_rule {n : N} {p q : Port (g.label n).sort} {a b : Context}
    (rule : LabelledTurn g (.inl ⟨n,p⟩) (.inl ⟨n,q⟩) a b) :
    Traversal (g.label n).index (g.label n).sort p q a b := by
  cases rule with
  | node node p q passage => exact passage

theorem LabelledTurn.total_expression_output {x y : Endpoint g} (a : ExprContext)
    (total : ∀ input : Context, ∃ output, LabelledTurn g x y (a.eval input) output) :
    ∃ b : ExprContext, ∀ input : Context, LabelledTurn g x y (a.eval input) (b.eval input) := by
  obtain ⟨output,rule⟩ := total Context.empty
  cases rule with
  | node node p q passage =>
    have traversals : ∀ input : Context, ∃ output,
        Traversal (g.label node).index (g.label node).sort p q (a.eval input) output := by
      intro input
      obtain ⟨output,rule⟩ := total input
      exact ⟨output,node_rule rule⟩
    obtain ⟨b,rules⟩ := Marker.total_expression_output _ _ p q a traversals
    exact ⟨b,fun input => .node node p q (rules input)⟩
  | transparent w d context => exact ⟨a,fun input => .transparent w d _⟩

/-- A real total-input finite ordinary path induces a finite symbolic trace.
Each trace step is constructed by primitive output reflection above; the
remaining actual tail is aligned by local output uniqueness. No symbolic
execution or path soundness is assumed as an input certificate. -/
theorem Labelling.expression_trace (es : List (Endpoint g)) (a : ExprContext)
    (total : ∀ input : Context, ∃ output, Labelling g es (a.eval input) output) :
    ∃ expressions : List ExprContext, expressions.head?=some a ∧
      ∀ input : Context, ContextTrace g es (expressions.map (fun c => c.eval input)) := by
  induction es generalizing a with
  | nil => obtain ⟨output,labels⟩ := total Context.empty; cases labels
  | cons e tail ih =>
    cases tail with
    | nil => exact ⟨[a],rfl,fun input => .single e _⟩
    | cons f tail =>
      have turns : ∀ input : Context, ∃ middle, LabelledTurn g (g.wire e) f (a.eval input) middle := by
        intro input
        obtain ⟨output,labels⟩ := total input
        cases labels with
        | cons turn after => exact ⟨_,turn⟩
      obtain ⟨b,turns⟩ := LabelledTurn.total_expression_output a turns
      have remaining : ∀ input : Context, ∃ output, Labelling g (f::tail) (b.eval input) output := by
        intro input
        obtain ⟨output,labels⟩ := total input
        cases labels with
        | cons turn after =>
          have same := turn.output_unique (turns input)
          rw [same] at after
          exact ⟨output,after⟩
      obtain ⟨expressions,head,traces⟩ := ih b remaining
      cases expressions with
      | nil => cases head
      | cons first expressions =>
        have same : first=b := Option.some.inj head
        subst first
        exact ⟨a::b::expressions,rfl,fun input => .cons (turns input) (traces input)⟩
end
end Lamping.AG.Marker
