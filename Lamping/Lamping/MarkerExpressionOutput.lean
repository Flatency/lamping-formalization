import Lamping.Lamping.MarkerExpressionTraversal
namespace Lamping.AG.Marker
open Graph

private theorem expose_one (a : Context) (i : Nat) :
    a.replace i ((a.tail (i+1)).cons (a.get i))=a := by
  ext k
  by_cases low : k<i
  · exact Context.replace_low _ _ low
  · rw [Context.replace_high _ _ (by omega)]
    cases h : k-i with
    | zero =>
      have same : k=i := by omega
      subst k
      rfl
    | succ d => change a.get (i+1+d)=a.get k; congr 1; omega

private theorem expose_two (a : Context) (i : Nat) :
    a.replace i (((a.tail (i+2)).cons (a.get (i+1))).cons (a.get i))=a := by
  ext k
  by_cases low : k<i
  · exact Context.replace_low _ _ low
  · rw [Context.replace_high _ _ (by omega)]
    cases h : k-i with
    | zero =>
      have same : k=i := by omega
      subst k
      rfl
    | succ d =>
      cases d with
      | zero => change a.get (i+1)=a.get k; congr 1; omega
      | succ d => change a.get (i+2+d)=a.get k; congr 1; omega

/-- Construct the symbolic result by the actual directed primitive rule.
Inverse reads are justified by the expression-level shape already reflected
from all real inputs; no output or whole-path labelling is a field. -/
theorem expression_output {i kind p q a0 b0} (rule : Traversal i kind p q a0 b0)
    (a : ExprContext) (shape : ExprInputShape i kind p q a) :
    ∃ b : ExprContext, ∀ input : Context, Traversal i kind p q (a.eval input) (b.eval input) := by
  cases rule with
  | direct passage =>
    cases passage with
    | fanO old tail x =>
      refine ⟨a.replace i ((a.drop (i+1)).cons (.o (a.get i))),?_⟩
      intro input
      simp only [ExprContext.eval_replace,ExprContext.eval_cons,ExprContext.eval_drop,LevelExpr.eval]
      have step := Traversal.direct (Passage.fanO (i:=i) (a.eval input) ((a.eval input).tail (i+1)) ((a.eval input).get i))
      rw [expose_one] at step
      exact step
    | fanStar old tail x =>
      refine ⟨a.replace i ((a.drop (i+1)).cons (.star (a.get i))),?_⟩
      intro input
      simp only [ExprContext.eval_replace,ExprContext.eval_cons,ExprContext.eval_drop,LevelExpr.eval]
      have step := Traversal.direct (Passage.fanStar (i:=i) (a.eval input) ((a.eval input).tail (i+1)) ((a.eval input).get i))
      rw [expose_one] at step
      exact step
    | cro old tail =>
      refine ⟨a.replace i ((a.drop i).cons .empty),?_⟩
      intro input
      simp only [ExprContext.eval_replace,ExprContext.eval_cons,ExprContext.eval_drop,LevelExpr.eval]
      have step := Traversal.direct (Passage.cro (i:=i) (a.eval input) ((a.eval input).tail i))
      rw [Context.replace_tail] at step
      exact step
    | bra old tail x y =>
      refine ⟨a.replace i ((a.drop (i+2)).cons (.pair (a.get (i+1)) (a.get i))),?_⟩
      intro input
      simp only [ExprContext.eval_replace,ExprContext.eval_cons,ExprContext.eval_drop,LevelExpr.eval]
      have step := Traversal.direct (Passage.bra (i:=i) (a.eval input) ((a.eval input).tail (i+2))
        ((a.eval input).get (i+1)) ((a.eval input).get i))
      rw [expose_two] at step
      exact step
    | appFun old => exact ⟨a,fun input => .direct (.appFun _)⟩
    | appArg old => exact ⟨a,fun input => .direct (.appArg _)⟩
    | lamBody old => exact ⟨a,fun input => .direct (.lamBody _)⟩
  | inverse passage =>
    cases passage with
    | fanO old tail x =>
      obtain ⟨child,same⟩ := shape
      refine ⟨a.replace i ((a.drop (i+1)).cons child),?_⟩
      intro input
      simp only [ExprContext.eval_replace,ExprContext.eval_cons,ExprContext.eval_drop]
      have level : (a.eval input).get i=.o (child.eval input.get) := congrArg (LevelExpr.eval input.get) same
      have step := Traversal.inverse (Passage.fanO (i:=i) (a.eval input) ((a.eval input).tail (i+1)) (child.eval input.get))
      rw [←level,expose_one] at step
      exact step
    | fanStar old tail x =>
      obtain ⟨child,same⟩ := shape
      refine ⟨a.replace i ((a.drop (i+1)).cons child),?_⟩
      intro input
      simp only [ExprContext.eval_replace,ExprContext.eval_cons,ExprContext.eval_drop]
      have level : (a.eval input).get i=.star (child.eval input.get) := congrArg (LevelExpr.eval input.get) same
      have step := Traversal.inverse (Passage.fanStar (i:=i) (a.eval input) ((a.eval input).tail (i+1)) (child.eval input.get))
      rw [←level,expose_one] at step
      exact step
    | cro old tail =>
      refine ⟨a.replace i (a.drop (i+1)),?_⟩
      intro input
      simp only [ExprContext.eval_replace,ExprContext.eval_drop]
      have level : (a.eval input).get i=.empty := congrArg (LevelExpr.eval input.get) shape
      have step := Traversal.inverse (Passage.cro (i:=i) (a.eval input) ((a.eval input).tail (i+1)))
      rw [←level,expose_one] at step
      exact step
    | bra old tail x y =>
      obtain ⟨left,right,same⟩ := shape
      refine ⟨a.replace i (((a.drop (i+1)).cons left).cons right),?_⟩
      intro input
      simp only [ExprContext.eval_replace,ExprContext.eval_cons,ExprContext.eval_drop]
      have level : (a.eval input).get i=.pair (left.eval input.get) (right.eval input.get) := congrArg (LevelExpr.eval input.get) same
      have step := Traversal.inverse (Passage.bra (i:=i) (a.eval input) ((a.eval input).tail (i+1))
        (left.eval input.get) (right.eval input.get))
      rw [←level,expose_one] at step
      exact step
    | appFun old => exact ⟨a,fun input => .inverse (.appFun _)⟩
    | appArg old => exact ⟨a,fun input => .inverse (.appArg _)⟩
    | lamBody old => exact ⟨a,fun input => .inverse (.lamBody _)⟩

theorem total_expression_output (i : Nat) (kind : Kind) (p q : Port kind) (a : ExprContext)
    (total : ∀ input : Context, ∃ output, Traversal i kind p q (a.eval input) output) :
    ∃ b : ExprContext, ∀ input : Context, Traversal i kind p q (a.eval input) (b.eval input) := by
  obtain ⟨output,rule⟩ := total Context.empty
  exact expression_output rule a (expression_input_shape i kind p q a total)
end Lamping.AG.Marker
