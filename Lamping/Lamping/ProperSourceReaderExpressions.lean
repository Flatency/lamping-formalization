import Lamping.Lamping.MarkerExpressionPaths
import Lamping.Lamping.MarkerTransport
import Lamping.Lamping.OrdinaryPrefixRelabelling
namespace Lamping.AG.Marker
open Graph Lambda

namespace LevelExpr
/-- A fixed old level, including constant empty, has no input variable. -/
def literal : Level → LevelExpr
  | .empty => .empty
  | .o a => .o (literal a)
  | .star a => .star (literal a)
  | .pair a b => .pair (literal a) (literal b)
@[simp] theorem eval_literal (level : Level) (input : Nat → Level) :
    (literal level).eval input=level := by
  induction level <;> simp_all [literal,eval]
end LevelExpr

namespace ExprContext
/-- Symbolic family for exactly the permitted source-tail replacements. -/
def sourceTail (a : Context) (m : Nat) : ExprContext where
  get k := if k<m then .literal (a.get k) else .var (k-m)
  cutoff := m
  offset := 0
  tail k bound := by simp only [if_neg (by omega : ¬k<m),Nat.zero_add]
@[simp] theorem eval_sourceTail (a : Context) (m : Nat) (input : Context) :
    (sourceTail a m).eval input=a.replace m input := by
  ext k
  by_cases low : k<m <;> simp [eval,sourceTail,Context.replace,low,LevelExpr.eval]
end ExprContext

section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable {g : Net signature N B W}

/-- Extract one actual turn at its literal ordinal from the supplied trace.
Repeated physical endpoints retain distinct ordinals. -/
theorem ContextTrace.turn_at_ordinal {es cs} (trace : ContextTrace g es cs)
    (j : Nat) (atE : es[j]?=some e) (atF : es[j+1]?=some f)
    (atA : cs[j]?=some a) (atB : cs[j+1]?=some b) :
    LabelledTurn g (g.wire e) f a b := by
  induction trace generalizing j with
  | single x c => cases j <;> simp at atF
  | cons turn tail ih =>
    cases j with
    | zero =>
      simp only [List.getElem?_cons_zero,Option.some.injEq] at atE atA
      simp only [List.getElem?_cons_succ,List.getElem?_cons_zero,Option.some.injEq] at atF atB
      subst e; subst f; subst a; subst b
      exact turn
    | succ j => exact ih j atE atF atA atB

/-- An actual reader in the SAME finite all-input trace tests a constructor
of its precise preceding expression. No initial-variable head is accepted
as an O/Star/Pair/Empty constructor by a total inverse. -/
theorem expression_reader_at_ordinal {es : List (Endpoint g)} {expressions : List ExprContext}
    (traces : ∀ input,ContextTrace g es (expressions.map (fun c => c.eval input)))
    (j : Nat) (node : N) (p q : Port (g.label node).sort)
    (atE : es[j]?=some e) (arrives : g.wire e=.inl ⟨node,p⟩)
    (atF : es[j+1]?=some (.inl ⟨node,q⟩))
    (atExpression : expressions[j]?=some a) :
    ExprInputShape (g.label node).index (g.label node).sort p q a := by
  apply expression_input_shape
  intro input
  have lengthEq := (traces input).length g
  rw [List.length_map] at lengthEq
  have valid : j+1<expressions.length := by
    have : j+1<es.length := List.getElem?_eq_some_iff.mp atF |>.1
    omega
  let b := expressions[j+1]
  have atB : expressions[j+1]?=some b := List.getElem?_eq_getElem valid
  have turn := ContextTrace.turn_at_ordinal (traces input) (a:=a.eval input) (b:=b.eval input) j atE atF
    (by simp only [List.getElem?_map,atExpression,Option.map_some])
    (by simp only [List.getElem?_map,atB,Option.map_some])
  rw [arrives] at turn
  cases turn with
  | node node p q actual => exact ⟨_,actual⟩

/-- Evaluate a symbolic occurrence at the original reference tail. The
actual prefix assignment, rather than endpoint equality, identifies its
context. This also exposes every permitted changed prefix. -/
theorem source_expression_prefix {es : List (Endpoint g)} {expressions : List ExprContext}
    (traces : ∀ input,ContextTrace g es (expressions.map (fun c => c.eval input)))
    (first : expressions.head?=some (ExprContext.sourceTail a m))
    (j : Nat) (point : expressions[j]?=some expression)
    (reference : Labelling g (es.take (j+1)) a middle) :
    expression.eval (a.tail m)=middle ∧
    ∀ input,Labelling g (es.take (j+1)) (a.replace m input) (expression.eval input) := by
  have prefixes : ∀ input,Labelling g (es.take (j+1)) (a.replace m input) (expression.eval input) := by
    intro input
    apply (traces input).prefix_labels j
      (by simp only [List.getElem?_map,point,Option.map_some])
    simp only [List.head?_map,first,Option.map_some,ExprContext.eval_sourceTail]
  refine ⟨?_,prefixes⟩
  have original := prefixes (a.tail m)
  rw [Context.replace_tail] at original
  exact original.output_unique reference
/-- Full ordinary I supplies this symbolic trace at every proper source,
including paths in components with no root access. The only quantified
input change is replace m, with the old low shell held fixed. -/
theorem Independence.source_expression_trace {root : B} (independence : Independence g root)
    {es e f sr tr m n a b}
    (head : es.head?=some e) (finish : es.getLast?=some (g.wire f))
    (source : AtProperRole g root e sr m) (outgoing : sr.outgoing)
    (target : AtProperRole g root f tr n) (incoming : tr.incoming)
    (forward : Forward g es) (labels : Labelling g es a b) :
    ∃ expressions : List ExprContext,
      expressions.head?=some (ExprContext.sourceTail a m) ∧
      ∀ input,ContextTrace g es (expressions.map (fun c => c.eval input)) := by
  have allInputs := (independence es e f sr tr m n a b head finish source outgoing target incoming forward labels).1
  apply Labelling.expression_trace
  simpa only [ExprContext.eval_sourceTail] using allInputs
end
end Lamping.AG.Marker



