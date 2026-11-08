import Lamping.Lambda.SyntaxIncidence
import Lamping.Checks.Phase6Projection

namespace Lamping.Checks.SyntaxIncidence
open Lambda Lambda.Labelled
namespace I
open Lambda.Labelled.SyntaxIncidence

abbrev term := Phase6Projection.repeatedSource
def rootVertex : Vertex term := some ⟨[],Or.inl ⟨_,_,_,rfl⟩⟩
def leftLambda : Vertex term := some ⟨[.fn],Or.inr ⟨_,_,rfl⟩⟩
def rightLambda : Vertex term := some ⟨[.arg],Or.inr ⟨_,_,rfl⟩⟩
def argumentEdge : Edge term := ⟨[.arg],by decide⟩
def leftVariable : Edge term := ⟨[.fn,.body],by decide⟩
def rightVariable : Edge term := ⟨[.arg,.body],by decide⟩
theorem closed : Closed term.erase := ⟨Nat.zero_lt_succ 0,Nat.zero_lt_succ 0⟩

theorem argument_source : source term argumentEdge=rootVertex :=
  source_eq_of_spec term argumentEdge ⟨.arg,_,_,rfl,rfl,.arg⟩
theorem argument_target : target term closed argumentEdge=rightLambda :=
  target_eq_of_spec term closed argumentEdge (Or.inl rfl)
theorem left_lexical_target : target term closed leftVariable=leftLambda :=
  target_eq_of_spec term closed leftVariable
    (Or.inr ⟨_,0,_,_,[],rfl,rfl,rfl,rfl⟩)
theorem right_lexical_target : target term closed rightVariable=rightLambda :=
  target_eq_of_spec term closed rightVariable
    (Or.inr ⟨_,0,_,_,[],rfl,rfl,rfl,rfl⟩)

/-- Equal source labels do not identify actual lexical vertices. -/
theorem repeated_labels_distinct_binders :
    label term leftVariable=label term rightVariable ∧
      target term closed leftVariable≠target term closed rightVariable := by
  refine ⟨rfl,?_⟩
  rw [left_lexical_target,right_lexical_target]
  intro equal
  have paths := congrArg (fun vertex => vertex.map Subtype.val) equal
  cases paths
end I

namespace Outer
open Lambda.Labelled.SyntaxIncidence
def term : LTerm := .lam (.atom 9) (.lam (.atom 9) (.var (.atom 9) 1))
def variableEdge : Edge term := ⟨[.body,.body],by decide⟩
def outerLambda : Vertex term := some ⟨[],Or.inr ⟨_,_,rfl⟩⟩
def innerLambda : Vertex term := some ⟨[.body],Or.inr ⟨_,_,rfl⟩⟩
theorem closed : Closed term.erase := by change 1<2; decide

/-- The variable source is the inner lambda while its target is the outer
lambda; repeated labels cannot replace the actual de Bruijn occurrence. -/
theorem variable_source : source term variableEdge=innerLambda :=
  source_eq_of_spec term variableEdge ⟨.body,_,_,rfl,rfl,.body⟩
theorem variable_target : target term closed variableEdge=outerLambda :=
  target_eq_of_spec term closed variableEdge
    (Or.inr ⟨_,1,_,_,[.body],rfl,rfl,rfl,rfl⟩)

theorem root_source_is_external : source term ⟨[],by decide⟩=none :=
  source_eq_of_spec term _ rfl
end Outer

#print axioms Lambda.Labelled.SourceSubterm.last_departure
#print axioms Lambda.Labelled.SyntaxIncidence.Source.unique
#print axioms Lambda.Labelled.SyntaxIncidence.Target.unique
#print axioms I.repeated_labels_distinct_binders
#print axioms Outer.variable_target
end Lamping.Checks.SyntaxIncidence
