import Lamping.Lamping.IncidenceChaseAlgebra
import Lamping.Checks.CreatedReadingIncidenceExpansion

namespace Lamping.Checks.IncidenceChaseAlgebraChecks
open Lambda Lambda.Labelled SyntaxIncidence
open CreatedReadingIncidenceExpansionChecks
open DirectedReadingDecompositionChecks

theorem repeated_five_roundtrip :
    IncidenceChase source (some Overlap.oldApp)
      ([[.fn],[.fn,.fn],[.fn,.fn,.body],[.fn,.fn],[.fn,.arg]] ++
       [[.fn,.arg],[.fn,.fn],[.fn,.fn,.body],[.fn,.fn],[.fn]])
      ([true,true,true,false,true] ++ [false,true,false,false,false])
      (some Overlap.oldApp) :=
  Overlap.exact_forward_five.append Overlap.exact_forward_five.reverse

theorem repeated_edge_positions :
    (Overlap.exact_forward_five.edgePosition [.fn,.fn] (by simp)).val=[.fn,.fn] ∧
    (Overlap.exact_forward_five.edgePosition [.fn,.fn,.body] (by simp)).val=[.fn,.fn,.body] :=
  ⟨rfl,rfl⟩

/-- The real external root edge may be reversed; no target at none is added. -/
def boundary : IncidenceChase source none [[]] [true] (some Overlap.oldApp) :=
  .forward rfl (show Target source [] (some Overlap.oldApp) from Or.inl rfl) .nil

theorem boundary_reverse : IncidenceChase source (some Overlap.oldApp) [[]] [false] none :=
  boundary.reverse

abbrev zeroTerm : LTerm := initLabels (.app I I)
theorem zeroClosed : Closed zeroTerm.erase := by change (0<1) ∧ (0<1); decide
def binderReading : PrerequisiteReading zeroTerm [.fn,.body] [[.fn]] [false] :=
  .var (parent:=[.fn]) (rest:=[]) rfl rfl rfl rfl (.redex_lam (p:=[]) rfl)
def lambdaReading : PrerequisiteReading zeroTerm [.fn] [[.fn]] [false] := .redex_lam (p:=[]) rfl

theorem binder_zero_extra_edge :
    ∃ finish, IncidenceChase zeroTerm
      (SyntaxIncidence.target zeroTerm zeroClosed ⟨[.fn,.body],by decide⟩)
      [[.fn]] [false] finish :=
  binderReading.incidence_chase_at_position zeroClosed ⟨[.fn,.body],by decide⟩

theorem binder_and_lambda_same_start :
    SyntaxIncidence.target zeroTerm zeroClosed ⟨[.fn,.body],by decide⟩=
      SyntaxIncidence.target zeroTerm zeroClosed ⟨[.fn],by decide⟩ := by
  apply SyntaxIncidence.Target.unique
    (SyntaxIncidence.target_spec zeroTerm zeroClosed ⟨[.fn,.body],by decide⟩)
  have actual := SyntaxIncidence.target_spec zeroTerm zeroClosed ⟨[.fn],by decide⟩
  have known : Target zeroTerm [.fn] (some ⟨[.fn],Or.inr ⟨_,_,rfl⟩⟩) := Or.inl rfl
  have equal := SyntaxIncidence.Target.unique actual known
  rw [equal]
  exact Or.inr ⟨_,0,_,_,[],rfl,rfl,rfl,rfl⟩

#print axioms repeated_five_roundtrip
#print axioms repeated_edge_positions
#print axioms boundary_reverse
#print axioms binder_zero_extra_edge
#print axioms binder_and_lambda_same_start
end Lamping.Checks.IncidenceChaseAlgebraChecks
