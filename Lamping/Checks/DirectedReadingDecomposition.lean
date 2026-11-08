import Lamping.Lambda.DirectedReadingDecomposition
import Lamping.Checks.WrappedSuccessfulChains
namespace Lamping.Checks.DirectedReadingDecompositionChecks
open Lambda Lambda.Labelled
abbrev I : Term := WrappedSuccessfulChains.I
abbrev source : LTerm := initLabels (.app (.app I I) I)
abbrev arg : LTerm := .lam (.atom 4) (.var (.atom 5) 0)
abbrev result : LTerm := LTerm.contract (.atom 1) (.atom 2) (.var (.atom 3) 0) arg
abbrev target : LTerm := .app (.atom 0) result (.lam (.atom 6) (.var (.atom 7) 0))
def step : StepAt [.fn] source target := .fn (.root _ _ _ _)
def history : History [[.fn]] source target := .cons step (.nil _)
theorem initial : INIT source := init_is_INIT _
theorem closed : Closed source.erase := by change (0<1 ∧0<1) ∧0<1;decide

def functionOrigin : BetaIncomingReadingOrigin (.var (.atom 3) 0) arg [.fn] [.fn] []
    [] [.fn] [.fn,.fn,.body] := .resultFunction rfl rfl
def contextOrigin : BetaIncomingReadingOrigin (.var (.atom 3) 0) arg [.fn] [.fn] [.fn]
    [.fn,.arg] [.fn,.arg] [.fn,.fn,.body] := .copyLambda (q:=[]) rfl rfl rfl rfl
theorem successful_function : PrerequisiteChain target [] [[.fn]] := .redex_app rfl
theorem successful_context : PrerequisiteChain target [.fn] [[.fn]] := by
  change PrerequisiteChain target ([]++[.fn]) [[]++[.fn]]
  exact .redex_lam rfl

theorem result_function_decomposition : ∃first last marker,
    source.subterm [.fn]=some first ∧source.subterm [.fn,.fn,.body]=some last ∧
    marker.MarksDegree (.atom 2) ∧ExactDirectedReadingFormula source [.fn] (.atom 2) true first last marker result :=
  functionOrigin.directed_label_decomposition step rfl ⟨Or.inl ⟨_,_,_,rfl,rfl⟩,rfl⟩ rfl
theorem copy_context_decomposition : ∃first last marker,
    source.subterm [.fn,.arg]=some first ∧source.subterm [.fn,.fn,.body]=some last ∧
    marker.MarksDegree (.atom 2) ∧ExactDirectedReadingFormula source [.fn] (.atom 2) false first last marker result :=
  contextOrigin.directed_label_decomposition step rfl ⟨Or.inr ⟨_,_,rfl,rfl⟩,rfl⟩ rfl

-- Root overlap retains BOTH separators in the correct reading order.
theorem actual_overlap_words :
    result.label.readLetters true=[.atom 1,.over (.atom 2),.atom 3,.under (.atom 2),.atom 4] ∧
    result.label.readLetters false=[.atom 4,.under (.atom 2),.atom 3,.over (.atom 2),.atom 1] := ⟨rfl,rfl⟩
theorem overlap_not_old_last_alone :
    result.label.readLetters true≠[.atom 1,.over (.atom 2),.atom 3] ∧
    result.label.readLetters false≠[.atom 4,.under (.atom 2),.atom 3] := by decide

abbrev rBody : LTerm := .lam (.atom 3) (.var (.atom 4) 1)
abbrev rSource : LTerm := initLabels (.app (.app (.lam (.lam (.var 1))) I) I)
abbrev rResult : LTerm := LTerm.contract (.atom 1) (.atom 2) rBody (.lam (.atom 5) (.var (.atom 6) 0))
abbrev rTarget : LTerm := .app (.atom 0) rResult (.lam (.atom 7) (.var (.atom 8) 0))
def rStep : StepAt [.fn] rSource rTarget := .fn (.root _ _ _ _)
theorem result_context_decomposition : ∃first last marker,
    rSource.subterm [.fn,.fn,.body]=some first ∧rSource.subterm [.fn]=some last ∧
    marker.MarksDegree (.atom 2) ∧ExactDirectedReadingFormula rSource [.fn] (.atom 2) false first last marker rResult :=
  (BetaIncomingReadingOrigin.resultLambda rfl rfl rfl).directed_label_decomposition
    rStep rfl ⟨Or.inr ⟨_,_,rfl,rfl⟩,rfl⟩ rfl

abbrev cBody : LTerm := .app (.atom 3) (.var (.atom 4) 0) (.var (.atom 5) 0)
abbrev cSource : LTerm := initLabels (.lam (.app (.lam (.app (.var 0) (.var 0))) (.var 0)))
abbrev cResult : LTerm := LTerm.contract (.atom 1) (.atom 2) cBody (.var (.atom 6) 0)
abbrev cTarget : LTerm := .lam (.atom 0) cResult
abbrev cCurrent : LTerm := .var (((Label.atom 4).concat (Label.atom 2).under).concat (.atom 6)) 0
def cStep : StepAt [.body] cSource cTarget := .body (.root _ _ _ _)
def cOrigin : BetaIncomingReadingOrigin cBody (.var (.atom 6) 0) [.body] [.body,.fn] [.body]
    [.body,.fn,.body] [.body,.fn,.body,.fn] [.body,.arg] := .copyFunction (parent:=[]) rfl rfl rfl
theorem copy_function_decomposition : ∃first last marker,
    cSource.subterm [.body,.fn,.body,.fn]=some first ∧cSource.subterm [.body,.arg]=some last ∧
    marker.MarksDegree (.atom 2) ∧ExactDirectedReadingFormula cSource [.body] (.atom 2) true first last marker cCurrent :=
  cOrigin.directed_label_decomposition cStep rfl ⟨Or.inl ⟨_,_,_,rfl,rfl⟩,rfl⟩ rfl

#print axioms BetaIncomingReadingOrigin.directed_label_decomposition
#print axioms initial
#print axioms history
#print axioms successful_function
#print axioms successful_context
#print axioms result_function_decomposition
#print axioms copy_context_decomposition
#print axioms result_context_decomposition
#print axioms copy_function_decomposition
#print axioms actual_overlap_words
#print axioms overlap_not_old_last_alone
end Lamping.Checks.DirectedReadingDecompositionChecks
