import Lamping.Lambda.SelectedFunctionSurvival
import Lamping.Lambda.LambdaOuterAtomSupport

namespace Lamping.Lambda.Marked
open Labelled

/-- A selected old FUNCTION's atom cannot remain as an OUTER letter after
the SAME actual development is normal. No current origin is a premise. -/
theorem RelativeOldHistory.normal_no_selected_function_outer_atom
    {source target oldBody oldArg node : LTerm}
    {F ps : List Path} {marked : Marked} {name position : Path}
    {oldApp : Labelled.Label} {n : Nat}
    (old : RelativeOldHistory F ps (mark F source.erase) marked)
    (labels : Labelled.History ps source target)
    (initial : INIT source)
    (normal : Normal marked)
    (selectedName : name∈F)
    (oldRedex : source.subterm name=
      some (.app oldApp (.lam (Labelled.Label.atom n) oldBody) oldArg))
    (lookup : target.subterm position=some node) :
    Letter.atom n∉node.label.letters := by
  intro outer
  have oldFunction : source.subterm (name++[.fn])=
      some (.lam (Labelled.Label.atom n) oldBody) := by
    simp only [LTerm.subterm_append,oldRedex,Option.bind_some,LTerm.subterm]
  obtain ⟨label,body,equal,_last,trace⟩ :=
    labels.original_lambda_outer_atom_origin initial oldFunction lookup outer
  rw [equal] at lookup
  exact old.normal_no_selected_function_origin labels normal selectedName oldRedex lookup trace

#print axioms RelativeOldHistory.normal_no_selected_function_outer_atom
end Lamping.Lambda.Marked
