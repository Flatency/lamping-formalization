import Lamping.Lamping.LocalSourceFragmentEvaluation

namespace Lamping.AG
open Graph Lambda Lambda.Labelled
section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable {g : Net signature N B W} {root : B}

/-- An arbitrary actual local middle need not be INIT. The ordinary COPY
formula retains both its actual variable lookup and complete ARG block;
history alignment and SOURCE Aux remain the high theorem's work. -/
theorem SourceEdgeSelection.copy_argument_local_formula
    {original middle localMiddle localTarget body argument localCurrent : LTerm}
    {chosen parent : Path} {beta degree : Lambda.Labelled.Label}
    (selection : SourceEdgeSelection original g root)
    (sameMiddle : middle.erase=localMiddle.erase)
    (redex : middle.subterm chosen=some (.app beta (.lam degree body) argument))
    (localStep : StepAt chosen localMiddle localTarget)
    (occurs : ArgumentOccurrence body.erase (parent++[.arg]))
    (localLookup : localTarget.subterm (chosen++(parent++[.arg]))=some localCurrent)
    (edge : BetaEdge g) :
    ∃localBeta localAlpha localBody localArgument variableStamp,
      localMiddle.subterm chosen=some (.app localBeta (.lam localAlpha localBody) localArgument) ∧
      localMiddle.subterm ((chosen++[.fn,.body])++(parent++[.arg]))=
        some (.var variableStamp (binderDepth (parent++[.arg]))) ∧
      selection.evalLabel edge localCurrent.label=
        selection.evalLabel edge variableStamp++
          (edge.reverseRoute++selection.evalLabel edge localArgument.label) := by
  obtain ⟨localBeta,localAlpha,localBody,localArgument,localRedex,_contractum⟩ := localStep.head_lookups
  have heads := congrArg (fun t=>subtermAt t chosen) sameMiddle
  simp only [←LTerm.erase_subterm,redex,localRedex,Option.map_some,LTerm.erase] at heads
  have components := Term.app.inj (Option.some.inj heads)
  have bodySame := Term.lam.inj components.1
  have localOccurs : ArgumentOccurrence localBody.erase (parent++[.arg]) := by
    rw [←bodySame]
    exact occurs
  have atContract : (LTerm.contract localBeta localAlpha localBody localArgument).subterm (parent++[.arg])=
      some localCurrent := by
    have actualLookup := localLookup
    rw [LTerm.subterm_append,localStep.contract_lookup localRedex,Option.bind_some] at actualLookup
    exact actualLookup
  obtain ⟨stamp,oldLookup,labelEq⟩ := LTerm.contract_argument_incoming_label localOccurs atContract
  have nonempty : parent++[Step.arg]≠[] := by simp
  rw [if_neg nonempty] at labelEq
  have localOld : localMiddle.subterm ((chosen++[.fn,.body])++(parent++[.arg]))=
      some (.var stamp (binderDepth (parent++[.arg]))) := by
    rw [List.append_assoc,LTerm.subterm_append,localRedex]
    simpa only [LTerm.subterm,Option.bind_some] using oldLookup
  have under : selection.evalLabel edge localAlpha.under=edge.reverseRoute := by
    simp [SourceEdgeSelection.evalLabel,Label.sourceWord,Label.under,Letter.sourceWord]
  refine ⟨localBeta,localAlpha,localBody,localArgument,stamp,localRedex,localOld,?_⟩
  simp only [labelEq,selection.evalLabel_concat,under]
end

#print axioms SourceEdgeSelection.copy_argument_local_formula
end Lamping.AG
