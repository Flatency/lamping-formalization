import Lamping.Lamping.LocalSourceFragmentEvaluation
import Lamping.Lamping.PairedMarkerLeafGeometry

namespace Lamping.AG
open Graph Lambda Lambda.Labelled
section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable {g : Net signature N B W} {root : B}
variable {source localTarget body argument : LTerm} {chosen parent oldPosition : Path}
variable {beta degree : Lambda.Labelled.Label}

private theorem append_singleton_inj {p q : Path} {s u : Step}
    (same : p++[s]=q++[u]) : p=q ∧s=u := by
  have reversed := congrArg List.reverse same
  simp only [List.reverse_append,List.reverse_cons,List.reverse_nil,List.nil_append,List.cons_append] at reversed
  have parts := List.cons.inj reversed
  exact ⟨by simpa only [List.reverse_reverse] using congrArg List.reverse parts.2,parts.1⟩

private theorem argument_parent_of_role {current term : LTerm} {p : Path}
    (lookup : current.subterm p=some term) (role : SourceDeparture term .arg ctx) :
    ∃stamp fn arg,current.subterm p=some (.app stamp fn arg) ∧
      SourceDeparture (.app stamp fn arg) .arg ctx := by
  cases role
  exact ⟨_,_,_,lookup,.arg⟩

/-- The literal ARG child itself determines its actual APP parent and
departure. No caller supplies an endpoint or incoming-role profile. -/
theorem OccurrenceFragment.argument_parent_departure
    {current : LTerm} {p : Path}
    (child : OccurrenceFragment current g root (p++[.arg])) :
    ∃stamp fn arg,current.subterm p=some (.app stamp fn arg) ∧
      SourceDeparture (.app stamp fn arg) .arg
        (sourceEdge child.environment child.context child.term).fromPort := by
  rcases child.occurrence.last_departure with ⟨empty,_external⟩|⟨parent,step,term,split,lookup,role⟩
  · simp at empty
  · obtain ⟨parents,steps⟩ := append_singleton_inj split
    subst parent
    subst step
    obtain ⟨stamp,fn,arg,parentLookup,departure⟩ := argument_parent_of_role lookup role
    refine ⟨stamp,fn,arg,parentLookup,?_⟩
    have fromEq : (sourceEdge child.environment child.context child.term).fromPort=child.context := by
      cases child.term <;> rfl
    rw [fromEq]
    exact departure

/-- At the FIRST relative event the local middle is the actual SOURCE's
INIT annotation. The complete normal COPY block retains the actual ARG.
The old fragment is aligned by its literal coordinate, never its label. -/
theorem SourceEdgeSelection.first_copy_argument_evaluation
    (selection : SourceEdgeSelection (initLabels source.erase) g root)
    (matching : Matches g root source.erase)
    (redex : source.subterm chosen=some (.app beta (.lam degree body) argument))
    (localStep : StepAt chosen (initLabels source.erase) localTarget)
    (occurs : ArgumentOccurrence body.erase (parent++[.arg]))
    (oldPath : oldPosition=(chosen++[.fn,.body])++(parent++[.arg]))
    (oldFragment : OccurrenceFragment source g root oldPosition)
    (localLookup : localTarget.subterm (chosen++(parent++[.arg]))=some localCurrent)
    (edge : BetaEdge g) :
    ∃localBeta localAlpha localBody localArgument,
      (initLabels source.erase).subterm chosen=some (.app localBeta (.lam localAlpha localBody) localArgument) ∧
      selection.evalLabel edge localCurrent.label=
        oldFragment.fragment.segments++(edge.reverseRoute++selection.evalLabel edge localArgument.label) := by
  obtain ⟨localBeta,localAlpha,localBody,localArgument,localRedex,_contractum⟩ := localStep.head_lookups
  have same : source.erase=(initLabels source.erase).erase := (erase_initLabels source.erase).symm
  have heads := congrArg (fun t=>subtermAt t chosen) same
  simp only [←LTerm.erase_subterm,redex,localRedex,Option.map_some,LTerm.erase] at heads
  have components := Term.app.inj (Option.some.inj heads)
  have bodySame := Term.lam.inj components.1
  have localOccurs : ArgumentOccurrence localBody.erase (parent++[.arg]) := by
    rw [←bodySame];exact occurs
  have atContract : (LTerm.contract localBeta localAlpha localBody localArgument).subterm (parent++[.arg])=
      some localCurrent := by
    have actualLookup := localLookup
    rw [LTerm.subterm_append,localStep.contract_lookup localRedex,Option.bind_some] at actualLookup
    exact actualLookup
  obtain ⟨stamp,oldLookup,labelEq⟩ := LTerm.contract_argument_incoming_label localOccurs atContract
  have nonempty : parent++[Step.arg]≠[] := by simp
  rw [if_neg nonempty] at labelEq
  have localOld : (initLabels source.erase).subterm oldPosition=some (.var stamp (binderDepth (parent++[.arg]))) := by
    rw [oldPath,List.append_assoc,LTerm.subterm_append,localRedex]
    simpa only [LTerm.subterm,Option.bind_some] using oldLookup
  obtain ⟨env,ctx,occurrence⟩ := SourceSubterm.of_lookup (initLabels source.erase) localOld [] .external
  have localMatches : Matches g root (initLabels source.erase).erase := by
    simpa only [erase_initLabels] using matching
  have evaluation := selection.evalLabel_occurrence_segments (init_is_INIT source.erase)
    localMatches matching occurrence oldFragment edge
  have under : selection.evalLabel edge localAlpha.under=edge.reverseRoute := by
    simp [SourceEdgeSelection.evalLabel,Label.sourceWord,Label.under,Letter.sourceWord]
  refine ⟨localBeta,localAlpha,localBody,localArgument,localRedex,?_⟩
  simpa only [labelEq,selection.evalLabel_concat,under] using
    congrArg (fun xs=>xs++(edge.reverseRoute++selection.evalLabel edge localArgument.label)) evaluation

/-- Algebra after a genuine SOURCE Aux application. The complete physical
high theorem must derive pieces internally; it is not an input invariant. -/
theorem SourceEdgeSelection.first_copy_argument_evaluations_eq
    {leftParent rightParent leftOld rightOld : Path}
    (selection : SourceEdgeSelection (initLabels source.erase) g root)
    (matching : Matches g root source.erase)
    (redex : source.subterm chosen=some (.app beta (.lam degree body) argument))
    (localStep : StepAt chosen (initLabels source.erase) localTarget)
    (leftOccurs : ArgumentOccurrence body.erase (leftParent++[.arg]))
    (rightOccurs : ArgumentOccurrence body.erase (rightParent++[.arg]))
    (leftPath : leftOld=(chosen++[.fn,.body])++(leftParent++[.arg]))
    (rightPath : rightOld=(chosen++[.fn,.body])++(rightParent++[.arg]))
    (leftFragment : OccurrenceFragment source g root leftOld)
    (rightFragment : OccurrenceFragment source g root rightOld)
    (leftLookup : localTarget.subterm (chosen++(leftParent++[.arg]))=some leftCurrent)
    (rightLookup : localTarget.subterm (chosen++(rightParent++[.arg]))=some rightCurrent)
    (edge : BetaEdge g)
    (pieces : leftFragment.fragment.segments=rightFragment.fragment.segments) :
    selection.evalLabel edge leftCurrent.label=selection.evalLabel edge rightCurrent.label := by
  obtain ⟨lb,la,lbody,larg,lredex,leval⟩ := selection.first_copy_argument_evaluation matching redex localStep
    leftOccurs leftPath leftFragment leftLookup edge
  obtain ⟨rb,ra,rbody,rarg,rredex,reval⟩ := selection.first_copy_argument_evaluation matching redex localStep
    rightOccurs rightPath rightFragment rightLookup edge
  have components := LTerm.app.inj (Option.some.inj (lredex.symm.trans rredex))
  rw [leval,reval,pieces,components.2.2]
end

#print axioms SourceEdgeSelection.first_copy_argument_evaluation
#print axioms SourceEdgeSelection.first_copy_argument_evaluations_eq
#print axioms OccurrenceFragment.argument_parent_departure
end Lamping.AG
