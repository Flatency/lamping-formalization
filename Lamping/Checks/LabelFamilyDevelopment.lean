import Lamping.Lambda.LabelFamilyDevelopment
namespace Lamping.Checks.LabelFamilyDevelopment
open Lambda Lambda.Labelled

private abbrev identity : Term := .lam (.var 0)
private abbrev bare := Term.app (.lam (.app (.var 0) (.var 0))) (.app identity identity)
private abbrev original := initLabels bare
private abbrev oldBody : LTerm := .app (.atom 2) (.var (.atom 3) 0) (.var (.atom 4) 0)
private abbrev oldArgument : LTerm := .app (.atom 5) (.lam (.atom 6) (.var (.atom 7) 0))
  (.lam (.atom 8) (.var (.atom 9) 0))
private abbrev source := LTerm.contract (.atom 0) (.atom 1) oldBody oldArgument
private def outer : StepAt [] original source := .root _ _ _ _
private abbrev outerStep := singleContraction outer.betaAt
private abbrev prior := ParallelHistory.single outerStep
private def priorLabels : History prior.derivation.paths original source := .cons outer (.nil _)
private theorem priorComplete : CompleteDerivation prior := by
  apply CompleteDerivation.step (.nil _)
  let representative : RedexOcc original.erase := ⟨[],outer.betaAt.redex⟩
  refine ⟨?_,representative,List.mem_singleton_self _,?_⟩
  · intro path member
    have equal : path=[] := List.mem_singleton.mp member
    subst path;exact outer.betaAt.redex
  · intro candidate
    rw [initial_families_injective]
    exact ⟨fun selected=>Subtype.ext (List.mem_singleton.mp selected).symm,
      fun equal=>by rw [←equal];exact List.mem_singleton_self _⟩

private abbrev leftLabel := (Label.atom 3).concat ((Label.atom 1).under.concat (.atom 5))
private abbrev rightLabel := (Label.atom 4).concat ((Label.atom 1).under.concat (.atom 5))
private abbrev rootLabel := ((Label.atom 0).concat (Label.atom 1).over).concat (.atom 2)
private abbrev leftResult := LTerm.contract leftLabel (.atom 6) (.var (.atom 7) 0)
  (.lam (.atom 8) (.var (.atom 9) 0))
private abbrev rightResult := LTerm.contract rightLabel (.atom 6) (.var (.atom 7) 0)
  (.lam (.atom 8) (.var (.atom 9) 0))
private abbrev rightCopy := oldArgument.prepend ((Label.atom 4).concat (Label.atom 1).under)
private abbrev middle : LTerm := .app rootLabel leftResult rightCopy
private abbrev target : LTerm := .app rootLabel leftResult rightResult
private abbrev selection : List Path := [[.fn],[.arg]]
private def first : StepAt [.fn] source middle := .fn (.root _ _ _ _)
private def second : StepAt [.arg] middle target := .arg (.root _ _ _ _)
private abbrev markedTarget : Marked := .app [] (.lam (.var 0)) (.lam (.var 0))
private def step : ParallelStep selection source.erase target.erase := by
  refine ⟨selection,markedTarget,(Marked.completeOld_iff _ _).mpr ⟨?_,?goal⟩,rfl⟩
  · change Marked.RelativeHistory selection
      (.app [] (.red [[.fn]] (.var 0) (.lam (.var 0))) (.red [[.arg]] (.var 0) (.lam (.var 0)))) markedTarget
    exact .cons (.appL (.root _ _ _)) (.cons (.appR (.root _ _ _)) (.nil _))
  case goal => exact ⟨True.intro,True.intro⟩
private def labels : History step.paths source target := .cons first (.cons second (.nil _))
private def representative : RedexOcc source.erase := ⟨[.fn],first.betaAt.redex⟩
private theorem every_redex (candidate : RedexOcc source.erase) : candidate.val∈selection := by
  have all : redexPositions source.erase=selection := by decide
  rw [←all]
  exact (mem_redexPositions _ _).mpr candidate.property
private theorem selected (path : Path) (member : path∈selection) : source.degreeAt path=some (.atom 6) := by
  rcases List.mem_cons.mp member with rfl | rest
  · rfl
  · have equal : path=[.arg] := List.mem_singleton.mp rest
    subst path;rfl
private theorem whole : CompleteFamilyStep prior step := by
  refine ⟨?_,representative,List.mem_cons_self,?_⟩
  · intro path member
    have all : redexPositions source.erase=selection := by decide
    exact (mem_redexPositions _ _).mp (all ▸ member)
  · intro candidate
    refine ⟨fun _=>?_,fun _=>every_redex candidate⟩
    apply (family_iff_degree original (init_is_INIT bare)
      (⟨source.erase,prior,representative⟩ : RedexWithHistory original.erase)
      (⟨source.erase,prior,candidate⟩ : RedexWithHistory original.erase)).mpr
    rw [degreeAlong_witness priorLabels,degreeAlong_witness priorLabels]
    exact (selected _ List.mem_cons_self).trans (selected _ (every_redex candidate)).symm

/-- The same original INIT supplies the actual nonempty prefix, and both
duplicated redexes form one historical family. The final labels are compared
against this non-INIT current source, not a freshly relabelled copy of it. -/
theorem real_global_family_classification :
    CompleteDerivation prior ∧CompleteFamilyStep prior step ∧step.paths.length=2 ∧
    ((Label.atom 9)∈source.labels ↔(Label.atom 9).OuterBarsSafe (fun payload=>payload≠Label.atom 6)) ∧
    rightResult.label∉source.labels := by
  refine ⟨priorComplete,whole,rfl,?_,?_⟩
  · exact whole.label_mem_iff_marker_free (init_is_INIT bare) priorComplete priorLabels labels
      representative List.mem_cons_self rfl (current := .var (.atom 9) 0) (edge := [.arg,.body]) rfl
  · intro member
    have safe := (whole.label_mem_iff_marker_free (init_is_INIT bare) priorComplete priorLabels labels
      representative List.mem_cons_self rfl (current := rightResult) (edge := [.arg]) rfl).mp member
    exact second.created_label_not_safe rfl (edge := [.arg]) rfl (Or.inl rfl) safe

end Lamping.Checks.LabelFamilyDevelopment
#print axioms Lamping.Lambda.CompleteFamilyStep.uniform_degree
#print axioms Lamping.Lambda.CompleteFamilyStep.label_mem_iff_marker_free
#print axioms Lamping.Checks.LabelFamilyDevelopment.real_global_family_classification
