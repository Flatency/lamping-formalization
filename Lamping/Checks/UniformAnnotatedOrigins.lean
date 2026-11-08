import Lamping.Lambda.UniformAnnotatedOrigins
namespace Lamping.Checks.UniformAnnotatedOrigins
open Lambda Lambda.Labelled
private abbrev a := Label.atom 7
private abbrev identity : LTerm := .lam a (.var a 0)
private abbrev argument : LTerm := .app a (.var a 0) identity
private abbrev inner : LTerm := .app a (.lam a (.var a 0)) argument
private abbrev sibling : LTerm := .app a identity identity
private abbrev insideResult := LTerm.contract a a (.var a 0) argument
private abbrev siblingResult := LTerm.contract a a (.var a 0) identity
private abbrev source : LTerm := .app a (.lam a inner) sibling
private abbrev middle : LTerm := .app a (.lam a insideResult) sibling
private abbrev target : LTerm := .app a (.lam a insideResult) siblingResult
private def first : StepAt [.fn,.body] source middle := .fn (.body (.root _ _ _ _))
private def second : StepAt [.arg] middle target := .arg (.root _ _ _ _)
private abbrev selection : List Path := [[.fn,.body],[.arg]]
private abbrev markedTarget : Marked := .app [[]] (.lam (.app [] (.var 0) (.lam (.var 0)))) (.lam (.var 0))
private def step : ParallelStep selection source.erase target.erase := by
  refine ⟨selection,markedTarget,(Marked.completeOld_iff _ _).mpr ⟨?_,?goal⟩,rfl⟩
  · change Marked.RelativeHistory selection
      (.app [[]] (.lam (.red [[.fn,.body]] (.var 0) (.app [] (.var 0) (.lam (.var 0)))))
        (.red [[.arg]] (.var 0) (.lam (.var 0)))) markedTarget
    exact .cons (.appL (.lam (.root _ _ _))) (.cons (.appR (.root _ _ _)) (.nil _))
  case goal => exact ⟨⟨True.intro,True.intro⟩,True.intro⟩
private def labels : History step.paths source target := .cons first (.cons second (.nil _))
private theorem selected (path : Path) (member : path∈selection) : source.degreeAt path=some a := by
  rcases List.mem_cons.mp member with rfl | rest
  · rfl
  · have equal := List.mem_singleton.mp rest
    subst path;rfl
private abbrev localArgument : LTerm := .app (.atom 5) (.var (.atom 6) 0) (.lam (.atom 7) (.var (.atom 8) 0))
private abbrev localSibling : LTerm := .app (.atom 9)
  (.lam (.atom 10) (.var (.atom 11) 0)) (.lam (.atom 12) (.var (.atom 13) 0))
private abbrev localResult := LTerm.contract (.atom 2) (.atom 3) (.var (.atom 4) 0) localArgument
private abbrev otherSource := initLabels source.erase
private abbrev otherMiddle : LTerm := .app (.atom 0) (.lam (.atom 1) localResult) localSibling
private abbrev otherTarget : LTerm := .app (.atom 0) (.lam (.atom 1) localResult)
  (LTerm.contract (.atom 9) (.atom 10) (.var (.atom 11) 0) (.lam (.atom 12) (.var (.atom 13) 0)))
private def otherFirst : StepAt [.fn,.body] otherSource otherMiddle := .fn (.body (.root _ _ _ _))
private def otherSecond : StepAt [.arg] otherMiddle otherTarget := .arg (.root _ _ _ _)
private def otherLabels : History step.paths otherSource otherTarget := .cons otherFirst (.cons otherSecond (.nil _))

/-- The global uniform degree is 7, while the paired INIT annotation has
degrees 3 and 10. The real middle is unsafe, yet a strict copied read has
one shared old coordinate, both preserved labels, and an actual origin trace. -/
theorem actual_paired_uniform_origin :
    ¬middle.OuterBarsSafe (fun payload=>payload≠a) ∧
    otherSource.degreeAt [.fn,.body]≠otherSource.degreeAt [.arg] ∧
    ∃ oldPosition oldNode otherOld,
      source.subterm oldPosition=some oldNode ∧otherSource.subterm oldPosition=some otherOld ∧
      oldNode.label=a ∧otherOld.label=Label.atom 6 ∧
      BetaNodeHistoryPreimage labels [.fn,.body,.fn] oldPosition := by
  refine ⟨?_,?_,?_⟩
  · intro middleSafe
    have atResult : middle.subterm [.fn,.body]=some insideResult := rfl
    exact first.created_label_not_safe rfl atResult (Or.inl rfl)
      ((LTerm.outerBarsSafe_iff _ _).mp middleSafe _ (LTerm.label_mem_of_subterm atResult))
  · change some (Label.atom 3)≠some (Label.atom 10)
    decide
  · exact step.complete.1.marker_free_paired_origin (DegreeAligned.initial source selection)
      labels otherLabels rfl selected (current:=.var a 0) (otherCurrent:=.var (.atom 6) 0) rfl rfl True.intro

#print axioms Marked.RelativeOldHistory.marker_free_paired_origin
#print axioms actual_paired_uniform_origin
end Lamping.Checks.UniformAnnotatedOrigins
