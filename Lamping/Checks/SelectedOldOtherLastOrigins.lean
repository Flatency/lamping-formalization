import Lamping.Lambda.SelectedOldOtherLastOrigins
import Lamping.Checks.NodeIncomingFirstCreation
namespace Lamping.Checks.SelectedOldOtherLastOriginsChecks
open Lambda Lambda.Labelled
open UniformOldCreatedIncomingLabelsChecks.Distinct
abbrev prefixLabels := NodeIncomingFirstCreationChecks.Distinct.preLabels
abbrev beforeMarked : Marked := .app [[]] (.lam (.lam (.var 0)))
  (.lam (.red [right] (.var 0) (.lam (.var 0))))
abbrev afterMarked : Marked := .app [[]] (.lam (.lam (.var 0))) (.lam (.lam (.var 0)))

def event : SelectedOldTurn F source (.atom 7) [left] middle target right where
  markedBefore := beforeMarked
  markedAfter := afterMarked
  beforeOld := .cons (.appL (.lam (.redRoot _ _ _))) (by decide) (.nil _)
  reduction := .appR (.lam (.redRoot _ _ _))
  member := by decide
  labels := prefixLabels
  turn := secondStep
  beta := .atom 6
  body := .var (.atom 8) 0
  argument := oldArgument
  redex := rfl

abbrev lastPosition : Path := right++[.fn,.body]
def readingOrigin : BetaIncomingReadingOrigin event.body event.argument right right right
    (right++[.arg]) (right++[.arg]) lastPosition :=
  .copyLambda (q:=[]) rfl rfl rfl rfl

def ownLastTrace : BetaNodeHistoryPreimage event.labels lastPosition lastPosition :=
  .one (step:=firstStep) (by rfl)
    (.context (by rintro ⟨rest,impossible⟩;cases impossible)) (.nil _ _)

theorem actual_other_last_suffix :
    ∃eventNode originalNode,middle.subterm lastPosition=some eventNode ∧
      source.subterm lastPosition=some originalNode ∧
      (eventNode.label=originalNode.label ∨∃preword marker,marker.MarksDegree (.atom 7) ∧
        eventNode.label.letters=preword++marker::originalNode.label.letters) :=
  event.other_last_origin_suffix_at_trace selected readingOrigin ownLastTrace

theorem own_other_last_not_constructor_origin :
    lastPosition≠oldRight ∧
    middle.subterm lastPosition=some (.var (.atom 8) 0) ∧
    source.subterm lastPosition=some (.var (.atom 8) 0) ∧
    source.subterm oldRight=some oldArgument := ⟨by decide,rfl,rfl,rfl⟩

theorem actual_reading : PrerequisiteReadsDirected target right right false :=
  ⟨Or.inr ⟨leftNode.label,.var (.atom 10) 0,rfl,rfl⟩,rfl⟩

/-- q=[] COPY lambda CONTEXT overlaps the beta result. The actual other-last
is BODY var8, whereas the created lambda's constructor ancestry is ARG lam9.
The nonempty actual prefix has already made the whole middle unsafe. -/
theorem actual_same_initial_nonempty_prefix_other_last :
    INIT original ∧History [[],left,right] original target ∧
    ¬middle.OuterBarsSafe (fun x=>x≠Label.atom 7) ∧
    PrerequisiteReadsDirected target right right false ∧
    lastPosition≠oldRight ∧
    BetaNodeHistoryPreimage event.labels lastPosition lastPosition ∧
    (∃eventNode originalNode,middle.subterm lastPosition=some eventNode ∧
      source.subterm lastPosition=some originalNode ∧
      (eventNode.label=originalNode.label ∨∃preword marker,marker.MarksDegree (.atom 7) ∧
        eventNode.label.letters=preword++marker::originalNode.label.letters)) :=
  ⟨initial,globalHistory.append labels,unsafe_middle,actual_reading,by decide,ownLastTrace,actual_other_last_suffix⟩

#print axioms event
#print axioms ownLastTrace
#print axioms actual_other_last_suffix
#print axioms own_other_last_not_constructor_origin
#print axioms actual_same_initial_nonempty_prefix_other_last
end Lamping.Checks.SelectedOldOtherLastOriginsChecks
