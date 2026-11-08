import Lamping.Lamping.BackwardOtherLastTargets
import Lamping.Checks.SelectedOldOtherLastOrigins
namespace Lamping.Checks.BackwardOtherLastTargetsChecks
open Graph Lambda Lambda.Labelled AG SyntaxIncidence
namespace DifferentPrefixes
open UniformOldCreatedIncomingLabelsChecks.Distinct
abbrev rightEvent := SelectedOldOtherLastOriginsChecks.event
abbrev leftLast : Path := left++[.fn,.body]
abbrev rightLast : Path := right++[.fn,.body]

def leftEvent : SelectedOldTurn F source (.atom 7) [] source middle left where
  markedBefore := Marked.mark F source.erase
  markedAfter := SelectedOldOtherLastOriginsChecks.beforeMarked
  beforeOld := .nil _
  reduction := .appL (.lam (.redRoot _ _ _))
  member := by decide
  labels := .nil _
  turn := firstStep
  beta := .atom 6
  body := .var (.atom 8) 0
  argument := oldArgument
  redex := rfl

def leftOrigin : BetaIncomingReadingOrigin leftEvent.body leftEvent.argument left left left
    (left++[.arg]) (left++[.arg]) leftLast := .copyLambda (q:=[]) rfl rfl rfl rfl

def leftTrace : BetaNodeHistoryPreimage leftEvent.labels leftLast leftLast := .nil _ _

theorem leftRead : PrerequisiteReadsDirected middle left left false :=
  ⟨Or.inr ⟨leftNode.label,.var (.atom 10) 0,rfl,rfl⟩,rfl⟩

theorem closedSource : Closed source.erase := by
  apply globalHistory.closed
  change (0<1 ∧0<1) ∧(0<2 ∧0<2)
  decide

def leftBinder : ProperPosition source := ⟨left++[.fn],Or.inr ⟨.atom 7,.var (.atom 8) 0,rfl⟩⟩
def rightBinder : ProperPosition source := ⟨right++[.fn],Or.inr ⟨.atom 7,.var (.atom 8) 0,rfl⟩⟩

theorem leftTarget : Target source leftLast (some leftBinder) :=
  Or.inr ⟨.atom 8,0,.atom 7,.var (.atom 8) 0,[],rfl,rfl,rfl,rfl⟩
theorem rightTarget : Target source rightLast (some rightBinder) :=
  Or.inr ⟨.atom 8,0,.atom 7,.var (.atom 8) 0,[],rfl,rfl,rfl,rfl⟩

theorem actual_bodyvar8_not_arglambda9 :
    source.subterm leftLast=some (.var (.atom 8) 0) ∧source.subterm rightLast=some (.var (.atom 8) 0) ∧
    source.subterm oldLeft=some oldArgument ∧source.subterm oldRight=some oldArgument ∧
    leftLast≠oldLeft ∧rightLast≠oldRight := ⟨rfl,rfl,rfl,rfl,by decide,by decide⟩

theorem actual_middle_target_and_zerojump :
    ∃vertex : ProperPosition middle,Target middle rightLast (some vertex) ∧
      (vertex.val=right ∨vertex.val=right++[.fn]) ∧
      PrerequisitePrefix middle rightLast [] vertex.val ∧EndpointChain middle (some vertex) [right++[.fn]] :=
  rightEvent.backward_other_last_target SelectedOldOtherLastOriginsChecks.readingOrigin SelectedOldOtherLastOriginsChecks.actual_reading

theorem actual_different_prefix_pair : SuccessfulEndpointIso source closedSource (some leftBinder) (some rightBinder) := by
  obtain ⟨ln,rn,lv,rv,ll,rl,lt,rt,comparison⟩:=leftEvent.backward_other_last_pair_iso rightEvent selected closedSource
    leftOrigin SelectedOldOtherLastOriginsChecks.readingOrigin leftRead SelectedOldOtherLastOriginsChecks.actual_reading
    leftTrace SelectedOldOtherLastOriginsChecks.ownLastTrace
  have le : (some lv : Vertex source)=some leftBinder := Target.unique lt leftTarget
  have re : (some rv : Vertex source)=some rightBinder := Target.unique rt rightTarget
  rw [le,re] at comparison
  exact comparison

theorem actual_overlap_reverse_word :
    leftNode.label.readLetters false=[.atom 9,.under (.atom 7),.atom 8,.over (.atom 7),.atom 6] := rfl

theorem actual_selected_target_is_third_role :
    source.subterm leftBinder.val=some (.lam (.atom 7) (.var (.atom 8) 0)) ∧
    source.subterm rightBinder.val=some (.lam (.atom 7) (.var (.atom 8) 0)) ∧
    leftBinder.val≠leftLast ∧leftBinder.val≠oldLeft ∧rightBinder.val≠rightLast ∧rightBinder.val≠oldRight :=
  ⟨rfl,rfl,by decide,by decide,by decide,by decide⟩

theorem actual_same_initial_distinct_prefixes : INIT original ∧History [[],left,right] original target ∧
    ([] : List Path)≠[left] ∧leftBinder.val≠rightBinder.val :=
  ⟨initial,globalHistory.append labels,by simp,by decide⟩
end DifferentPrefixes
namespace ResultLambda
abbrev I : Term := WrappedSuccessfulChains.I
abbrev source : LTerm := initLabels (.app (.lam (.lam (.var 0))) I)
abbrev body : LTerm := .lam (.atom 2) (.var (.atom 3) 0)
abbrev argument : LTerm := .lam (.atom 4) (.var (.atom 5) 0)
abbrev target : LTerm := LTerm.contract (.atom 0) (.atom 1) body argument
abbrev F : List Path := [[]]
def event : SelectedOldTurn F source (.atom 1) [] source target [] where
  markedBefore := Marked.mark F source.erase
  markedAfter := .lam (.var 0)
  beforeOld := .nil _
  reduction := .redRoot _ _ _
  member := by decide
  labels := .nil _
  turn := .root _ _ _ _
  beta := .atom 0
  body := body
  argument := argument
  redex := rfl

def origin : BetaIncomingReadingOrigin event.body event.argument [] [] [] [.fn,.body] [.fn,.body] [] :=
  .resultLambda rfl rfl rfl

theorem reading : PrerequisiteReadsDirected target [] [] false := ⟨Or.inr ⟨_,_,rfl,rfl⟩,rfl⟩
theorem selected (p : Path) (mem : p∈F) : source.degreeAt p=some (.atom 1) := by
  have eq:=List.mem_singleton.mp mem;subst p;rfl

theorem actual_result_original_target :
    ∃name∈F,∃beta body argument originalNode vertex,
      source.subterm name=some (.app beta (.lam (.atom 1) body) argument) ∧
      source.subterm []=some originalNode ∧Target source [] (some vertex) ∧
      (vertex.val=name ∨vertex.val=name++[.fn]) ∧EndpointChain source (some vertex) [name++[.fn]] :=
  event.backward_original_other_last_target selected origin reading (.nil _ _)
end ResultLambda
#print axioms SelectedOldTurn.backward_other_last_target
#print axioms SelectedOldTurn.backward_original_other_last_target
#print axioms SelectedOldTurn.backward_other_last_pair_iso
#print axioms DifferentPrefixes.actual_bodyvar8_not_arglambda9
#print axioms DifferentPrefixes.actual_middle_target_and_zerojump
#print axioms DifferentPrefixes.actual_different_prefix_pair
#print axioms DifferentPrefixes.actual_overlap_reverse_word
#print axioms DifferentPrefixes.actual_selected_target_is_third_role
#print axioms DifferentPrefixes.actual_same_initial_distinct_prefixes
#print axioms ResultLambda.actual_result_original_target
end Lamping.Checks.BackwardOtherLastTargetsChecks
