import Lamping.Lambda.MarkerLeafSourceFirstChains
import Lamping.Checks.DirectedMarkerLeafTails
namespace Lamping.Checks.MarkerLeafSourceFirstChainsChecks
open Lambda Lambda.Labelled
open UniformOldCreatedIncomingLabelsChecks.Distinct

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

def leftLeaf : DirectedMarkerLeafOutput F source (.atom 7) false [left,right] (leftNode.label.readLetters false) where
  pre := []
  middle := source
  target := middle
  site := left
  event := leftEvent
  after := [right]
  schedule := rfl
  edge := left
  reader := left
  oldReader := oldLeft
  first := oldLeft
  last := left++[Step.fn,Step.body]
  current := leftNode
  firstNode := oldArgument
  lastNode := .var (.atom 8) 0
  reading := ⟨Or.inr ⟨_,_,rfl,rfl⟩,rfl⟩
  origin := BetaIncomingReadingOrigin.copyLambda (body:=.var (.atom 8) 0) (argument:=oldArgument) (site:=left) (q:=[]) rfl rfl rfl rfl
  lookup := rfl
  firstLookup := rfl
  lastLookup := rfl
  firstSafe := by trivial
  lastSourcePosition := left++[Step.fn,Step.body]
  lastSourceNode := .var (.atom 8) 0
  lastSourceLookup := rfl
  lastTrace := .nil _ _
  marker := .under (.atom 7)
  marks := Or.inr rfl
  formula := Or.inr (Or.inr ⟨rfl,rfl,.app (.atom 6) (.lam (.atom 7) (.var (.atom 8) 0)) oldArgument,rfl,rfl⟩)
  continuation := []
  equation := (List.append_nil _).symm

def rightLeaf : DirectedMarkerLeafOutput F source (.atom 7) false [left,right] (leftNode.label.readLetters false) where
  pre := [left]
  middle := middle
  target := target
  site := right
  event := SelectedOldOtherLastOriginsChecks.event
  after := []
  schedule := rfl
  edge := right
  reader := right
  oldReader := oldRight
  first := oldRight
  last := right++[Step.fn,Step.body]
  current := leftNode
  firstNode := oldArgument
  lastNode := .var (.atom 8) 0
  reading := SelectedOldOtherLastOriginsChecks.actual_reading
  origin := SelectedOldOtherLastOriginsChecks.readingOrigin
  lookup := rfl
  firstLookup := rfl
  lastLookup := rfl
  firstSafe := by trivial
  lastSourcePosition := right++[Step.fn,Step.body]
  lastSourceNode := .var (.atom 8) 0
  lastSourceLookup := rfl
  lastTrace := SelectedOldOtherLastOriginsChecks.ownLastTrace
  marker := .under (.atom 7)
  marks := Or.inr rfl
  formula := Or.inr (Or.inr ⟨rfl,rfl,.app (.atom 6) (.lam (.atom 7) (.var (.atom 8) 0)) oldArgument,rfl,rfl⟩)
  continuation := []
  equation := (List.append_nil _).symm

def rightFirstTrace : BetaNodeHistoryPreimage rightLeaf.event.labels rightLeaf.first oldRight :=
  .one (step:=firstStep) (by rfl) (.context (by rintro ⟨rest,impossible⟩;cases impossible)) (.nil _ _)
def rightFunctionTrace : BetaNodeHistoryPreimage rightLeaf.event.labels (rightLeaf.site++[.fn]) (right++[.fn]) :=
  .one (step:=firstStep) (by rfl) (.context (by rintro ⟨rest,impossible⟩;cases impossible)) (.nil _ _)

theorem left_exact_source_chain : PrerequisiteChain source oldLeft [oldLeft,left++[.fn]] := by
  obtain ⟨name,reader,first,node,functionBody,chosen,lookup,fullLabel,atFunction,firstTrace,startTrace,fnTrace,chain⟩:=
    leftLeaf.source_first_two_chain selected source_safe
  have nameEq : name=left:=List.append_cancel_right (fnTrace.unique (.nil _ _))
  have firstEq:=firstTrace.unique (.nil _ _)
  have readerEq:=startTrace.unique (.nil _ _)
  subst name;subst first;subst reader
  exact chain

theorem right_exact_source_chain : PrerequisiteChain source oldRight [oldRight,right++[.fn]] := by
  obtain ⟨name,reader,first,node,functionBody,chosen,lookup,fullLabel,atFunction,firstTrace,startTrace,fnTrace,chain⟩:=
    rightLeaf.source_first_two_chain selected source_safe
  have nameEq : name=right:=List.append_cancel_right (fnTrace.unique rightFunctionTrace)
  have firstEq:=firstTrace.unique rightFirstTrace
  have readerEq:=startTrace.unique rightFirstTrace
  subst name;subst first;subst reader
  exact chain

theorem actual_complete_source_labels :
    [oldLeft,left++[.fn]].map source.labelAt=[oldRight,right++[.fn]].map source.labelAt := by
  obtain ⟨ln,rn,lr,rr,lf,rf,lo,ro,lc,rc,lat,rat,lt,rt,lfn,rfn,lchain,rchain,firstEq,listsEq⟩:=
    leftLeaf.compare_source_first_two_chains rightLeaf selected source_safe rfl
  have lfEq:=lt.unique (.nil _ _)
  have rfEq:=rt.unique rightFirstTrace
  have lnEq : ln=left:=List.append_cancel_right (lfn.unique (.nil _ _))
  have rnEq : rn=right:=List.append_cancel_right (rfn.unique rightFunctionTrace)
  simpa only [lfEq,rfEq,lnEq,rnEq] using listsEq

theorem actual_source_is_noninitial : ¬INIT source := by
  intro init
  obtain ⟨n,equal⟩:=init.1 source.label (LTerm.label_mem_of_subterm (by rfl : source.subterm []=some source))
  cases equal

theorem actual_same_initial_two_old : INIT original ∧Closed original.erase ∧History [[],left,right] original target ∧
    Marked.RelativeOldHistory F [left,right] (Marked.mark F source.erase) SelectedOldOtherLastOriginsChecks.afterMarked ∧
    ¬INIT source ∧¬middle.OuterBarsSafe (fun x=>x≠Label.atom 7) :=
  ⟨initial,by simp [Closed,Scoped,original,initLabels,initFrom,nodeCount,LTerm.erase],
    globalHistory.append labels,old,actual_source_is_noninitial,unsafe_middle⟩

theorem actual_first_last_roles : left≠right ∧oldLeft≠oldRight ∧
    leftLeaf.first=oldLeft ∧rightLeaf.first=oldRight ∧
    oldLeft≠leftLeaf.last ∧oldRight≠rightLeaf.last ∧
    source.subterm oldLeft=some oldArgument ∧source.subterm oldRight=some oldArgument ∧
    source.subterm leftLeaf.last=some (.var (.atom 8) 0) ∧
    source.subterm rightLeaf.last=some (.var (.atom 8) 0) ∧
    leftLeaf.pre=[] ∧rightLeaf.pre=[left] :=
  ⟨by decide,by decide,rfl,rfl,by decide,by decide,rfl,rfl,rfl,rfl,rfl,rfl⟩

#print axioms DirectedMarkerLeafOutput.source_first_two_chain
#print axioms DirectedMarkerLeafOutput.compare_source_first_two_chains
#print axioms left_exact_source_chain
#print axioms right_exact_source_chain
#print axioms actual_complete_source_labels
#print axioms actual_source_is_noninitial
#print axioms actual_same_initial_two_old
#print axioms actual_first_last_roles
end Lamping.Checks.MarkerLeafSourceFirstChainsChecks
