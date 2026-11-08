import Lamping.Lamping.SameEventForwardHeads
import Lamping.Checks.DirectedReadingDecomposition

namespace Lamping.Checks.SameEventForwardHeadsChecks
open AG Graph Lambda Lambda.Labelled

namespace SharedCopies
abbrev I : Term := .lam (.var 0)
abbrev original : LTerm := initLabels
  (.app (.lam (.app (.lam (.app (.var 0) (.var 0))) (.app (.var 0) I))) (.app I I))
abbrev innerBody : LTerm := .app (.atom 4) (.var (.atom 5) 0) (.var (.atom 6) 0)
abbrev innerArg : LTerm := .app (.atom 7) (.var (.atom 8) 0) (.lam (.atom 9) (.var (.atom 10) 0))
abbrev body : LTerm := LTerm.contract (.atom 2) (.atom 3) innerBody innerArg
abbrev argument : LTerm := .app (.atom 11) (.lam (.atom 12) (.var (.atom 13) 0))
  (.lam (.atom 14) (.var (.atom 15) 0))
abbrev source : LTerm := .app (.atom 0) (.lam (.atom 1) body) argument
abbrev target : LTerm := LTerm.contract (.atom 0) (.atom 1) body argument
abbrev current : LTerm := argument.prepend ((Label.atom 8).concat (Label.atom 1).under)
abbrev F : List Path := [[]]
abbrev markedBody : Marked := .app [] (.app [] (.var 0) (.lam (.var 0)))
  (.app [] (.var 0) (.lam (.var 0)))
abbrev markedArg : Marked := .app [[.arg]] (.lam (.var 0)) (.lam (.var 0))

def prefixStep : StepAt [.fn,.body] original source := .fn (.body (.root _ _ _ _))
def prefixHistory : History [[.fn,.body]] original source := .cons prefixStep (.nil _)
theorem initial : INIT original := init_is_INIT _
theorem closed : Closed source.erase := prefixHistory.closed (by
  change ((0<2 ∧0<2) ∧(0<1 ∧0<2)) ∧(0<1 ∧0<1)
  decide)
theorem noninitial : source≠initLabels source.erase := by decide
theorem sourceSafe : source.OuterBarsSafe (fun x=>x≠Label.atom 1) := by
  simp only [body,LTerm.contract,LTerm.subst,LTerm.single,LTerm.prepend,
    LTerm.OuterBarsSafe,Label.atom,Label.concat,Label.over,Label.under,Label.OuterBarsSafe]
  decide

def event : SelectedOldTurn F source (.atom 1) [] source target [] where
  markedBefore := Marked.mark F source.erase
  markedAfter := Marked.contract markedBody markedArg
  beforeOld := .nil _
  reduction := by
    change Marked.ReductionAt [] (.red [[]] markedBody markedArg) (Marked.contract markedBody markedArg)
    exact .redRoot _ _ _
  member := by decide
  labels := .nil _
  turn := .root _ _ _ _
  beta := .atom 0
  body := body
  argument := argument
  redex := rfl

def history : History [[]] source target := .cons event.turn (.nil _)
theorem selected (name : Path) (member : name∈F) : source.degreeAt name=some (.atom 1) := by
  have same := List.mem_singleton.mp member
  subst name
  rfl

abbrev parent (b : Bool) : Path := if b then [.fn] else [.arg]
abbrev first (b : Bool) : Path := [.fn,.body]++(parent b++[.fn])
def origin (b : Bool) : BetaIncomingReadingOrigin body argument [] (parent b++[.fn]) (parent b)
    ([.fn,.body]++parent b) (first b) [.arg] :=
  .copyFunction (by cases b <;> rfl) (by rfl) (by rfl)
def reading (b : Bool) : PrerequisiteReadsDirected target (parent b) (parent b++[.fn]) true :=
  by cases b <;> exact ⟨Or.inl ⟨_,_,_,rfl,rfl⟩,rfl⟩
def leaf (b : Bool) : DirectedMarkerLeafOutput F source (.atom 1) true [[]] current.label.letters where
  pre := []
  middle := source
  target := target
  site := []
  event := event
  after := []
  schedule := rfl
  edge := parent b++[Step.fn]
  reader := parent b
  oldReader := [Step.fn,Step.body]++parent b
  first := first b
  last := [.arg]
  current := current
  firstNode := .var (.atom 8) 0
  lastNode := argument
  reading := reading b
  origin := by simpa only [event] using origin b
  lookup := by cases b <;> rfl
  firstLookup := by cases b <;> rfl
  lastLookup := rfl
  firstSafe := by trivial
  lastSourcePosition := [.arg]
  lastSourceNode := argument
  lastSourceLookup := rfl
  lastTrace := .nil _ _
  marker := .under (.atom 1)
  marks := Or.inr rfl
  formula := Or.inl rfl
  continuation := []
  equation := (List.append_nil _).symm

/-- Distinct actual copied FN heads have the SAME full global word, while
their common relative source is nonINIT and retains its actual INIT prefix. -/
theorem actual_distinct_same_word :
    (leaf true).edge≠(leaf false).edge ∧(leaf true).current.label=(leaf false).current.label ∧
    source≠initLabels source.erase ∧INIT original ∧History [[.fn,.body],[]] original target :=
  ⟨by decide,rfl,noninitial,initial,prefixHistory.append history⟩

/-- Direct complete-head consumer with legal conditional SOURCE REP.
No physical site/Joint realization for this nonINIT source is asserted. -/
theorem actual_distinct_complete_heads
    {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
    {g : Net signature N B W} {root : B}
    (matching : Matches g root source.erase)
    (sourceSelection : OccurrenceFragmentSelection source g root)
    (representation : ChainRepresentationInvariant closed sourceSelection)
    (selection : SourceEdgeSelection (initLabels source.erase) g root) (edge : BetaEdge g) :
    ∃localTarget,History [[]] (initLabels source.erase) localTarget ∧
      ∃lp : PairedMarkerEventGeometry (leaf true) (initLabels source.erase) localTarget,
        ∃rp : PairedMarkerEventGeometry (leaf false) (initLabels source.erase) localTarget,
          selection.evalLabel edge lp.current.label=selection.evalLabel edge rp.current.label := by
  obtain ⟨localTarget,labels,_erase⟩ := lift_history history.betaHistory
    (initLabels source.erase) (erase_initLabels source.erase)
  obtain ⟨lp⟩ := paired_marker_leaf_geometry (leaf true) labels (erase_initLabels source.erase).symm
  obtain ⟨rp⟩ := paired_marker_leaf_geometry (leaf false) labels (erase_initLabels source.erase).symm
  exact ⟨localTarget,labels,lp,rp,paired_marker_same_event_forward_evaluations (leaf true) (leaf false)
    lp rp rfl rfl matching selected sourceSafe prefixHistory initial closed sourceSelection representation selection edge rfl⟩
end SharedCopies

/-- RESULTvar0 uses the real contractum, whose literal word still contains
the second separator and actual ARG; it is not just FIRST+marker+BODY. -/
theorem actual_result_zero_complete :
    (originMarker [.fn] [.fn] (.atom 2)=.over (.atom 2) ∧
      DirectedReadingDecompositionChecks.result=LTerm.contract (.atom 1) (.atom 2)
        (.var (.atom 3) 0) DirectedReadingDecompositionChecks.arg) ∧
      DirectedReadingDecompositionChecks.result.label.letters=
        [.atom 1,.over (.atom 2),.atom 3,.under (.atom 2),.atom 4] := by
  have output := DirectedReadingDecompositionChecks.functionOrigin.forward_complete_head
    DirectedReadingDecompositionChecks.step rfl ⟨Or.inl ⟨_,_,_,rfl,rfl⟩,rfl⟩ rfl rfl (.atom 2)
  rcases output with good|bad
  · exact ⟨good,rfl⟩
  · have impossible : originMarker [.fn] [.fn] (.atom 2)=.over (.atom 2) := by simp [originMarker]
    cases impossible.symm.trans bad.1

#print axioms SharedCopies.actual_distinct_same_word
#print axioms SharedCopies.actual_distinct_complete_heads
#print axioms actual_result_zero_complete
end Lamping.Checks.SameEventForwardHeadsChecks
