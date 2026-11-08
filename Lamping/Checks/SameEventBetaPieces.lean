import Lamping.Lamping.SameEventBetaPieces
import Lamping.Checks.PairedMarkerPrefixComparison

namespace Lamping.Checks.SameEventBetaPiecesChecks
open AG Graph Lambda Lambda.Labelled
open BetaBeforeBlockImagesChecks

abbrev argument : LTerm := .lam (.atom 4)
  (.app (.atom 5) (.var (.atom 6) 0) (.lam (.atom 7) (.var (.atom 8) 0)))
abbrev markedBody : Marked := .var 0
abbrev markedArgument : Marked := .lam (.app [] (.var 0) (.lam (.var 0)))
abbrev markedOther : Marked := .lam (.var 0)

def event : SelectedOldTurn [[.fn]] source (.atom 2) [] source target [.fn] where
  markedBefore := Marked.mark [[.fn]] source.erase
  markedAfter := FunctionWrappedReachable.endpoint
  beforeOld := .nil _
  reduction := .appL (.redRoot _ _ _)
  member := by decide
  labels := .nil _
  turn := WrappedSuccessfulChains.actualStep
  beta := .atom 1
  body := .var (.atom 3) 0
  argument := argument
  redex := rfl

def leaf : DirectedMarkerLeafOutput [[.fn]] source (.atom 2) true [[.fn]] functionTerm.label.letters where
  pre := []
  middle := source
  target := target
  site := [.fn]
  event := event
  after := []
  schedule := rfl
  edge := [.fn]
  reader := []
  oldReader := []
  first := [.fn]
  last := [.fn,.fn,.body]
  current := functionTerm
  firstNode := .app (.atom 1) (.lam (.atom 2) (.var (.atom 3) 0)) argument
  lastNode := .var (.atom 3) 0
  reading := ⟨Or.inl ⟨_,_,_,rfl,rfl⟩,rfl⟩
  origin := .resultFunction rfl rfl
  lookup := rfl
  firstLookup := rfl
  lastLookup := rfl
  firstSafe := by trivial
  lastSourcePosition := [.fn,.fn,.body]
  lastSourceNode := .var (.atom 3) 0
  lastSourceLookup := rfl
  lastTrace := .nil _ _
  marker := .over (.atom 2)
  marks := Or.inl rfl
  formula := Or.inr (Or.inl ⟨rfl,rfl,argument,rfl,rfl⟩)
  continuation := []
  equation := (List.append_nil _).symm

/-- A real closed physical site supplies every hypothesis of the NEW full
producer wrapper. Two arbitrary selectors test the same literal occurrence;
this is sameleaf integration, not a distinct-chain/Joint claim. -/
theorem actual_same_producer_complete_pieces
    (leftSelection rightSelection : OccurrenceFragmentSelection target site.reduce (.inl ())) :
    ∃sourceSelection : OccurrenceFragmentSelection source site.net (.inl ()),
      JointRepresentation WrappedSuccessfulChains.sourceClosed sourceSelection ∧
      ∃edge : BetaEdge site.net,SiteBetaGeometry site edge ∧∃oldBlock,
        oldBlock≠[] ∧
        BetaPathResidual site edge
          ((leftSelection ⟨[.fn],rfl⟩).fragment.segments.map (plugEnd _ _).invFun) oldBlock ∧
        BetaPathResidual site edge
          ((rightSelection ⟨[.fn],rfl⟩).fragment.segments.map (plugEnd _ _).invFun) oldBlock ∧
        (leftSelection ⟨[.fn],rfl⟩).fragment.segments=(rightSelection ⟨[.fn],rfl⟩).fragment.segments := by
  have originalMatches : Matches FunctionWrappedReachable.net (.inl ()) source.erase :=
    encode_closed_matches FunctionWrappedReachable.term FunctionWrappedReachable.closed 0
  have matching := FunctionWrappedReachable.concrete.sourceIso.matches originalMatches
  obtain ⟨initialSelection,initialJoint⟩ := encode_initial_joint_realization source
    WrappedSuccessfulChains.sourceClosed WrappedSuccessfulChains.initial 0
  obtain ⟨sourceSelection⟩ := matching.occurrence_fragment_selection WrappedSuccessfulChains.sourceClosed
  have joint := (FunctionWrappedReachable.concrete.sourceIso.joint_representation originalMatches
    WrappedSuccessfulChains.sourceClosed initialSelection sourceSelection).mpr initialJoint
  have inputs := FunctionWrappedReachable.concrete.sourceIso.rootInputs
    (encode_closed_independence FunctionWrappedReachable.term FunctionWrappedReachable.closed 0).rootInputs
  obtain ⟨originalFlow⟩ := encode_flowBalance FunctionWrappedReachable.term 0
  have flow := FunctionWrappedReachable.concrete.sourceIso.flowBalance originalFlow
  obtain ⟨originalBalance⟩ := encode_indexed_balance FunctionWrappedReachable.term 0
  have balance := FunctionWrappedReachable.concrete.sourceIso.indexed_balance originalBalance
  have transparency := FunctionWrappedReachable.concrete.sourceIso.transparency
    (encode_closed_transparency FunctionWrappedReachable.term FunctionWrappedReachable.closed 0)
  obtain ⟨localTarget,_localHistory,edge,selection,geometry,lp,rp,heads,nonempty,_otherNonempty,
      leftResidual,rightResidual,pieces⟩ :=
    site.beta_same_event_forward_pieces WrappedSuccessfulChains.sourceClosed matching inputs flow rfl balance rfl
      transparency FunctionWrappedReachable.relative
      (by simp [FunctionWrappedReachable.endpoint,Marked.Normal]) WrappedSuccessfulChains.actualHistory
      leaf leaf rfl rfl rfl rfl selected (WrappedSuccessfulChains.initial.outerBarsSafe _)
      (.nil source) WrappedSuccessfulChains.initial sourceSelection joint.1 rfl
      (leftSelection ⟨[.fn],rfl⟩) (rightSelection ⟨[.fn],rfl⟩)
  exact ⟨sourceSelection,joint,edge,geometry,selection.evalLabel edge lp.current.label,nonempty,
    leftResidual,heads ▸ rightResidual,pieces⟩

#print axioms actual_same_producer_complete_pieces
end Lamping.Checks.SameEventBetaPiecesChecks
