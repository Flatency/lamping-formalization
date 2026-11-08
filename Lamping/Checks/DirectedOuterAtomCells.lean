import Lamping.Lambda.DirectedOuterAtomCells
import Lamping.Checks.UniformOldOuterImageAlignment

namespace Lamping.Checks.DirectedOuterAtomCellsChecks
open Lambda Lambda.Labelled

namespace Nested
open UniformOldNodeLabelSuffixChecks
open DirectedMarkerSpineIncidenceChecks.Nested

theorem forward_actual_cells :
    INIT originalWrapped ∧PrerequisiteChain targetForward [] [[.fn]] ∧
    ∃leaf snapshot,
    ∃geometry : SpineIncidenceProvenance family sourceWrapped (.atom 10) true
      forwardSpine (by rfl : targetForward.subterm [.fn]=some target) leaf snapshot,
    ∃localTarget,∃localHistory : History [[.fn],[.fn]] (initLabels sourceWrapped.erase) localTarget,
    ∃paired : PairedSpineReannotation geometry localHistory (erase_initLabels sourceWrapped.erase).symm,
      2≤geometry.creationFrames.length ∧leaf.after≠[] ∧paired.localTailPieces≠[] ∧
      Nonempty (DirectedOuterAtomCells (initialRelabelling sourceWrapped 0)
        paired.current.label paired.current.label true) := by
  obtain ⟨leaf,snapshot,geometry,multiple,after,_⟩ :=
    PairedMarkerSpineReannotationChecks.Nested.forward_multiple_frames
  obtain ⟨localTarget,localHistory,_⟩ :=
    lift_history labelsForward.betaHistory (initLabels sourceWrapped.erase) (erase_initLabels _)
  obtain ⟨paired⟩ := geometry.paired_reannotation localHistory (erase_initLabels _).symm
  have output := oldForward.directed_outer_atom_cells oldForward labelsForward labelsForward
    localHistory localHistory selected sourceSafe (by rfl : targetForward.subterm [.fn]=some target)
    (by rfl : targetForward.subterm [.fn]=some target) paired.currentLookup paired.currentLookup rfl true
  exact ⟨initial,successful_readings.1,leaf,snapshot,geometry,localTarget,localHistory,paired,
    multiple,after,paired.tails_nonempty multiple,output⟩

theorem reverse_actual_cells :
    INIT originalWrapped ∧PrerequisiteChain targetReverse [.fn] [[.fn]] ∧
    ∃leaf snapshot,
    ∃geometry : SpineIncidenceProvenance family sourceWrapped (.atom 10) false
      reverseSpine (by rfl : targetReverse.subterm [.fn]=some reverseResult) leaf snapshot,
    ∃localTarget,∃localHistory : History [[.fn,.arg],[.fn]] (initLabels sourceWrapped.erase) localTarget,
    ∃paired : PairedSpineReannotation geometry localHistory (erase_initLabels sourceWrapped.erase).symm,
      2≤geometry.creationFrames.length ∧leaf.after≠[] ∧paired.localTailPieces≠[] ∧
      Nonempty (DirectedOuterAtomCells (initialRelabelling sourceWrapped 0)
        paired.current.label paired.current.label false) := by
  obtain ⟨leaf,snapshot,geometry,multiple,after,_⟩ :=
    PairedMarkerSpineReannotationChecks.Nested.reverse_multiple_frames
  obtain ⟨localTarget,localHistory,_⟩ :=
    lift_history labelsReverse.betaHistory (initLabels sourceWrapped.erase) (erase_initLabels _)
  obtain ⟨paired⟩ := geometry.paired_reannotation localHistory (erase_initLabels _).symm
  have output := oldReverse.directed_outer_atom_cells oldReverse labelsReverse labelsReverse
    localHistory localHistory selected sourceSafe (by rfl : targetReverse.subterm [.fn]=some reverseResult)
    (by rfl : targetReverse.subterm [.fn]=some reverseResult) paired.currentLookup paired.currentLookup rfl false
  exact ⟨initial,successful_readings.2,leaf,snapshot,geometry,localTarget,localHistory,paired,
    multiple,after,paired.tails_nonempty multiple,output⟩

theorem distinct_real_schedules : ([[.fn],[.fn]] : List Path)≠[[.fn,.arg],[.fn]] := by decide
end Nested

namespace MarkedLast
open UniformOldOuterImageAlignmentChecks.MarkedLast

abbrev word : List Letter := [.atom 3,.under (.atom 1),.atom 5,.over (.atom 6),.atom 7]
theorem literal_word : localCurrent.label.letters=word := rfl

theorem actual_complete_cells (forward : Bool) :
    Nonempty (DirectedOuterAtomCells (initialRelabelling source 0)
      localCurrent.label localCurrent.label forward) :=
  old.directed_outer_atom_cells old labels labels localLabels localLabels selected sourceSafe
    (by rfl : target.subterm [.fn]=some current) (by rfl : target.subterm [.fn]=some current)
    (by rfl : localTarget.subterm [.fn]=some localCurrent)
    (by rfl : localTarget.subterm [.fn]=some localCurrent) rfl forward

theorem first3_cell :
    Nonempty (PairedDirectedAtomCell (initialRelabelling source 0) word word [] 3
      [.under (.atom 1),.atom 5,.over (.atom 6),.atom 7]) := by
  obtain ⟨cells⟩ := actual_complete_cells true
  exact cells.leftCells [] 3 _ rfl

theorem interior5_cell :
    Nonempty (PairedDirectedAtomCell (initialRelabelling source 0) word word
      [.atom 3,.under (.atom 1)] 5 [.over (.atom 6),.atom 7]) := by
  obtain ⟨cells⟩ := actual_complete_cells true
  exact cells.leftCells _ 5 _ rfl

theorem last7_cell :
    Nonempty (PairedDirectedAtomCell (initialRelabelling source 0) word word
      [.atom 3,.under (.atom 1),.atom 5,.over (.atom 6)] 7 []) := by
  obtain ⟨cells⟩ := actual_complete_cells true
  exact cells.leftCells _ 7 [] rfl

theorem reverse5_writing_window :
    ∃cell : PairedDirectedAtomCell (initialRelabelling source 0) word.reverse word.reverse
      [.atom 7,.over (.atom 6)] 5 [.under (.atom 1),.atom 3],
      localCurrent.label.letters=
        ([.under (.atom 1),.atom 3] : List Letter).reverse++[.atom 5]++
          ([.atom 7,.over (.atom 6)] : List Letter).reverse ∧
      initialRelabelling source 0 5=initialRelabelling source 0 cell.rightAtom := by
  obtain ⟨cells⟩ := actual_complete_cells false
  obtain ⟨cell⟩ := cells.leftCells [.atom 7,.over (.atom 6)] 5 [.under (.atom 1),.atom 3] rfl
  exact ⟨cell,cell.writing_windows.1,cell.fullImageEq⟩

theorem compound_not_atomic_and_actual_last :
    ¬IsAtomic oldBeta ∧¬lastNode.label.OuterBarsSafe (fun d=>d≠Label.atom 10) ∧
    initialRelabelling source 0 5=oldBeta ∧
    PrerequisiteChain target [] [[.fn],[.fn,.fn]] :=
  ⟨oldBetaCompound,lastMarked,rfl,chain⟩
end MarkedLast

namespace Singleton
abbrev term : LTerm := initLabels WrappedSuccessfulChains.I
theorem actual_singleton_cell :
    ∃cell : PairedDirectedAtomCell (initialRelabelling term 0)
      [.atom 0] [.atom 0] [] 0 [],
      cell.rightBefore=[] ∧cell.rightAfter=[] ∧cell.rightAtom=0 := by
  have old : Marked.RelativeOldHistory [] [] (Marked.mark [] term.erase) (Marked.mark [] term.erase) := .nil _
  have basis : initLabels term.erase=term := rfl
  have history : History [] term term := .nil _
  have localHistory : History [] (initLabels term.erase) term := by rw [basis];exact .nil _
  have selected : ∀p∈([] : List Path),term.degreeAt p=some (Label.atom 99) := by simp
  have safe : term.OuterBarsSafe (fun d=>d≠Label.atom 99) := (init_is_INIT _).outerBarsSafe _
  obtain ⟨cells⟩ := old.directed_outer_atom_cells old history history localHistory localHistory
    selected safe (by rfl : term.subterm []=some term) (by rfl : term.subterm []=some term)
    (by rfl : term.subterm []=some term) (by rfl : term.subterm []=some term) rfl true
  obtain ⟨cell⟩ := cells.leftCells [] 0 [] rfl
  have before : cell.rightBefore=[] := by simpa using cell.rightBeforeCanonical
  have after : cell.rightAfter=[] := by simpa using cell.rightAfterCanonical
  have node := cell.rightSplit
  rw [before,after] at node
  have atom : cell.rightAtom=0 := (Letter.atom.inj (List.cons.inj node).1).symm
  exact ⟨cell,before,after,atom⟩
end Singleton

namespace CrossPrefix
open SingleUnsafeCopyFunctionAppInputsChecks
open ExpandedArgumentHistoryOriginsChecks.CrossPrefix
open UniformOldOuterImageAlignmentChecks.CrossPrefix

theorem distinct_actual_prefix_cells (forward : Bool) :
    INIT original ∧History [[.arg,.fn,.body],[]] original source ∧
    earlyHead≠leftHead ∧earlyLocal.label≠lateLocal.label ∧
    Nonempty (DirectedOuterAtomCells (initialRelabelling source 0)
      earlyLocal.label lateLocal.label forward) := by
  have earlyAt : middle.subterm earlyHead=some copiedArgument := rfl
  have output := event.beforeOld.directed_outer_atom_cells event.final_old preHistory event.final_history
    localBefore localFull selected sourceSafe earlyAt leftLookup
    (by rfl : localMiddle.subterm earlyHead=some earlyLocal)
    (by rfl : localTarget.subterm leftHead=some lateLocal) rfl forward
  exact ⟨initial,prefixHistory,by decide,by decide,output⟩
end CrossPrefix

#print axioms Marked.RelativeOldHistory.directed_outer_atom_cells
#print axioms directed_atom_cell
#print axioms PairedDirectedAtomCell.writing_windows
#print axioms Nested.forward_actual_cells
#print axioms Nested.reverse_actual_cells
#print axioms Nested.distinct_real_schedules
#print axioms MarkedLast.actual_complete_cells
#print axioms MarkedLast.first3_cell
#print axioms MarkedLast.interior5_cell
#print axioms MarkedLast.last7_cell
#print axioms MarkedLast.reverse5_writing_window
#print axioms MarkedLast.compound_not_atomic_and_actual_last
#print axioms Singleton.actual_singleton_cell
#print axioms CrossPrefix.distinct_actual_prefix_cells
end Lamping.Checks.DirectedOuterAtomCellsChecks
