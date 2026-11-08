import Lamping.Lambda.EarliestReadingMarker
import Lamping.Lambda.DirectedReadingDecomposition
namespace Lamping.Lambda.Labelled

/-- An OUTPUT of actual spine descent. No caller supplies this package and
no field is added to History, SelectedOldTurn, or DirectedMarkerSpine.
The continuation is a literal word, not a physical graph path. -/
structure DirectedMarkerLeafOutput (F : List Path) (source : LTerm) (degree : Label)
    (forward : Bool) (ps : List Path) (word : List Letter) where
  pre : List Path
  middle : LTerm
  target : LTerm
  site : Path
  event : SelectedOldTurn F source degree pre middle target site
  after : List Path
  schedule : ps=pre++site::after
  edge : Path
  reader : Path
  oldReader : Path
  first : Path
  last : Path
  current : LTerm
  firstNode : LTerm
  lastNode : LTerm
  reading : PrerequisiteReadsDirected target reader edge forward
  origin : BetaIncomingReadingOrigin event.body event.argument site edge reader oldReader first last
  lookup : target.subterm edge=some current
  firstLookup : middle.subterm first=some firstNode
  lastLookup : middle.subterm last=some lastNode
  firstSafe : firstNode.label.OuterBarsSafe (fun x=>x≠degree)
  lastSourcePosition : Path
  lastSourceNode : LTerm
  lastSourceLookup : source.subterm lastSourcePosition=some lastSourceNode
  lastTrace : BetaNodeHistoryPreimage event.labels last lastSourcePosition
  marker : Letter
  marks : marker.MarksDegree degree
  formula : ExactDirectedReadingFormula middle site degree forward firstNode lastNode marker current
  continuation : List Letter
  equation : word=current.label.readLetters forward++continuation

/-- Extending a proved OUTPUT retains its actual leaf geometry and appends
only the supplied literal word continuation. -/
def DirectedMarkerLeafOutput.extend
    (leaf : DirectedMarkerLeafOutput F source degree forward ps word) (suffix : List Letter) :
    DirectedMarkerLeafOutput F source degree forward ps (word++suffix) :=
  { leaf with
    continuation := leaf.continuation++suffix
    equation := (congrArg (fun xs : List Letter=>xs++suffix) leaf.equation).trans (List.append_assoc _ _ _) }

/-- The actual final OLD turn extends the remaining schedule after the
same leaf. Its event prefix stays a prefix of THIS supplied schedule. -/
def DirectedMarkerLeafOutput.snoc
    (leaf : DirectedMarkerLeafOutput F source degree forward ps word) (nextSite : Path) :
    DirectedMarkerLeafOutput F source degree forward (ps++[nextSite]) word :=
  { leaf with
    after := leaf.after++[nextSite]
    schedule := by
      have same := congrArg (fun xs : List Path=>xs++[nextSite]) leaf.schedule
      exact same.trans (by simp only [List.append_assoc,List.cons_append]) }

/-- The actual operational spine produces its safe leaf, its complete local
word formula (including overlaps), and the exact accumulated continuation. -/
theorem DirectedMarkerSpine.leaf_output
    (spine : DirectedMarkerSpine F source degree forward ps target beforeLabels edge)
    (currentLookup : target.subterm edge=some current) :
    Nonempty (DirectedMarkerLeafOutput F source degree forward ps (current.label.readLetters forward)) := by
  induction spine generalizing current with
  | inherited event lookup oldLookup origin uncreated same earlier ih =>
    have equal := Option.some.inj (lookup.symm.trans currentLookup)
    cases equal
    rw [same]
    obtain ⟨leaf⟩ := ih oldLookup
    exact ⟨leaf.snoc _⟩
  | safe event reading lookup origin segment beforeEq beforeSafe firstLookup firstSafe lastLookup lastSourceLookup lastTrace =>
    have equal := Option.some.inj (lookup.symm.trans currentLookup)
    cases equal
    obtain ⟨firstNode,lastNode,marker,firstAt,lastAt,marks,formula⟩ :=
      origin.directed_label_decomposition event.turn event.redex reading lookup
    have firstEq := Option.some.inj (firstAt.symm.trans firstLookup)
    have lastEq := Option.some.inj (lastAt.symm.trans lastLookup)
    subst firstNode
    subst lastNode
    exact ⟨{
      pre := _
      middle := _
      target := _
      site := _
      event := event
      after := []
      schedule := rfl
      edge := _
      reader := _
      oldReader := _
      first := _
      last := _
      current := _
      firstNode := _
      lastNode := _
      reading := reading
      origin := origin
      lookup := lookup
      firstLookup := firstLookup
      lastLookup := lastLookup
      firstSafe := firstSafe
      lastSourcePosition := _
      lastSourceNode := _
      lastSourceLookup := lastSourceLookup
      lastTrace := lastTrace
      marker := marker
      marks := marks
      formula := formula
      continuation := []
      equation := (List.append_nil _).symm }⟩
  | marked event reading lookup origin segment beforeEq beforeSafe firstLookup firstMarked lastLookup lastSourceLookup lastTrace earlier ih =>
    have equal := Option.some.inj (lookup.symm.trans currentLookup)
    cases equal
    obtain ⟨leaf⟩ := ih firstLookup
    obtain ⟨firstNode,lastNode,marker,rest,firstAt,lastAt,marks,equation⟩ :=
      origin.directed_label_prefix event.turn event.redex reading lookup
    have firstEq := Option.some.inj (firstAt.symm.trans firstLookup)
    subst firstNode
    rw [equation]
    exact ⟨(leaf.extend (marker::rest)).snoc _⟩

#print axioms DirectedMarkerLeafOutput.extend
#print axioms DirectedMarkerLeafOutput.snoc
#print axioms DirectedMarkerSpine.leaf_output
end Lamping.Lambda.Labelled

namespace Lamping.Lambda.Marked
open Labelled
/-- A public producer from the actual uniform OLD history and actual unsafe
reading. The caller supplies neither a spine nor a chosen leaf or marker. -/
theorem RelativeOldHistory.earliest_marker_leaf_output
    {F ps : List Path} {source target current : LTerm} {n : Marked} {degree : Label}
    (old : RelativeOldHistory F ps (mark F source.erase) n)
    (labels : Labelled.History ps source target)
    (selected : ∀ name∈F,source.degreeAt name=some degree)
    (sourceSafe : source.OuterBarsSafe (fun x=>x≠degree))
    (segment : PrerequisitePrefix target start before middle)
    (reading : PrerequisiteReadsDirected target middle edge forward)
    (lookup : target.subterm edge=some current)
    (marked : ¬current.label.OuterBarsSafe (fun x=>x≠degree))
    (safeBefore : ∀ e∈before,∀ node,target.subterm e=some node →node.label.OuterBarsSafe (fun x=>x≠degree)) :
    Nonempty (DirectedMarkerLeafOutput F source degree forward ps (current.label.readLetters forward)) :=
  (old.directed_marker_spine labels selected sourceSafe segment reading lookup marked safeBefore).leaf_output lookup
#print axioms RelativeOldHistory.earliest_marker_leaf_output
end Lamping.Lambda.Marked
