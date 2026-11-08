import Lamping.Lamping.RecentSpineFarOrigins
import Lamping.Lamping.SameEventForwardHeads

namespace Lamping.Lambda.Labelled

private theorem paired_after
    (step : StepAt site source target) (other : StepAt site otherSource otherTarget)
    (same : source.erase=otherSource.erase) : target.erase=otherTarget.erase := by
  have bare : BetaAt otherSource.erase site target.erase := by rw [←same];exact step.betaAt
  obtain ⟨candidate,lifted,erased⟩ := lift_betaAt bare
  rw [lifted.deterministic other] at erased
  exact erased.symm

/-- Actual uncreated ancestry is unchanged by reannotation along the SAME
schedule. No incoming safety or representation premise is needed. -/
theorem UncreatedNodeHistoryPreimage.reannotate
    {source target otherSource otherTarget : LTerm} {ps : List Path}
    {labels : History ps source target} {otherLabels : History ps otherSource otherTarget}
    (same : source.erase=otherSource.erase)
    (trace : UncreatedNodeHistoryPreimage labels edge oldEdge) :
    UncreatedNodeHistoryPreimage otherLabels edge oldEdge := by
  induction trace generalizing otherSource otherTarget with
  | nil => cases otherLabels;exact .nil _ _
  | @one site ps source middle target body argument beta alpha edge mid oldEdge step remaining redex origin uncreated tail ih =>
    cases otherLabels with
    | cons otherStep otherRemaining =>
      have midSame := paired_after step otherStep same
      have localTail := ih (otherLabels:=otherRemaining) midSame
      obtain ⟨ob,oa,otherBody,otherArgument,otherRedex,_contractum⟩ := otherStep.head_lookups
      have heads := congrArg (fun t=>subtermAt t site) same
      simp only [←LTerm.erase_subterm,redex,otherRedex,Option.map_some,LTerm.erase] at heads
      have parts := Term.app.inj (Option.some.inj heads)
      have bodySame := Term.lam.inj parts.1
      have localOrigin := origin.reannotate bodySame parts.2
      have localUncreated := fun created=>uncreated ((betaCreatedIncoming_of_same_erase bodySame).mpr created)
      exact .one (step:=otherStep) otherRedex localOrigin localUncreated localTail

private theorem uncreated_append
    {source middle target : LTerm}
    {firstHistory : History ps source middle} {lastHistory : History qs middle target}
    (first : UncreatedNodeHistoryPreimage firstHistory middleEdge oldEdge)
    (last : UncreatedNodeHistoryPreimage lastHistory edge middleEdge) :
    UncreatedNodeHistoryPreimage (firstHistory.append lastHistory) edge oldEdge := by
  induction first with
  | nil => exact last
  | @one _ _ _ _ _ _ _ _ _ _ _ _ step _ redex origin uncreated tail ih =>
    exact .one (step:=step) redex origin uncreated (ih last)

namespace SpineIncidenceProvenance
variable {F : List Path} {source : LTerm} {degree : Label} {forward : Bool}
variable {ps : List Path} {target current : LTerm} {beforeLabels : List (Option Label)} {edge : Path}
variable {spine : DirectedMarkerSpine F source degree forward ps target beforeLabels edge}
variable {lookup : target.subterm edge=some current}
variable {leaf : DirectedMarkerLeafOutput F source degree forward ps (current.label.readLetters forward)}
variable {snapshot : IncomingIncidenceSnapshot target edge}

/-- A single actual creation has only uncreated inherited turns after its
safe base leaf. This is stronger than merely having an actual suffix. -/
theorem single_creation_suffix
    (geometry : SpineIncidenceProvenance F source degree forward spine lookup leaf snapshot)
    (single : geometry.creationFrames.length=1) :
    leaf.continuation=[] ∧
      UncreatedNodeHistoryPreimage geometry.actual_suffix edge leaf.edge := by
  induction geometry with
  | inherited event lookup oldLookup origin uncreated same earlier earlierGeometry snap transport ih =>
    have earlierSingle : earlierGeometry.creationFrames.length=1 := by
      simpa only [creationFrames] using single
    obtain ⟨continuation,trace⟩ := ih earlierSingle
    refine ⟨continuation,?_⟩
    exact uncreated_append trace (.one (step:=event.turn) event.redex origin uncreated (.nil _ _))
  | safe => exact ⟨rfl,.nil _ _⟩
  | marked event reading lookup origin segment beforeEq beforeSafe firstLookup firstMarked lastLookup lastSourceLookup lastTrace earlier earlierGeometry equation marks formula snap frame ih =>
    obtain ⟨packet,tail,frames,_⟩ := earlierGeometry.base_frame_coordinates
    have sizes := congrArg List.length frames
    simp only [creationFrames,List.length_append,List.length_cons,List.length_nil] at single sizes
    omega
end SpineIncidenceProvenance

#print axioms UncreatedNodeHistoryPreimage.reannotate
#print axioms SpineIncidenceProvenance.single_creation_suffix
end Lamping.Lambda.Labelled
