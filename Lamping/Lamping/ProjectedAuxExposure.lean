import Lamping.Lamping.FiniteAuxExposureWorker
import Lamping.Lamping.LabelledTraceProjection
import Lamping.Lambda.ClosedVariableBinders

namespace Lamping.AG
open Graph Lambda Lambda.Labelled Readback ExposureScheduling

section
variable {B : Type} [FiniteNames B]

private theorem eventIsoSource {g h k : ActualNet B} {root : B} {schema : Schema}
    {initial current : LTerm} {history : ParallelHistory initial.erase current.erase}
    (iso : NetIso g.net h.net) (event : LabelledGraphEvent schema h k root initial current history) :
    LabelledGraphEvent schema g k root initial current history := by
  cases event with
  | auxiliary step notBeta => exact .auxiliary (step.iso_source iso) notBeta
  | beta kept site before after complete labels erased =>
    exact .beta kept site (iso.trans before) after complete labels erased

/-- Append the actual event without replacing either labelled schedule. -/
theorem LabelledGraphProjection.snoc_event {g h k : ActualNet B} {root : B}
    {schemas : List Schema} {schema : Schema}
    {original current target : LTerm}
    {history : ParallelHistory original.erase current.erase}
    {step : ParallelHistory current.erase target.erase}
    (earlierProjection : LabelledGraphProjection g h root schemas original current history)
    (event : LabelledGraphEvent schema h k root current target step) :
    LabelledGraphProjection g k root (schemas++[schema]) original target (history.append step) := by
  induction earlierProjection with
  | iso same =>
    simpa only [List.nil_append,ParallelHistory.append,ParallelHistory.append_nil] using
      LabelledGraphProjection.cons (eventIsoSource same event) (.iso (.refl _))
  | cons first rest ih =>
    simpa only [List.cons_append,ParallelHistory.append_assoc] using
      LabelledGraphProjection.cons first (ih event)
end

/-- An auxiliary trace retains the same labelled term and contributes no
parallel syntax step. -/
theorem GraphTrace.labelled_auxiliary_projection {B : Type} [FiniteNames B]
    {g h : ActualNet B} {schemas : List Schema} (trace : GraphTrace g h schemas)
    (auxOnly : ∀ s∈schemas, ∀ i, s≠.beta i) (root : B) (current : LTerm) :
    LabelledGraphProjection g h root schemas current current (.nil current.erase) := by
  induction trace with
  | iso same => exact .iso same
  | cons step rest ih =>
    exact .cons (.auxiliary step (auxOnly _ List.mem_cons_self))
      (ih (fun s member => auxOnly s (List.mem_cons_of_mem _ member)))

/-- Append the actual auxiliary trace to the given original projection,
keeping both labelled endpoints and its original parallel history. -/
theorem LabelledGraphProjection.append_auxiliary {B : Type} [FiniteNames B]
    {g h final : ActualNet B} {root : B} {schemas extra : List Schema}
    {initial current : LTerm} {history : ParallelHistory initial.erase current.erase}
    (original : LabelledGraphProjection g h root schemas initial current history)
    (suffix : GraphTrace h final extra) (auxOnly : ∀ s∈extra, ∀ i, s≠.beta i) :
    LabelledGraphProjection g final root (schemas++extra) initial current history := by
  induction original with
  | @iso _g _h indexedRoot indexedSource same =>
    simpa only [List.nil_append] using
      (suffix.iso_source same).labelled_auxiliary_projection auxOnly indexedRoot indexedSource
  | cons event rest ih =>
    exact .cons event (ih suffix)

namespace ExposureScheduling

/-- The ordinary redex occurrence determines the labelled redex shape by
erasure of the literal lookup at that same path. -/
theorem labelledExposureOccurrence_of_redex (current : LTerm) (closed : Closed current.erase)
    (redex : RedexOcc current.erase) : LabelledExposureOccurrence current.erase redex := by
  obtain ⟨bare,lookup,redexShape⟩ := redex.property
  rw [←LTerm.erase_subterm] at lookup
  obtain ⟨labelled,atPath,erased⟩ := Option.map_eq_some_iff.mp lookup
  subst bare
  refine ⟨current,rfl,closed,?_⟩
  cases labelled with
  | var stamp index => simp [LTerm.erase,IsRedex] at redexShape
  | lam stamp body => simp [LTerm.erase,IsRedex] at redexShape
  | app appStamp fn arg =>
    cases fn with
    | var stamp index => simp [LTerm.erase,IsRedex] at redexShape
    | app stamp first second => simp [LTerm.erase,IsRedex] at redexShape
    | lam lamStamp body => exact ⟨appStamp,lamStamp,body,arg,atPath⟩

section
variable {B : Type} [FiniteNames B] [DecidableEq B]
variable {root : B} {directions : B → Bool}

/-- The executable worker starts from the same original labelled history,
whose closed source gives the proof-only current redex witness. -/
def exposeProjectedOccurrence (source : ExecutableNet B) {initial current : LTerm}
    {history : ParallelHistory initial.erase current.erase}
    (closed : Closed initial.erase) (labels : History history.derivation.paths initial current)
    (domain : AuxExposureDomain source.graph root current.erase directions)
    (redex : RedexOcc current.erase) :
    FiniteAuxExposure source root current.erase redex directions :=
  finiteAuxExposure redex (labelledExposureOccurrence_of_redex current (labels.closed closed) redex)
    source domain

theorem exposeProjectedOccurrence_projection (source : ExecutableNet B)
    {origin : ActualNet B} {schemas : List Schema} {initial current : LTerm}
    {history : ParallelHistory initial.erase current.erase}
    (original : LabelledGraphProjection origin source.graph root schemas initial current history)
    (closed : Closed initial.erase) (labels : History history.derivation.paths initial current)
    (domain : AuxExposureDomain source.graph root current.erase directions)
    (redex : RedexOcc current.erase) :
    let exposed := exposeProjectedOccurrence source closed labels domain redex
    LabelledGraphProjection origin exposed.target.graph root (schemas++exposed.schemas)
      initial current history := by
  let exposed := exposeProjectedOccurrence source closed labels domain redex
  exact original.append_auxiliary exposed.trace exposed.auxOnly
end
end ExposureScheduling
end Lamping.AG
