import Lamping.Lamping.LabelledEventSemantics
import Lamping.Lamping.BetaAuxiliary
import Lamping.Lamping.JointRepresentationTransport

namespace Lamping.AG
open Graph Lambda Lambda.Labelled

/-- Lift the actual beta event's Aux clause through both real carrier isos.
The source Joint is an induction hypothesis; target Joint is never assumed. -/
theorem LabelledGraphEvent.beta_auxiliary_preserve
    {B : Type} [FiniteNames B]
    {i : Nat} {g h : ActualNet B} {root : B}
    {original source target : LTerm}
    {raw : ParallelHistory source.erase target.erase}
    (event : LabelledGraphEvent (.beta i) g h root source target raw)
    (initial : INIT original)
    (prior : ParallelHistory original.erase source.erase)
    (completePrior : CompleteDerivation prior)
    (prefixHistory : History prior.derivation.paths original source)
    (closed : Closed source.erase)
    {directions : B → Bool} {heights : B → Int}
    (flow : FlowBalance g.net directions) (positive : directions root=true)
    (balance : IndexedLevelBalance g.net heights) (rootDepth : heights root=0)
    (inputs : RootInputs g.net root) (transparent : Transparency g.net root)
    (matching : Matches g.net root source.erase)
    (sourceSelection : OccurrenceFragmentSelection source g.net root)
    (targetSelection : OccurrenceFragmentSelection target h.net root)
    (sourceJoint : JointRepresentation closed sourceSelection) :
    AuxiliarySeparation (event.label_history.closed closed) targetSelection := by
  have targetMatching := event.target_matches flow positive balance rootDepth inputs transparent matching closed
  cases event with
  | auxiliary _ notBeta => exact False.elim (notBeta i rfl)
  | beta kept site before after complete labels erased =>
    have localMatching := before.matches matching
    have localTargetMatching := after.symm.matches targetMatching
    obtain ⟨localSource⟩ := localMatching.occurrence_fragment_selection closed
    obtain ⟨localTarget⟩ := localTargetMatching.occurrence_fragment_selection (labels.closed closed)
    have localJoint := (before.joint_representation matching closed sourceSelection localSource).mpr sourceJoint
    obtain ⟨relative,normal⟩ := (Marked.completeOld_iff _ _).mp complete
    have localAux := site.beta_auxiliary_preserve initial prior completePrior prefixHistory closed
      localMatching (before.rootInputs inputs) (before.flowBalance flow) positive
      (before.indexed_balance balance) rootDepth (before.transparency transparent)
      relative normal labels localSource localTarget localJoint
    change AuxiliarySeparation (labels.closed closed) targetSelection
    intro left right leftAux rightAux same different
    apply localAux left right leftAux rightAux same
    intro equal
    apply different
    exact (after.occurrence_fragment_equality localTargetMatching
      (localTarget left) (targetSelection left) (localTarget right) (targetSelection right)).mpr equal

#print axioms LabelledGraphEvent.beta_auxiliary_preserve
end Lamping.AG
