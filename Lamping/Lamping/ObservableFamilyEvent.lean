import Lamping.Lamping.LabelledEventSemantics
import Lamping.Lamping.BetaFiberFamilies
import Lamping.Lamping.JointRepresentationTransport
import Lamping.Lambda.ObservableHistory

namespace Lamping.AG
open Graph Lambda Lambda.Labelled

section
variable {B : Type} [FiniteNames B]

/-- A single actual event extends an ALREADY complete historical prefix,
conditionally on its source chain REP. Empty physical beta fibers and all
auxiliary events are silent; nonempty fibers retain the event's exact OLD
schedule and form a whole family relative to the original INIT history.
No reachable-REP assertion or general completion principle is assumed in
the graph/event definitions or proved by this conditional theorem. -/
theorem LabelledGraphEvent.observable_complete_extension
    {s : Schema} {g h : ActualNet B} {root : B} {original source target : LTerm}
    {raw : ParallelHistory source.erase target.erase}
    (event : LabelledGraphEvent s g h root source target raw)
    (initial : INIT original) (closed : Closed source.erase)
    (prior : ParallelHistory original.erase source.erase)
    (history : History prior.derivation.paths original source)
    (completePrior : CompleteDerivation prior)
    (matching : Matches g.net root source.erase)
    (selection : OccurrenceFragmentSelection source g.net root)
    (representation : ChainRepresentationInvariant closed selection) :
    ∃ observed : ParallelHistory source.erase target.erase,
      ParallelHistory.Observable observed ∧ raw.derivation=observed.derivation ∧
      PermEq raw observed ∧ CompleteDerivation (prior.append observed) := by
  cases event with
  | auxiliary _ _ =>
    exact ⟨.nil _,.nil _,rfl,.refl _,by simpa only [ParallelHistory.append_nil] using completePrior⟩
  | beta kept site before after complete labels erased =>
    by_cases empty : site.betaSyntaxFiber root source.erase=[]
    · have emptyPaths : _=[] :=
        (redexFiber_complete_empty_endpoint complete empty).1
      rw [emptyPaths] at labels
      cases labels
      let step : ParallelStep (site.betaSyntaxFiber root source.erase) source.erase source.erase :=
        ⟨_,_,complete,erased⟩
      refine ⟨.nil _,.nil _,?_,?_,?_⟩
      · apply Derivation.ext
        simpa only [ParallelHistory.single_derivation,ParallelStep.derivation,
          ParallelHistory.derivation,Derivation.nil] using emptyPaths
      · exact PermEq.empty_of_selection step empty
      · simpa only [ParallelHistory.append_nil] using completePrior
    · have siteMatching := before.matches matching
      obtain ⟨siteSelection⟩ := siteMatching.occurrence_fragment_selection closed
      have siteRepresentation : ChainRepresentationInvariant closed siteSelection := by
        intro p q left right first second
        exact (before.chain_representation matching selection siteSelection first second).trans
          (representation first second)
      let step : ParallelStep (site.betaSyntaxFiber root source.erase) source.erase target.erase :=
        ⟨_,_,complete,erased⟩
      exact ⟨.single step,.cons empty (.nil _),rfl,.refl _,
        site.beta_extend_complete_derivation initial closed prior history completePrior
          siteMatching siteSelection siteRepresentation empty step⟩

end
end Lamping.AG
