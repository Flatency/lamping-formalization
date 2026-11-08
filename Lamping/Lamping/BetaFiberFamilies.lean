import Lamping.Lamping.BetaFiberDegrees
import Lamping.Lamping.BetaLabelledProjection
import Lamping.Lambda.LabelFamilyDegreeEquivalence
import Lamping.Lambda.CompleteFamilies
namespace Lamping.AG
open Graph Lambda Lambda.Labelled
section
variable {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K → Graph.Label signature} {i : Nat}
variable (site : PathSite (.beta i) kept (B:=B) (W:=W) (V:=V))

/-- The original INIT and its actual labelled lift are retained. Current
redexes are compared in the SAME supplied historical prefix, without relabelling. -/
theorem PathSite.beta_fiber_iff_historical_family {root : B} {original current : LTerm}
    (initial : INIT original) (closed : Closed current.erase)
    (prior : ParallelHistory original.erase current.erase)
    (history : History prior.derivation.paths original current)
    (matching : Matches site.net root current.erase)
    (selection : OccurrenceFragmentSelection current site.net root)
    (representation : ChainRepresentationInvariant closed selection)
    (representative : RedexOcc current.erase)
    (member : representative.val∈site.betaSyntaxFiber root current.erase)
    (candidate : RedexOcc current.erase) :
    candidate.val∈site.betaSyntaxFiber root current.erase ↔
      FamilyEq ⟨current.erase,prior,representative⟩ ⟨current.erase,prior,candidate⟩ := by
  have family := family_iff_degree original initial
    (⟨current.erase,prior,representative⟩ : RedexWithHistory original.erase)
    (⟨current.erase,prior,candidate⟩ : RedexWithHistory original.erase)
  change FamilyEq ⟨current.erase,prior,representative⟩ ⟨current.erase,prior,candidate⟩ ↔
    degreeAlong original prior.derivation.paths representative.val=
      degreeAlong original prior.derivation.paths candidate.val at family
  rw [degreeAlong_witness history,degreeAlong_witness history] at family
  have physical := site.beta_fiber_iff_degree closed matching selection representation representative member candidate
  exact ⟨fun selected=>family.mpr (physical.mp selected).symm,
    fun related=>physical.mpr (family.mp related).symm⟩

/-- An existing complete development of the SAME ordered physical fiber is
one whole-family step when the fiber is nonempty and REP holds. This proves
family maximality; it does not complete an arbitrary syntax derivation. -/
theorem PathSite.beta_complete_family_step {root : B} {original current : LTerm}
    (initial : INIT original) (closed : Closed current.erase)
    (prior : ParallelHistory original.erase current.erase)
    (history : History prior.derivation.paths original current)
    (matching : Matches site.net root current.erase)
    (selection : OccurrenceFragmentSelection current site.net root)
    (representation : ChainRepresentationInvariant closed selection)
    (positive : site.betaSyntaxFiber root current.erase≠[])
    (step : ParallelStep (site.betaSyntaxFiber root current.erase) current.erase target) :
    CompleteFamilyStep prior step := by
  have valid (p : Path) (member : p∈site.betaSyntaxFiber root current.erase) :
      ∃ term,subtermAt current.erase p=some term ∧IsRedex term := by
    obtain ⟨redex,_source,path,_app,_lam⟩ :=
      (mem_physicalBetaFiberPaths site.net root current.erase (.inr (.inl ())) (.inr (.inr ())) p).mp member
    rw [←path]
    exact redex.property
  obtain ⟨p,member⟩ := List.exists_mem_of_ne_nil _ positive
  let representative : RedexOcc current.erase := ⟨p,valid p member⟩
  refine ⟨valid,representative,member,?_⟩
  intro candidate
  exact site.beta_fiber_iff_historical_family initial closed prior history matching selection representation
    representative member candidate

/-- Extend an ALREADY complete prefix by its actual physical beta fiber.
No general completion or endpoint/permutation assertion is introduced. -/
theorem PathSite.beta_extend_complete_derivation {root : B} {original current : LTerm}
    (initial : INIT original) (closed : Closed current.erase)
    (prior : ParallelHistory original.erase current.erase)
    (history : History prior.derivation.paths original current)
    (complete : CompleteDerivation prior)
    (matching : Matches site.net root current.erase)
    (selection : OccurrenceFragmentSelection current site.net root)
    (representation : ChainRepresentationInvariant closed selection)
    (positive : site.betaSyntaxFiber root current.erase≠[])
    (step : ParallelStep (site.betaSyntaxFiber root current.erase) current.erase target) :
    CompleteDerivation (prior.append (.single step)) :=
  .step complete (site.beta_complete_family_step initial closed prior history matching selection representation positive step)
/-- The SAME actual site and complete OLD-fiber schedule produce a matched
labelled target and one whole historical family step, assuming source REP.
The existential target is constructed on the actual RHS, not freely chosen. -/
theorem PathSite.beta_nonempty_family_projection {root : B} {original current : LTerm}
    (initial : INIT original) (closed : Closed current.erase)
    (prior : ParallelHistory original.erase current.erase)
    (history : History prior.derivation.paths original current)
    (matching : Matches site.net root current.erase) (inputs : RootInputs site.net root)
    {boundary : B → Bool} (flow : FlowBalance site.net boundary) (positiveRoot : boundary root=true)
    {heights : B → Int} (balance : IndexedLevelBalance site.net heights) (rootDepth : heights root=0)
    (transparent : Transparency site.net root)
    (selection : OccurrenceFragmentSelection current site.net root)
    (representation : ChainRepresentationInvariant closed selection)
    (positive : site.betaSyntaxFiber root current.erase≠[]) :
    ∃ next : LTerm,∃ step : ParallelStep (site.betaSyntaxFiber root current.erase) current.erase next.erase,
      History step.paths current next ∧Matches site.reduce root next.erase ∧CompleteFamilyStep prior step := by
  obtain ⟨ps,marked,next,complete,labelled,erased,newMatches⟩ :=
    site.beta_labelled_projection closed matching inputs flow positiveRoot balance rootDepth transparent
  let step : ParallelStep (site.betaSyntaxFiber root current.erase) current.erase next.erase :=
    ⟨ps,marked,complete,erased.symm⟩
  exact ⟨next,step,labelled,newMatches,
    site.beta_complete_family_step initial closed prior history matching selection representation positive step⟩

end
end Lamping.AG
