import Lamping.Lamping.FiniteAuxExposureWorker
import Lamping.Lamping.EmptyBetaNeeded
import Lamping.Lamping.BetaFiberFamilies
import Lamping.Lamping.ReachableJointRepresentation
import Lamping.Lambda.FiniteSelections

namespace Lamping.AG.ExposureScheduling
open Graph Lambda Lambda.Labelled Readback
section
variable {B : Type} [FiniteNames B] [DecidableEq B]
variable {source : ExecutableNet B} {root : B} {term : Term}
variable {redex : RedexOcc term} {directions : B → Bool}

private theorem FiniteAuxExposure.betaIndices
    (exposed : FiniteAuxExposure source root term redex directions) :
    exposed.access.connection.appIndex=exposed.access.connection.lamIndex := by
  obtain ⟨depths,_zero,⟨balance⟩⟩ := exposed.domain.balanced
  exact empty_beta_recipe_index_eq exposed.target exposed.access
    (show Nonempty (LevelBalance exposed.target.graph.net depths) from ⟨balance.toLevelBalance⟩)
    exposed.emptyWord

/-- Construct the final beta from the actual zero-control occurrence.
The root balance supplies only a proof of index equality. -/
def FiniteAuxExposure.betaRecipe (exposed : FiniteAuxExposure source root term redex directions) :
    ExplicitRewriteRecipe exposed.target (.beta exposed.access.connection.appIndex) :=
  empty_beta_recipe_with_index_eq exposed.target exposed.access exposed.betaIndices exposed.emptyWord

/-- The final beta is the same physical recipe on the retained program result. -/
def FiniteAuxExposure.programBetaRecipe (exposed : FiniteAuxExposure source root term redex directions) :
    ExplicitRewriteRecipe exposed.program.result (.beta exposed.access.connection.appIndex) :=
  exposed.programResult.symm ▸ exposed.betaRecipe

theorem FiniteAuxExposure.betaRecipe_member
    (exposed : FiniteAuxExposure source root term redex directions) :
    redex.val∈exposed.betaRecipe.site.betaSyntaxFiber root term := by
  obtain ⟨_depths,_zero,⟨balance⟩⟩ := exposed.domain.balanced
  have member := empty_beta_recipe_fiber_member exposed.target exposed.access
    balance.toLevelBalance exposed.emptyWord
  rw [empty_beta_recipe_eq_with_index_eq exposed.target exposed.access balance.toLevelBalance
    exposed.betaIndices exposed.emptyWord] at member
  exact member
end

section
variable {original current : LTerm} [DecidableEq (Boundary original.erase)]
variable {source : ExecutableNet (Boundary original.erase)}
variable {directions : Boundary original.erase → Bool}
variable {redex : RedexOcc current.erase}

/-- The exact final beta fibre is the requested representative's whole
historical family, measured from the same original INIT. -/
theorem exposedBetaFiber_iff_requestedFamily
    (exposed : FiniteAuxExposure source (.inl ()) current.erase redex directions)
    (initial : INIT original) (originalClosed : Closed original.erase)
    {schemas : List Schema} {raw : ParallelHistory original.erase current.erase}
    (actual : LabelledGraphProjection (ActualNet.initial original.erase)
      exposed.target.graph (.inl ()) schemas original current raw)
    (prior : ParallelHistory original.erase current.erase)
    (sameDerivation : raw.derivation=prior.derivation)
    (candidate : RedexOcc current.erase) :
    candidate.val∈exposed.betaRecipe.site.betaSyntaxFiber (.inl ()) current.erase ↔
      FamilyEq ⟨current.erase,prior,redex⟩ ⟨current.erase,prior,candidate⟩ := by
  have closed := actual.label_history.closed originalClosed
  have history : History prior.derivation.paths original current := by
    rw [←sameDerivation]
    exact actual.label_history
  let matching := exposed.domain.matching
  let recipe := exposed.betaRecipe
  obtain ⟨selection⟩ := matching.occurrence_fragment_selection closed
  have joint := actual.initial_joint_representation initial originalClosed selection
  have siteMatching := recipe.sourceIso.matches matching
  obtain ⟨siteSelection⟩ := siteMatching.occurrence_fragment_selection closed
  have siteRepresentation : ChainRepresentationInvariant closed siteSelection := by
    intro p q left right first second
    exact (recipe.sourceIso.chain_representation matching selection siteSelection first second).trans
      (joint.1 first second)
  exact recipe.site.beta_fiber_iff_historical_family initial closed prior history
    siteMatching siteSelection siteRepresentation redex exposed.betaRecipe_member candidate

/-- A given complete family step at the maintained prefix selects exactly
the same paths as the actual beta fibre, in membership rather than list order. -/
theorem exposedBetaFiber_iff_givenSelection {F : List Path} {next : Term}
    (exposed : FiniteAuxExposure source (.inl ()) current.erase redex directions)
    (initial : INIT original) (originalClosed : Closed original.erase)
    {schemas : List Schema} {raw : ParallelHistory original.erase current.erase}
    (actual : LabelledGraphProjection (ActualNet.initial original.erase)
      exposed.target.graph (.inl ()) schemas original current raw)
    (prior : ParallelHistory original.erase current.erase)
    (sameDerivation : raw.derivation=prior.derivation)
    (given : ParallelStep F current.erase next) (family : CompleteFamilyStep prior given)
    (requested : redex.val∈F) (p : Path) :
    p∈exposed.betaRecipe.site.betaSyntaxFiber (.inl ()) current.erase ↔ p∈F := by
  constructor
  · intro member
    have physical := (mem_physicalBetaFiberPaths exposed.betaRecipe.site.net (.inl ())
      current.erase (.inr (.inl ())) (.inr (.inr ())) p).mp member
    obtain ⟨candidate,_access,path,_app,_lam⟩ := physical
    have related := (exposedBetaFiber_iff_requestedFamily exposed initial originalClosed actual
      prior sameDerivation candidate).mp (path.symm ▸ member)
    exact path ▸ family.maximal redex candidate requested related
  · intro member
    let candidate : RedexOcc current.erase := ⟨p,family.1 p member⟩
    exact (exposedBetaFiber_iff_requestedFamily exposed initial originalClosed actual
      prior sameDerivation candidate).mpr (family.same_family redex candidate requested member)

/-- One prescribed complete-family stage is replayed at the actual final beta
site. Equality of selections gives equality with the prescribed target. -/
theorem exposedBetaReplay_givenStage {F : List Path} {next : Term}
    (exposed : FiniteAuxExposure source (.inl ()) current.erase redex directions)
    (initial : INIT original) (originalClosed : Closed original.erase)
    {schemas : List Schema} {raw : ParallelHistory original.erase current.erase}
    (actual : LabelledGraphProjection (ActualNet.initial original.erase)
      exposed.target.graph (.inl ()) schemas original current raw)
    (prior : ParallelHistory original.erase current.erase)
    (sameDerivation : raw.derivation=prior.derivation)
    (given : ParallelStep F current.erase next) (family : CompleteFamilyStep prior given)
    (requested : redex.val∈F) :
    ∃ target : LTerm, ∃ replay : ParallelStep
      (exposed.betaRecipe.site.betaSyntaxFiber (.inl ()) current.erase) current.erase target.erase,
      LabelledGraphEvent (.beta exposed.access.connection.appIndex) exposed.target.graph
        exposed.betaRecipe.target.graph (.inl ()) current target (.single replay) ∧
      History replay.paths current target ∧ target.erase=next ∧
      Matches exposed.betaRecipe.target.graph.net (.inl ()) next := by
  let recipe := exposed.betaRecipe
  let domain := exposed.domain
  obtain ⟨flow⟩ := domain.flow
  obtain ⟨depths,rootDepth,⟨balance⟩⟩ := domain.balanced
  have closed := actual.label_history.closed originalClosed
  obtain ⟨paths,marked,target,complete,labels,erased,matching⟩ :=
    recipe.site.beta_labelled_projection closed (recipe.sourceIso.matches domain.matching)
      (recipe.sourceIso.rootInputs domain.inputs) (recipe.sourceIso.flowBalance flow)
      domain.positive (recipe.sourceIso.indexed_balance balance) rootDepth
      (recipe.sourceIso.transparency domain.transparent)
  let replay : ParallelStep (recipe.site.betaSyntaxFiber (.inl ()) current.erase)
      current.erase target.erase := ⟨paths,marked,complete,erased.symm⟩
  have endpoint : target.erase=next := replay.endpoint_selection given
    (exposedBetaFiber_iff_givenSelection exposed initial originalClosed actual prior
      sameDerivation given family requested)
  exact ⟨target,replay,.beta recipe.kept recipe.site recipe.sourceIso (.refl _) complete labels
    erased.symm,labels,endpoint,endpoint ▸ matching⟩
end
end Lamping.AG.ExposureScheduling
