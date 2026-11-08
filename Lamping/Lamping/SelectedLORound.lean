import Lamping.Lamping.ProjectedAuxExposure
import Lamping.Lamping.AuxiliaryExposureNeeded

namespace Lamping.AG.Readback
open Graph Lambda Lambda.Labelled ExposureScheduling

section
variable {B : Type} [FiniteNames B] [DecidableEq B]
variable {root : B} {directions : B → Bool}

private theorem index_eq_at_exposure {source : ExecutableNet B}
    {term : Term} {redex : RedexOcc term}
    (exposure : FiniteAuxExposure source root term redex directions) :
    exposure.access.connection.appIndex = exposure.access.connection.lamIndex := by
  obtain ⟨_, _, balance⟩ := exposure.domain.balanced
  exact empty_beta_recipe_index_eq exposure.target exposure.access
    (indexed_balance_level_witness balance) exposure.emptyWord

/-- The result uses the worker's actual endpoint and access. The existential
level witness is consumed only by the index-equality proof. -/
def selectedRoundBeta {source : ExecutableNet B} {term : Term} {redex : RedexOcc term}
    (exposure : FiniteAuxExposure source root term redex directions) :
    ExplicitRewriteRecipe exposure.target (.beta exposure.access.connection.appIndex) :=
  empty_beta_recipe_with_index_eq exposure.target exposure.access
    (index_eq_at_exposure exposure) exposure.emptyWord

private def selectedLOExposure (source : ExecutableNet B)
    {original current : LTerm} {raw : ParallelHistory original.erase current.erase}
    (closed : Closed original.erase) (history : History raw.derivation.paths original current)
    (domain : AuxExposureDomain source.graph root current.erase directions)
    {path : Path} (hit : loRedex (source.readback root domain.readbackDomain) = some path) :
    FiniteAuxExposure source root current.erase
      (⟨path, loRedex_sound ((congrArg loRedex
        (source.readback_eq_of_matches root domain.readbackDomain domain.matching)).symm.trans hit)⟩ :
        RedexOcc current.erase) directions :=
  exposeProjectedOccurrence source closed history domain _

/-- One strategy round, computed by P10 readback, LO selection, actual
finite auxiliary exposure, and the proof-only beta builder. -/
def neededGraphNext (source : ExecutableNet B)
    {original current : LTerm} {raw : ParallelHistory original.erase current.erase}
    (closed : Closed original.erase) (history : History raw.derivation.paths original current)
    (domain : AuxExposureDomain source.graph root current.erase directions) :
    Option (ExecutableNet B) :=
  match hit : loRedex (source.readback root domain.readbackDomain) with
  | none => none
  | some _ => some (selectedRoundBeta (selectedLOExposure source closed history domain hit)).target

theorem neededGraphNext_none_iff (source : ExecutableNet B)
    {original current : LTerm} {raw : ParallelHistory original.erase current.erase}
    (closed : Closed original.erase) (history : History raw.derivation.paths original current)
    (domain : AuxExposureDomain source.graph root current.erase directions) :
    neededGraphNext source closed history domain = none ↔
      BetaNF (source.readback root domain.readbackDomain) := by
  rw [← loRedex_none_iff]
  unfold neededGraphNext
  split
  · rename_i hn
    exact ⟨fun _ => hn, fun _ => rfl⟩
  · rename_i p hp
    constructor
    · intro impossible
      cases impossible
    · intro hn
      cases hp.symm.trans hn

end

private theorem isAuxiliary (schema : Schema) (notBeta : ∀ i, schema ≠ .beta i) :
    IsCancellation schema ∨ IsAction schema := by
  cases schema with
  | beta i => exact False.elim (notBeta i rfl)
  | fanCancel i => exact .inl (.fan i)
  | croCancel i => exact .inl (.cro i)
  | braCancel i => exact .inl (.bra i)
  | fanAction op i j lt => exact .inr (.fan op i j lt)
  | croAction op i j lt => exact .inr (.cro op i j lt)
  | braAction op i j lt => exact .inr (.bra op i j lt)

/-- The actual selected round is a complete Needed extension of the literal
maintained prefix. Only the proof refers to the labelled term and history. -/
theorem selected_lo_round_spec {original current : LTerm} [DecidableEq (Boundary original.erase)]
    (source : ExecutableNet (Boundary original.erase))
    (initial : INIT original) (closed : Closed original.erase)
    {schemas : List Schema} {raw : ParallelHistory original.erase current.erase}
    (actual : LabelledGraphProjection (ActualNet.initial original.erase)
      source.graph (.inl ()) schemas original current raw)
    (prior : ParallelHistory original.erase current.erase)
    (sameDerivation : raw.derivation = prior.derivation)
    (complete : CompleteDerivation prior) (needful : CallByNeedHistory prior)
    {directions : Boundary original.erase → Bool}
    (domain : AuxExposureDomain source.graph (.inl ()) current.erase directions)
    {path : Path} (hit : loRedex (source.readback (.inl ()) domain.readbackDomain) = some path) :
    let exposed := selectedLOExposure source closed actual.label_history domain hit
    let recipe := selectedRoundBeta exposed
    neededGraphNext source closed actual.label_history domain = some recipe.target ∧
    ∃ (target : LTerm)
      (step : ParallelStep (recipe.site.betaSyntaxFiber (.inl ()) current.erase) current.erase target.erase),
      LabelledGraphEvent (.beta exposed.access.connection.appIndex) exposed.target.graph
        recipe.target.graph (.inl ()) current target (.single step) ∧
      CompleteDerivation (prior.append (.single step)) ∧ CallByNeedHistory (prior.append (.single step)) ∧
      ∃ targetDomain : ReadbackDomain recipe.target.graph.net (.inl ()),
        NeededParallelNext (recipe.target.readback (.inl ()) targetDomain)
          (source.readback (.inl ()) domain.readbackDomain) := by
  let exposed := selectedLOExposure source closed actual.label_history domain hit
  have sourceTerm := source.readback_eq_of_matches (.inl ()) domain.readbackDomain domain.matching
  have selected : loRedex current.erase = some path := (congrArg loRedex sourceTerm).symm.trans hit
  obtain ⟨depths, rootDepth, balance⟩ := domain.balanced
  have event := exposed_beta_extend_strategy_prior source exposed.target initial closed actual exposed.trace
    (fun rule member => isAuxiliary rule (exposed.auxOnly rule member))
    prior sameDerivation complete needful exposed.access exposed.emptyWord selected
    domain.flow domain.positive balance rootDepth domain.transparent
  constructor
  · unfold neededGraphNext
    split
    · rename_i hn
      cases hit.symm.trans hn
    · rename_i p hp
      have samePath : p = path := Option.some.inj (hp.symm.trans hit)
      subst p
      rfl
  · dsimp only at event ⊢
    obtain ⟨target, step, projected, completeNext, needfulNext, targetDomain, decreases⟩ := event
    refine ⟨target, step, projected, completeNext, needfulNext, targetDomain, ?_⟩
    exact Eq.mp (congrArg (NeededParallelNext _) sourceTerm.symm) decreases

#print axioms Lamping.AG.Readback.selectedRoundBeta
#print axioms Lamping.AG.Readback.neededGraphNext
#print axioms Lamping.AG.Readback.neededGraphNext_none_iff
#print axioms Lamping.AG.Readback.selected_lo_round_spec

end Lamping.AG.Readback
