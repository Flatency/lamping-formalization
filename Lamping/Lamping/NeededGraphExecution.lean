import Lamping.Lamping.NeededGraphOuter

namespace Lamping.AG.Readback
open Graph Lambda Lambda.Labelled ExposureScheduling

private theorem auxiliary_kind (s : Schema) (noBeta : ∀ i, s ≠ .beta i) :
    IsCancellation s ∨ IsAction s := by
  cases s with
  | beta i => exact False.elim (noBeta i rfl)
  | fanCancel i => exact .inl (.fan i)
  | croCancel i => exact .inl (.cro i)
  | braCancel i => exact .inl (.bra i)
  | fanAction op i j lt => exact .inr (.fan op i j lt)
  | croAction op i j lt => exact .inr (.cro op i j lt)
  | braAction op i j lt => exact .inr (.bra op i j lt)

section
variable {original : LTerm} [DecidableEq (Boundary original.erase)]

private theorem round_update {current : LTerm}
    (initial : INIT original) (closed : Closed original.erase)
    {source : ExecutableNet (Boundary original.erase)} {schemas : List Schema}
    {raw prior : ParallelHistory original.erase current.erase}
    (actual : LabelledGraphProjection (ActualNet.initial original.erase)
      source.graph (.inl ()) schemas original current raw)
    (same : raw.derivation = prior.derivation)
    (complete : CompleteDerivation prior) (needful : CallByNeedHistory prior)
    (domain : AuxExposureDomain source.graph (.inl ()) current.erase initialBoundaryPolarity)
    {redex : RedexOcc current.erase} (lo : loRedex current.erase = some redex.val)
    (exposed : FiniteAuxExposure source (.inl ()) current.erase redex initialBoundaryPolarity) :
    let target := (selectedRoundBeta exposed).target
    ∃ valid : StrategyGraphInvariant original target,
      NeededParallelNext (target.readback (.inl ()) valid.readbackDomain) current.erase := by
  let recipe := selectedRoundBeta exposed
  obtain ⟨depths, rootDepth, balance⟩ := domain.balanced
  obtain ⟨target, step, event, nextComplete, nextNeedful, targetReadback, decreases⟩ :=
    exposed_beta_extend_strategy_prior source exposed.target initial closed actual exposed.trace
      (fun s member => auxiliary_kind s (exposed.auxOnly s member))
      prior same complete needful exposed.access exposed.emptyWord lo domain.flow domain.positive
      balance rootDepth domain.transparent
  have atTarget : LabelledGraphEvent (.beta exposed.access.connection.appIndex)
      exposed.target.graph recipe.target.graph (.inl ()) current target (.single step) := event
  have full := (actual.append_auxiliary exposed.trace exposed.auxOnly).snoc_event atTarget
  have sameNext : (raw.append (.single step)).derivation = (prior.append (.single step)).derivation := by
    rw [ParallelHistory.derivation_append, ParallelHistory.derivation_append, same]
  obtain ⟨exposedFlow⟩ := exposed.domain.flow
  obtain ⟨finalDepths, finalRootDepth, ⟨exposedBalance⟩⟩ := exposed.domain.balanced
  have currentClosed := actual.label_history.closed closed
  have targetMatches := atTarget.target_matches exposedFlow exposed.domain.positive exposedBalance
    finalRootDepth exposed.domain.inputs exposed.domain.transparent exposed.domain.matching currentClosed
  have physical := atTarget.graph_step
  have nextDomain : AuxExposureDomain recipe.target.graph (.inl ()) target.erase initialBoundaryPolarity :=
    ⟨physical.rootInputs exposedFlow exposed.domain.positive exposedBalance finalRootDepth
        exposed.domain.inputs exposed.domain.transparent exposed.domain.matching,
      targetMatches,
      physical.transparency_indexed exposedFlow exposed.domain.positive exposedBalance
        finalRootDepth exposed.domain.transparent,
      physical.flowBalance exposedFlow, exposed.domain.positive,
      finalDepths, finalRootDepth, physical.indexed_balance exposedBalance⟩
  let valid : StrategyGraphInvariant original recipe.target :=
    ⟨target, _, _, _, full, sameNext, nextComplete, nextNeedful, nextDomain⟩
  exact ⟨valid, (show NeededParallelNext (recipe.target.readback (.inl ()) targetReadback) current.erase from
    decreases)⟩

private theorem graph_round_domain (state : NeededGraphState original) :
    AuxExposureDomain state.graph.graph (.inl ()) state.term initialBoundaryPolarity := by
  obtain ⟨current, _, _, _, _, _, _, _, domain⟩ := state.invariant
  have same : state.term = current.erase :=
    state.graph.readback_eq_of_matches (.inl ()) state.invariant.readbackDomain domain.matching
  exact Eq.mp (congrArg (fun term : Term =>
    AuxExposureDomain state.graph.graph (.inl ()) term initialBoundaryPolarity) same.symm) domain

private theorem graph_round_labelled (state : NeededGraphState original)
    (closed : Closed original.erase) (redex : RedexOcc state.term) :
    LabelledExposureOccurrence state.term redex := by
  obtain ⟨current, _, _, _, actual, _, _, _, domain⟩ := state.invariant
  have liftOccurrence (term : Term) (same : term = current.erase)
      (r : RedexOcc term) : LabelledExposureOccurrence term r := by
    subst term
    exact labelledExposureOccurrence_of_redex current (actual.label_history.closed closed) r
  exact liftOccurrence state.term
    (state.graph.readback_eq_of_matches (.inl ()) state.invariant.readbackDomain domain.matching) redex

private def graph_round_exposure (state : NeededGraphState original)
    (closed : Closed original.erase) {p : Path} (hit : loRedex state.term = some p) :
    FiniteAuxExposure state.graph (.inl ()) state.term
      (⟨p, loRedex_sound hit⟩ : RedexOcc state.term) initialBoundaryPolarity :=
  finiteAuxExposure ⟨p, loRedex_sound hit⟩ (graph_round_labelled state closed _)
    state.graph (graph_round_domain state)

private theorem graph_round_update (state : NeededGraphState original)
    (initial : INIT original) (closed : Closed original.erase)
    {p : Path} (hit : loRedex state.term = some p) :
    let target := (selectedRoundBeta (graph_round_exposure state closed hit)).target
    ∃ valid : StrategyGraphInvariant original target,
      NeededParallelNext (target.readback (.inl ()) valid.readbackDomain) state.term := by
  obtain ⟨current, _, _, _, actual, same, complete, needful, domain⟩ := state.invariant
  have transfer (term : Term) (equal : term = current.erase)
      (redex : RedexOcc term) (lo : loRedex term = some redex.val)
      (exposed : FiniteAuxExposure state.graph (.inl ()) term redex initialBoundaryPolarity) :
      ∃ valid : StrategyGraphInvariant original (selectedRoundBeta exposed).target,
        NeededParallelNext ((selectedRoundBeta exposed).target.readback (.inl ()) valid.readbackDomain)
          term := by
    subst term
    exact round_update initial closed actual same complete needful domain lo exposed
  exact transfer state.term
    (state.graph.readback_eq_of_matches (.inl ()) state.invariant.readbackDomain domain.matching)
    ⟨p, loRedex_sound hit⟩ hit (graph_round_exposure state closed hit)

/-- Execute one actual selected round and attach the exact next certificate to
the computed graph. The certificate and decrease proofs are erased. -/
def NeededGraphState.nextOfLO (state : NeededGraphState original)
    (initial : INIT original) (closed : Closed original.erase)
    {p : Path} (hit : loRedex state.term = some p) :
    {next : NeededGraphState original // NeededParallelNext next.term state.term} :=
  let target := (selectedRoundBeta (graph_round_exposure state closed hit)).target
  have valid : StrategyGraphInvariant original target := by
    obtain ⟨valid, _⟩ := graph_round_update state initial closed hit
    exact valid
  have decreases : NeededParallelNext (target.readback (.inl ()) valid.readbackDomain) state.term := by
    obtain ⟨_, strict⟩ := graph_round_update state initial closed hit
    exact strict
  ⟨⟨target, valid, NeededParallelNext.hasNF state.normalizable decreases⟩, decreases⟩

local instance : WellFoundedRelation (NeededGraphState original) :=
  NeededGraphState.order original

/-- Normalize by actual rounds. The recursion only sees an executable graph
and the computed LO result. Termination uses the exact Needed successor. -/
def normalizeNeededGraphState (initial : INIT original) (closed : Closed original.erase)
    (state : NeededGraphState original) : {result : NeededGraphState original // BetaNF result.term} :=
  match hit : loRedex state.term with
  | none => ⟨state, (loRedex_none_iff _).mp hit⟩
  | some _ =>
    let next := state.nextOfLO initial closed hit
    normalizeNeededGraphState initial closed next.val
termination_by state
decreasing_by exact next.property

/-- Closed executable entry from the actual initial encoding and its fixed
INIT labels. The given HasNF is used only to justify termination. -/
def normalizeNeededGraph (term : Term)
    (closed : Closed term) (normalizable : HasNF term) :
    {result : NeededGraphState (initLabels term) // BetaNF result.term} :=
  have closedInitial : Closed (initLabels term).erase := by
    simpa only [erase_initLabels] using closed
  have normalizableInitial : HasNF (initLabels term).erase := by
    simpa only [erase_initLabels] using normalizable
  normalizeNeededGraphState (init_is_INIT term) closedInitial
    (NeededGraphState.initial (initLabels term) closedInitial normalizableInitial)

/-- The graph produced by the closed executable comes with its actual trace
from INIT, the exact complete and Needed projection, and NF readback. -/
theorem normalizeNeededGraph_spec (term : Term)
    (closed : Closed term) (normalizable : HasNF term) :
    let result := (normalizeNeededGraph term closed normalizable).val
    BetaNF result.term ∧
      ∃ (current : LTerm) (schemas : List Schema)
        (raw prior : ParallelHistory (initLabels term).erase current.erase),
        GraphTrace (ActualNet.initial (initLabels term).erase) result.graph.graph schemas ∧
        LabelledGraphProjection (ActualNet.initial (initLabels term).erase) result.graph.graph
          (.inl ()) schemas (initLabels term) current raw ∧
        raw.derivation = prior.derivation ∧ CompleteDerivation prior ∧ CallByNeedHistory prior ∧
        current.erase = result.term := by
  let result := normalizeNeededGraph term closed normalizable
  refine ⟨result.property, ?_⟩
  obtain ⟨current, schemas, raw, prior, actual, same, complete, needful, domain⟩ := result.val.invariant
  exact ⟨current, schemas, raw, prior, actual.graph_trace, actual, same, complete, needful,
    (result.val.graph.readback_eq_of_matches (.inl ()) result.val.invariant.readbackDomain domain.matching).symm⟩

end

#print axioms Lamping.AG.Readback.NeededGraphState.nextOfLO
#print axioms Lamping.AG.Readback.normalizeNeededGraphState
#print axioms Lamping.AG.Readback.normalizeNeededGraph
#print axioms Lamping.AG.Readback.normalizeNeededGraph_spec

end Lamping.AG.Readback
