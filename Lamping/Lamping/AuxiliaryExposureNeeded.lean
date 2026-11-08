import Lamping.Lamping.EmptyBetaStrategyPrior
import Lamping.Lamping.AuxiliaryMatching

namespace Lamping.AG
open Graph Lambda Lambda.Labelled

section
variable {B : Type} [FiniteNames B]

/-- A finite real administrative trace has no labelled syntax boundary. -/
theorem GraphTrace.auxiliary_labelled_same
    {g h : ActualNet B} {schemas : List Schema} (trace : GraphTrace g h schemas)
    (auxiliary : ∀ s ∈ schemas, IsCancellation s ∨ IsAction s)
    (root : B) (term : LTerm) :
    LabelledGraphProjection g h root schemas term term (.nil term.erase) := by
  induction trace with
  | iso same => exact .iso same
  | @cons _ _ _ s _ step _ ih =>
    have notBeta : ∀ i, s ≠ .beta i := by
      intro i equal
      have real := auxiliary s List.mem_cons_self
      rw [equal] at real
      rcases real with cancel | action
      · cases cancel
      · cases action
    exact .cons (.auxiliary step notBeta)
      (ih (fun rule member => auxiliary rule (List.mem_cons_of_mem _ member)))

/-- Append actual exposure to the original raw projection. Even the raw
parallel history remains literally unchanged through these six schemas. -/
theorem LabelledGraphProjection.append_auxiliary_cases
    {g h k : ActualNet B} {root : B} {first rest : List Schema}
    {original term : LTerm} {raw : ParallelHistory original.erase term.erase}
    (earlier : LabelledGraphProjection g h root first original term raw)
    (trace : GraphTrace h k rest)
    (auxiliary : ∀ s ∈ rest, IsCancellation s ∨ IsAction s) :
    LabelledGraphProjection g k root (first ++ rest) original term raw := by
  induction earlier with
  | @iso _g _h indexedRoot indexedSource same =>
    simpa only [List.nil_append] using
      (trace.iso_source same).auxiliary_labelled_same auxiliary indexedRoot indexedSource
  | cons event _tail ih => exact .cons event (ih trace)

end

namespace Readback
open ExposureScheduling

section
variable {B : Type} [FiniteNames B]

/-- Map the reached indexed-balance witness only inside Prop. -/
theorem indexed_balance_level_witness {g : ExecutableNet B} {heights : B → Int}
    (balance : Nonempty (IndexedLevelBalance g.graph.net heights)) :
    Nonempty (LevelBalance g.graph.net heights) := by
  obtain ⟨indexed⟩ := balance
  exact ⟨indexed.toLevelBalance⟩

/-- Execute the proof-only empty-control beta builder at the already returned
exposure endpoint. The actual graph and actual access determine the recipe. -/
def exposedBetaRecipe (exposed : ExecutableNet B) {root : B}
    {term : Term} {redex : RedexOcc term}
    (access : ActualRedexAccess exposed.graph.net root redex)
    {heights : B → Int} (balance : Nonempty (IndexedLevelBalance exposed.graph.net heights))
    (empty : controlWord exposed.graph.net access.connection.edges = []) :
    ExplicitRewriteRecipe exposed (.beta access.connection.appIndex) :=
  empty_beta_recipe_with_index_eq exposed access
    (empty_beta_recipe_index_eq exposed access (indexed_balance_level_witness balance) empty) empty

private theorem exposure_balance {g h : ActualNet B} {schemas : List Schema}
    (trace : GraphTrace g h schemas) {heights : B → Int}
    (balance : Nonempty (IndexedLevelBalance g.net heights)) :
    Nonempty (IndexedLevelBalance h.net heights) := by
  obtain ⟨old⟩ := balance
  exact trace.indexed_balance old

/-- The worker's actual administrative trace and endpoint are sufficient to
assemble a complete Needed strategy round on the exact maintained prior.
Its target is the actual proof-only beta recipe's executable target. -/
theorem exposed_beta_extend_strategy_prior
    {original current : LTerm} [DecidableEq (Boundary original.erase)]
    (source exposed : ExecutableNet (Boundary original.erase))
    (initial : INIT original) (originalClosed : Closed original.erase)
    {schemas auxSchemas : List Schema} {raw : ParallelHistory original.erase current.erase}
    (actual : LabelledGraphProjection (ActualNet.initial original.erase)
      source.graph (.inl ()) schemas original current raw)
    (trace : GraphTrace source.graph exposed.graph auxSchemas)
    (auxiliary : ∀ s ∈ auxSchemas, IsCancellation s ∨ IsAction s)
    (prior : ParallelHistory original.erase current.erase)
    (sameDerivation : raw.derivation = prior.derivation)
    (complete : CompleteDerivation prior) (needful : CallByNeedHistory prior)
    {redex : RedexOcc current.erase}
    (access : ActualRedexAccess exposed.graph.net (.inl ()) redex)
    (empty : controlWord exposed.graph.net access.connection.edges = [])
    (selectedLO : loRedex current.erase = some redex.val)
    {directions : Boundary original.erase → Bool}
    (flow : Nonempty (FlowBalance source.graph.net directions))
    (positive : directions (.inl ()) = true)
    {heights : Boundary original.erase → Int}
    (balance : Nonempty (IndexedLevelBalance source.graph.net heights))
    (rootDepth : heights (.inl ()) = 0) (transparent : Transparency source.graph.net (.inl ())) :
    let recipe := exposedBetaRecipe exposed access (exposure_balance trace balance) empty
    ∃ (target : LTerm)
      (step : ParallelStep (recipe.site.betaSyntaxFiber (.inl ()) current.erase) current.erase target.erase),
      LabelledGraphEvent (.beta access.connection.appIndex) exposed.graph recipe.target.graph (.inl ())
        current target (.single step) ∧
      CompleteDerivation (prior.append (.single step)) ∧
      CallByNeedHistory (prior.append (.single step)) ∧
      ∃ domain : ReadbackDomain recipe.target.graph.net (.inl ()),
        NeededParallelNext (recipe.target.readback (.inl ()) domain) current.erase := by
  dsimp only
  obtain ⟨sourceFlow⟩ := flow
  obtain ⟨sourceBalance⟩ := balance
  obtain ⟨targetFlow⟩ := trace.flowBalance sourceFlow
  obtain ⟨targetBalance⟩ := trace.indexed_balance sourceBalance
  have targetTransparent := trace.transparency_indexed sourceFlow positive sourceBalance rootDepth transparent
  have sameRecipe : exposedBetaRecipe exposed access
        (exposure_balance trace (show Nonempty (IndexedLevelBalance source.graph.net heights) from ⟨sourceBalance⟩)) empty =
      empty_beta_recipe exposed access targetBalance.toLevelBalance empty :=
    (empty_beta_recipe_eq_with_index_eq exposed access targetBalance.toLevelBalance _ empty).symm
  rw [sameRecipe]
  exact empty_beta_recipe_extend_strategy_prior exposed initial originalClosed
    (actual.append_auxiliary_cases trace auxiliary) prior sameDerivation complete needful
    access targetBalance.toLevelBalance empty selectedLO targetFlow positive targetBalance rootDepth targetTransparent

end
end Readback

#print axioms Lamping.AG.GraphTrace.auxiliary_labelled_same
#print axioms Lamping.AG.LabelledGraphProjection.append_auxiliary_cases
#print axioms Lamping.AG.Readback.indexed_balance_level_witness
#print axioms Lamping.AG.Readback.exposedBetaRecipe
#print axioms Lamping.AG.Readback.exposed_beta_extend_strategy_prior

end Lamping.AG
