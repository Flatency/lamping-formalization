import Lamping.Lamping.ComputedTotalAuxRecipe
import Lamping.Lamping.ReadbackActualAccessAt
import Lamping.Lamping.AuxiliaryMatching
import Lamping.Lamping.LabelledGraphEvents

namespace Lamping.AG.ExposureScheduling
open Graph Lambda Lambda.Labelled Readback
section
variable {B : Type} [FiniteNames B]

/-- Invariants used by a same-term auxiliary exposure run. -/
structure AuxExposureDomain (graph : ActualNet B) (root : B)
    (term : Term) (directions : B → Bool) : Prop where
  inputs : RootInputs graph.net root
  matching : Matches graph.net root term
  transparent : Transparency graph.net root
  flow : Nonempty (FlowBalance graph.net directions)
  positive : directions root=true
  balanced : ∃ depths : B → Int, depths root=0 ∧ Nonempty (IndexedLevelBalance graph.net depths)

theorem AuxExposureDomain.readbackDomain {graph : ActualNet B} {root : B}
    {term : Term} {directions : B → Bool} (domain : AuxExposureDomain graph root term directions) :
    ReadbackDomain graph.net root :=
  ⟨domain.inputs,domain.transparent,term,domain.matching⟩

private theorem auxiliaryCases (schema : Schema) (notBeta : ∀ i, schema≠.beta i) :
    IsCancellation schema ∨ IsAction schema := by
  cases schema with
  | beta i => exact False.elim (notBeta i rfl)
  | fanCancel i => exact Or.inl (.fan i)
  | croCancel i => exact Or.inl (.cro i)
  | braCancel i => exact Or.inl (.bra i)
  | fanAction f i j lt => exact Or.inr (.fan f i j lt)
  | croAction f i j lt => exact Or.inr (.cro f i j lt)
  | braAction f i j lt => exact Or.inr (.bra f i j lt)

/-- Preserve the proof-only domain through the actual auxiliary step. -/
theorem AuxExposureDomain.step {g h : ActualNet B} {schema : Schema}
    {root : B} {term : Term} {directions : B → Bool}
    (domain : AuxExposureDomain g root term directions) (step : GraphStep schema g h)
    (notBeta : ∀ i, schema≠.beta i) : AuxExposureDomain h root term directions := by
  obtain ⟨flow⟩ := domain.flow
  obtain ⟨depths,rootDepth,⟨balance⟩⟩ := domain.balanced
  have nextMatching : Matches h.net root term := (auxiliaryCases schema notBeta).elim
    (fun cancel => step.cancellation_matches_rootInputs cancel flow domain.positive
      domain.inputs balance rootDepth domain.transparent domain.matching)
    (fun action => step.action_matches_rootInputs action flow domain.positive
      balance rootDepth domain.inputs domain.transparent domain.matching)
  exact ⟨step.rootInputs flow domain.positive balance rootDepth domain.inputs domain.transparent
    domain.matching, nextMatching,
    step.transparency_indexed flow domain.positive balance rootDepth domain.transparent,
    step.flowBalance flow,domain.positive,depths,rootDepth,step.indexed_balance balance⟩

variable [DecidableEq B]
variable {root : B} {term : Term} {directions : B → Bool}

/-- The evaluator computes the access of the fixed original occurrence. -/
def auxExposureAccess (source : ExecutableNet B)
    (domain : AuxExposureDomain source.graph root term directions) (redex : RedexOcc term) :
    ActualRedexAccess source.graph.net root redex :=
  source.actualAccessAt root domain.readbackDomain domain.matching redex

structure AuxExposureTransition (source : ExecutableNet B) (root : B)
    (term : Term) (redex : RedexOcc term) (directions : B → Bool) where
  schema : Schema
  recipe : ExplicitRewriteRecipe source schema
  notBeta : ∀ i, schema≠.beta i
  domain : AuxExposureDomain recipe.target.graph root term directions

/-- The actual nonempty auxiliary recipe and its target. Only the two equality
algorithms of the source graph are installed for the selector. -/
def auxExposureTransition (source : ExecutableNet B)
    (domain : AuxExposureDomain source.graph root term directions) (redex : RedexOcc term)
    (nonempty : controlWord source.graph.net (auxExposureAccess source domain redex).connection.edges≠[]) :
    AuxExposureTransition source root term redex directions := by
  letI := source.graph.nodesFinite
  letI := source.graph.wiresFinite
  letI := source.nodeEquality
  letI := source.wireEquality
  let selected := selectComputedAuxRecipe (auxExposureAccess source domain redex)
    domain.inputs domain.balanced domain.flow nonempty
  -- The graph in the selector is the very same graph with its carriers exposed.
  exact ⟨selected.schema,selected.recipe,selected.not_beta,
    domain.step selected.recipe.actual_step selected.not_beta⟩

def AuxExposureTransition.targetAccess {source : ExecutableNet B} {redex : RedexOcc term}
    (step : AuxExposureTransition source root term redex directions) :
    ActualRedexAccess step.recipe.target.graph.net root redex :=
  auxExposureAccess step.recipe.target step.domain redex

omit [DecidableEq B] in
/-- The actual auxiliary event retains the supplied current labels. -/
theorem AuxExposureTransition.labelledEvent {source : ExecutableNet B} {current : LTerm}
    {redex : RedexOcc current.erase}
    (step : AuxExposureTransition source root current.erase redex directions) :
    LabelledGraphEvent step.schema source.graph step.recipe.target.graph root
      current current (.nil current.erase) :=
  .auxiliary step.recipe.actual_step step.notBeta

/-- Only the correctness proof uses the labelled redex shape. The successor
access itself is computed on the literal executable target. -/
theorem auxExposureTransition_strict (source : ExecutableNet B) {current : LTerm}
    (domain : AuxExposureDomain source.graph root current.erase directions)
    (redex : RedexOcc current.erase) (closed : Closed current.erase)
    (appStamp lamStamp : Lambda.Labelled.Label) (body arg : LTerm)
    (lookup : current.subterm redex.val=some (.app appStamp (.lam lamStamp body) arg))
    (nonempty : controlWord source.graph.net (auxExposureAccess source domain redex).connection.edges≠[]) :
    let step := auxExposureTransition source domain redex nonempty
    ControlWordDecrease (controlWord step.recipe.target.graph.net step.targetAccess.connection.edges)
      (controlWord source.graph.net (auxExposureAccess source domain redex).connection.edges) := by
  letI := source.graph.nodesFinite
  letI := source.graph.wiresFinite
  letI := source.nodeEquality
  letI := source.wireEquality
  let selected := selectComputedAuxRecipe (auxExposureAccess source domain redex)
    domain.inputs domain.balanced domain.flow nonempty
  let nextDomain := domain.step selected.recipe.actual_step selected.not_beta
  exact selected.fixed_target_decrease domain.matching closed domain.positive domain.transparent
    appStamp lamStamp body arg lookup nextDomain.matching
    (auxExposureAccess selected.recipe.target nextDomain redex)
end
end Lamping.AG.ExposureScheduling
