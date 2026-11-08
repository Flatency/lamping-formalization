import Lamping.Lamping.ComputedGivenFamilyStage
import Lamping.Lambda.CompleteFamilies

namespace Lamping.AG.ExposureScheduling
open Graph Lambda Lambda.Labelled Readback

variable {original : LTerm} [DecidableEq (Boundary original.erase)]
variable {directions : Boundary original.erase → Bool}

/-- Verification of a prescribed finite derivation. The actual graph and
labelled schedule are those of the successive computed stages. -/
theorem finiteGivenFamilyReplay
    (source : ExecutableNet (Boundary original.erase))
    (initialGraph : source.graph = ActualNet.initial original.erase)
    (initial : INIT original) (closed : Closed original.erase)
    (initialDomain : AuxExposureDomain source.graph (.inl ()) original.erase directions)
    {final : Term} {requested : ParallelHistory original.erase final}
    (complete : CompleteDerivation requested) :
    ∃ (target : ExecutableNet (Boundary original.erase)) (current : LTerm)
      (schemas : List Schema) (raw : ParallelHistory original.erase current.erase)
      (endpoint : current.erase=final),
      LabelledGraphProjection (ActualNet.initial original.erase) target.graph
        (.inl ()) schemas original current raw ∧
      PermEq (endpoint ▸ raw) requested ∧
      AuxExposureDomain target.graph (.inl ()) final directions := by
  induction complete with
  | nil =>
    refine ⟨source,original,[],.nil original.erase,rfl,?_,PermEq.refl _,initialDomain⟩
    rw [initialGraph]
    exact .iso (.refl _)
  | step _ family ih =>
    obtain ⟨graph,current,schemas,raw,endpoint,projection,permutation,domain⟩ := ih
    cases endpoint
    let exposed := computeGivenFamilyExposure graph domain family
      (fun r => labelledExposureOccurrence_of_redex current (projection.label_history.closed closed) r)
    obtain ⟨target,actualNext,endpoint,nextProjection,nextPermutation,nextDomain⟩ :=
      computedGivenFamilyStage graph initial closed projection domain _ permutation _ family
    exact ⟨exposed.betaRecipe.target,target,
      (schemas++exposed.schemas)++[.beta exposed.access.connection.appIndex],
      actualNext,endpoint,nextProjection,nextPermutation,nextDomain⟩

end Lamping.AG.ExposureScheduling
