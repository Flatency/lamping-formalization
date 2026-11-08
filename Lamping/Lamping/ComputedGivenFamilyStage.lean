import Lamping.Lamping.ExposedRequestedFamily
import Lamping.Lamping.ProjectedAuxExposure
import Lamping.Lambda.FiniteFamilySupport
import Lamping.Lambda.ObservableFamilyHistory

namespace Lamping.AG
open Graph Lambda Lambda.Labelled Readback ExposureScheduling
namespace ExposureScheduling

/-- The requested representative is the head of the actual finite
enumeration, filtered by membership in the given whole-family selection. -/
def selectGivenFamilyRepresentative {m t u : Term} {F : List Path}
    {prior : ParallelHistory m t} {given : ParallelStep F t u}
    (family : CompleteFamilyStep prior given) : {r : RedexOcc t // r.val∈F} := by
  cases first : (selectedRedexes t F).head? with
  | none =>
    exact False.elim (by
      obtain ⟨p,member⟩ := List.exists_mem_of_ne_nil _ family.nonempty
      let actual : RedexOcc t := ⟨p,family.1 p member⟩
      have present : actual∈selectedRedexes t F := (mem_selectedRedexes t F actual).mpr member
      rw [List.head?_eq_none_iff.mp first] at present
      exact List.not_mem_nil present)
  | some actual =>
    have present : actual∈selectedRedexes t F := by
      obtain ⟨_tail,split⟩ := List.head?_eq_some_iff.mp first
      rw [split] <;> simp
    exact ⟨actual,(mem_selectedRedexes t F actual).mp present⟩

section
variable {B : Type} [FiniteNames B] [DecidableEq B]
variable {root : B} {directions : B → Bool}
variable {m t u : Term} {F : List Path}
variable {prior : ParallelHistory m t} {given : ParallelStep F t u}

/-- Execute the finite auxiliary exposure for the representative selected
from the given batch. The labelled certificate is a proposition. -/
def computeGivenFamilyExposure (source : ExecutableNet B)
    (domain : AuxExposureDomain source.graph root t directions)
    (family : CompleteFamilyStep prior given)
    (labelled : ∀ r : RedexOcc t, LabelledExposureOccurrence t r) :
    FiniteAuxExposure source root t (selectGivenFamilyRepresentative family).val directions :=
  let r := (selectGivenFamilyRepresentative family).val
  finiteAuxExposure r (labelled r) source domain
end

section
variable {original current : LTerm} [DecidableEq (Boundary original.erase)]
variable {directions : Boundary original.erase → Bool}

/-- One computed stage advances the literal physical projection and the
prescribed prefix in parallel. The prefixes are related by genuine PermEq. -/
theorem computedGivenFamilyStage {F : List Path} {next : Term}
    (source : ExecutableNet (Boundary original.erase))
    (initial : INIT original) (closed : Closed original.erase)
    {schemas : List Schema} {raw : ParallelHistory original.erase current.erase}
    (actual : LabelledGraphProjection (ActualNet.initial original.erase)
      source.graph (.inl ()) schemas original current raw)
    (domain : AuxExposureDomain source.graph (.inl ()) current.erase directions)
    (prior : ParallelHistory original.erase current.erase) (perm : PermEq raw prior)
    (given : ParallelStep F current.erase next) (family : CompleteFamilyStep prior given) :
    let exposed := computeGivenFamilyExposure source domain family
      (fun r => labelledExposureOccurrence_of_redex current (actual.label_history.closed closed) r)
    ∃ (target : LTerm) (actualNext : ParallelHistory original.erase target.erase)
      (endpoint : target.erase=next),
      LabelledGraphProjection (ActualNet.initial original.erase) exposed.betaRecipe.target.graph
        (.inl ()) ((schemas++exposed.schemas)++[.beta exposed.access.connection.appIndex])
        original target actualNext ∧
      PermEq (endpoint ▸ actualNext) (prior.append (.single given)) ∧
      AuxExposureDomain exposed.betaRecipe.target.graph (.inl ()) next directions := by
  let exposed := computeGivenFamilyExposure source domain family
    (fun r => labelledExposureOccurrence_of_redex current (actual.label_history.closed closed) r)
  have projected := actual.append_auxiliary exposed.trace exposed.auxOnly
  have rawFamily := family.prefix_permutation perm.symm
  have requested := (selectGivenFamilyRepresentative family).property
  obtain ⟨target,replay,event,_labels,endpoint,matching⟩ :=
    exposedBetaReplay_givenStage exposed initial closed projected raw rfl given rawFamily requested
  subst next
  have sameSelection := exposedBetaFiber_iff_givenSelection exposed initial closed projected
    raw rfl given rawFamily requested
  have nextPerm := PermEq.comp perm (PermEq.selection replay given sameSelection)
  let beta := exposed.betaRecipe.actual_step
  obtain ⟨flow⟩ := exposed.domain.flow
  obtain ⟨depths,rootDepth,⟨balance⟩⟩ := exposed.domain.balanced
  have targetDomain : AuxExposureDomain exposed.betaRecipe.target.graph (.inl ()) target.erase directions :=
    ⟨beta.rootInputs flow exposed.domain.positive balance rootDepth exposed.domain.inputs
        exposed.domain.transparent exposed.domain.matching,
      matching, beta.transparency_indexed flow exposed.domain.positive balance rootDepth exposed.domain.transparent,
      beta.flowBalance flow, exposed.domain.positive, depths, rootDepth, beta.indexed_balance balance⟩
  exact ⟨target,raw.append (.single replay),rfl,projected.snoc_event event,nextPerm,targetDomain⟩
end
end ExposureScheduling
end Lamping.AG
