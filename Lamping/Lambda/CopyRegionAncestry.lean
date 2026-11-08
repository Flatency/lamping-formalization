import Lamping.Lambda.CopyProjection
import Lamping.Lambda.RightSiblingExtraction
import Lamping.Lambda.ExtractionFamilyInvariance
namespace Lamping.Lambda

/-- The actual residual and disjoint generators used in region pruning.
These carry only original rule witnesses, with no Copy conclusion field. -/
inductive PruningStep : ExtractionRun m → ExtractionRun m → Prop where
  | residual (pre : ParallelHistory m t) (ordinary : Atomic pre)
      (R : BetaAt t p u) (S : BetaAt u q v) (S' : BetaAt t q' v')
      (residual : (singleContraction R).derivation.Residual ⟨q',S'.redex⟩ ⟨q,S.redex⟩) :
      PruningStep (.of ((pre.append (.single (singleContraction R))).append (.single (singleContraction S)))
          ((ordinary.append (.single R)).append (.single S)))
        (.of (pre.append (.single (singleContraction S'))) (ordinary.append (.single S')))
  | disjoint (pre : ParallelHistory m t) (ordinary : Atomic pre)
      (R : BetaAt t p u) (σ : ParallelHistory t v) (ha : Atomic σ)
      (τ : ParallelHistory u w) (hb : Atomic τ) (last : ParallelStep F v w)
      (row : StepProjection (singleContraction R) σ τ last) (positive : 0<σ.length)
      (site : Path) (apart : DisjointPositions p site) (inside : Internal site σ) :
      PruningStep (.of ((pre.append (.single (singleContraction R))).append τ)
          ((ordinary.append (.single R)).append hb))
        (.of (pre.append σ) (ordinary.append ha))

inductive Pruning : ExtractionRun m → ExtractionRun m → Prop where
  | refl (r) : Pruning r r
  | cons (step : PruningStep r s) (rest : Pruning s t) : Pruning r t

theorem PruningStep.extraction (step : PruningStep r s) : ExtractionStep r s := by
  cases step with
  | residual pre ordinary R S S' residual => exact .residual pre ordinary R S S' residual
  | disjoint pre ordinary R σ ha τ hb last row positive site apart inside =>
    exact .disjoint pre ordinary R σ ha τ hb last row positive site apart inside

theorem PruningStep.prepend {r s : ExtractionRun t} (step : PruningStep r s)
    (pre : ParallelHistory m t) (ordinary : Atomic pre) :
    PruningStep (r.prepend pre ordinary) (s.prepend pre ordinary) := by
  cases step with
  | residual ρ hρ R S S' residual =>
    simpa only [ExtractionRun.prepend,ExtractionRun.of,ParallelHistory.append_assoc] using
      PruningStep.residual (pre.append ρ) (ordinary.append hρ) R S S' residual
  | disjoint ρ hρ R σ ha τ hb last row positive site apart inside =>
    simpa only [ExtractionRun.prepend,ExtractionRun.of,ParallelHistory.append_assoc] using
      PruningStep.disjoint (pre.append ρ) (ordinary.append hρ) R σ ha τ hb last row positive site apart inside

theorem Pruning.single (step : PruningStep r s) : Pruning r s := .cons step (.refl _)
theorem Pruning.extraction (steps : Pruning r s) : Extraction r s := by
  induction steps with
  | refl r => exact .refl r
  | cons step rest ih => exact .cons step.extraction ih
theorem Pruning.trans (first : Pruning r s) (last : Pruning s t) : Pruning r t := by
  induction first with
  | refl => exact last
  | cons step rest ih => exact .cons step (ih last)
theorem Pruning.prepend {r s : ExtractionRun t} (steps : Pruning r s)
    (pre : ParallelHistory m t) (ordinary : Atomic pre) :
    Pruning (r.prepend pre ordinary) (s.prepend pre ordinary) := by
  induction steps with
  | refl => exact .refl _
  | cons step rest ih => exact .cons (step.prepend pre ordinary) ih

theorem PruningStep.copy {r s : ExtractionRun m} (step : PruningStep r s)
    (a b : RedexWithHistory m) (source : RunRepresents r a) (target : RunRepresents s b) : Copy b a := by
  cases step with
  | residual pre ordinary R S S' residual =>
    let upper : RedexWithHistory m := ⟨_,pre.append (.single (singleContraction R)),⟨_,S.redex⟩⟩
    let lower : RedexWithHistory m := ⟨_,pre,⟨_,S'.redex⟩⟩
    have upperRep : RunRepresents
        (.of ((pre.append (.single (singleContraction R))).append (.single (singleContraction S)))
          ((ordinary.append (.single R)).append (.single S))) upper := ⟨S,ordinary.append (.single R),rfl⟩
    have lowerRep : RunRepresents (.of (pre.append (.single (singleContraction S'))) (ordinary.append (.single S'))) lower :=
      ⟨S',ordinary,rfl⟩
    rw [source.unique upperRep,target.unique lowerRep]
    exact ⟨.single (singleContraction R),.refl _,by simpa only [ParallelHistory.single_derivation] using residual⟩
  | disjoint pre ordinary R σ ha τ hb last row positive site apart inside =>
    obtain ⟨lower,upper,lowerRep,upperRep,copy⟩ := row.pointed_copy R ha hb positive pre ordinary
    rw [source.unique upperRep,target.unique lowerRep]
    exact copy

theorem Pruning.copy {r s : ExtractionRun m} (steps : Pruning r s) (a b : RedexWithHistory m)
    (source : RunRepresents r a) (target : RunRepresents s b) : Copy b a := by
  induction steps generalizing a b with
  | refl =>
    have same := source.unique target
    cases same
    exact .refl _
  | @cons r mid s step rest ih =>
    obtain ⟨middle,rep⟩ := mid.represents_exists step.extraction.positive
    exact (ih middle b rep target).trans (step.copy a middle source rep)

theorem Atomic.prune_initial_residual {ρ : ParallelHistory t u} (atomic : Atomic ρ)
    (initial : RedexOcc t) (last : BetaAt u p v)
    (residual : ρ.derivation.Residual initial ⟨p,last.redex⟩) (initialStep : BetaAt t initial.val w) :
    Pruning (.of (ρ.append (.single (singleContraction last))) (atomic.append (.single last)))
      (.of (.single (singleContraction initialStep)) (.single initialStep)) := by
  induction atomic generalizing p v w with
  | nil t =>
    have same := congrArg Subtype.val ((Derivation.residual_nil initial ⟨p,last.redex⟩).mp residual)
    have runEq : ExtractionRun.of ((ParallelHistory.nil t).append (.single (singleContraction last)))
        ((Atomic.nil t).append (.single last)) = .of (.single (singleContraction initialStep)) (.single initialStep) := by
      apply ExtractionRun.ext_paths
      change [p]=[initial.val]
      rw [same]
    rw [runEq]
    exact .refl _
  | @cons t q mid u tail head tailAtomic ih =>
    change (head |> singleContraction).derivation.append tail.derivation |>.Residual initial ⟨p,last.redex⟩ at residual
    obtain ⟨middle,first,rest⟩ := (Derivation.residual_append _ _ initial ⟨p,last.redex⟩).mp residual
    obtain ⟨target,middleStep⟩ := middle.contract_exists
    have removedTail := (ih middle last rest middleStep).prepend (.single (singleContraction head)) (.single head)
    have removedHead := Pruning.single (PruningStep.residual (.nil t) (.nil t) head middleStep initialStep first)
    exact .trans (by simpa only [ExtractionRun.prepend,ExtractionRun.of,ParallelHistory.single,ParallelHistory.append] using removedTail) removedHead

theorem Atomic.prune_apart_suffix (pre : ParallelHistory m t) (prefixAtomic : Atomic pre)
    {suffix : ParallelHistory t u} (ordinary : Atomic suffix) (last : BetaAt u p v)
    (apart : ∀ q∈suffix.derivation.paths,DisjointPositions q p) :
    ∃ w, ∃ initial : BetaAt t p w,
      Pruning (.of ((pre.append suffix).append (.single (singleContraction last)))
        ((prefixAtomic.append ordinary).append (.single last)))
        (.of (pre.append (.single (singleContraction initial))) (prefixAtomic.append (.single initial))) := by
  obtain ⟨ancestor,same,residual⟩ := ordinary.apart_pointed_ancestor ⟨p,last.redex⟩ apart
  change ancestor.val=p at same
  obtain ⟨w,initial⟩ := ancestor.contract_exists
  have atP : BetaAt t p w := by rw [←same]; exact initial
  have removed := (ordinary.prune_initial_residual ancestor last residual initial).prepend pre prefixAtomic
  refine ⟨w,atP,?_⟩
  have sourceEq : ExtractionRun.prepend pre prefixAtomic
      (.of (suffix.append (.single (singleContraction last))) (ordinary.append (.single last))) =
      .of ((pre.append suffix).append (.single (singleContraction last)))
        ((prefixAtomic.append ordinary).append (.single last)) := by
    apply ExtractionRun.ext_paths
    simp only [ExtractionRun.prepend,ExtractionRun.of,ParallelHistory.derivation_append,Derivation.append,List.append_assoc]
  have targetEq : ExtractionRun.prepend pre prefixAtomic
      (.of (.single (singleContraction initial)) (.single initial)) =
      .of (pre.append (.single (singleContraction atP))) (prefixAtomic.append (.single atP)) := by
    apply ExtractionRun.ext_paths
    simp only [ExtractionRun.prepend,ExtractionRun.of,ParallelHistory.derivation_append,
      Derivation.append,ParallelHistory.single_derivation,ParallelStep.derivation,singleContraction]
    rw [same]
  rw [sourceEq,targetEq] at removed
  exact removed

theorem Atomic.prune_disjoint_prefix {pre : ParallelHistory t u} (preAtomic : Atomic pre)
    (σ : ParallelHistory u w) (ordinary : Atomic σ) (inside : Internal site σ)
    (positive : 0<σ.length)
    (apart : ∀ p∈pre.derivation.paths,DisjointPositions p site) :
    ∃ v, ∃ source : ParallelHistory t v, ∃ sourceAtomic : Atomic source,
      source.derivation.paths=σ.derivation.paths ∧ Internal site source ∧
      Pruning (.of (pre.append σ) (preAtomic.append ordinary)) (.of source sourceAtomic) := by
  induction preAtomic generalizing w with
  | nil t => exact ⟨w,σ,ordinary,rfl,inside,.refl _⟩
  | @cons t p mid u tail R tailAtomic ih =>
    have tailApart : ∀ q∈tail.derivation.paths,DisjointPositions q site := by
      intro q hq; exact apart q (by simp [ParallelHistory.derivation,Derivation.append,hq])
    obtain ⟨z,middle,middleAtomic,middlePaths,middleInside,removed⟩ :=
      ih σ ordinary inside positive tailApart
    have headApart : DisjointPositions p site := apart p (by
      simp [ParallelHistory.derivation,Derivation.append,ParallelStep.derivation,singleContraction])
    obtain ⟨v,source,remaining,sourceAtomic,sourcePaths,sourceInside,row⟩ :=
      middleAtomic.disjoint_row_pullback R headApart middleInside
    have sourcePositive : 0<source.length := by
      have eq := congrArg List.length (sourcePaths.trans middlePaths)
      rw [sourceAtomic.paths_length,ordinary.paths_length] at eq
      omega
    have first := removed.prepend (.single (singleContraction R)) (.single R)
    have second := Pruning.single (PruningStep.disjoint (.nil t) (.nil t)
      R source sourceAtomic middle middleAtomic (singleContraction remaining) row sourcePositive site headApart sourceInside)
    refine ⟨v,source,sourceAtomic,sourcePaths.trans middlePaths,sourceInside,?_,⟩
    exact .trans (by simpa only [ExtractionRun.prepend,ExtractionRun.of,ParallelHistory.single,ParallelHistory.append] using first) second

end Lamping.Lambda

