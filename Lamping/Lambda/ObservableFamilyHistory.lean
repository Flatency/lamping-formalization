import Lamping.Lambda.ObservableHistory
import Lamping.Lambda.CompleteFamilies

namespace Lamping.Lambda

/-- Changing only a prefix by a generated permutation preserves whole
current families. The original source and current redex occurrences stay fixed. -/
theorem CompleteFamilyStep.prefix_permutation {prior other : ParallelHistory m t}
    {step : ParallelStep F t u} (whole : CompleteFamilyStep prior step)
    (permutation : PermEq prior other) : CompleteFamilyStep other step := by
  obtain ⟨valid,representative,member,family⟩ := whole
  refine ⟨valid,representative,member,?_⟩
  intro candidate
  have first := FamilyEq.of_permutation (⟨t,prior,representative⟩ : RedexWithHistory m) other permutation
  have last := FamilyEq.of_permutation (⟨t,prior,candidate⟩ : RedexWithHistory m) other permutation
  exact ⟨fun selected=>first.symm.trans ((family candidate).mp selected |>.trans last),
    fun related=>(family candidate).mpr (first.trans (related.trans last.symm))⟩

/-- A separate premise about actual raw parallel boundaries: every nonempty
selection is ALREADY proved a whole family at its actual raw prefix.
This is not a field of a graph trace and supplies no such family proof. -/
inductive FamilyStepsOrSilent : {t u : Term} → ParallelHistory m t → ParallelHistory t u → Prop where
  | nil (prior : ParallelHistory m t) : FamilyStepsOrSilent prior (.nil t)
  | cons {prior : ParallelHistory m t} {F : List Path} {step : ParallelStep F t u}
      {tail : ParallelHistory u v}
      (head : F=[] ∨ CompleteFamilyStep prior step)
      (rest : FamilyStepsOrSilent (prior.append (.single step)) tail) :
      FamilyStepsOrSilent prior (.cons step tail)

private theorem normalize_family_steps (raw : ParallelHistory t u)
    (prior other : ParallelHistory m t) (permutation : PermEq prior other)
    (certified : FamilyStepsOrSilent prior raw) (complete : CompleteDerivation other) :
    ∃ observed : ParallelHistory t u,
      ParallelHistory.Observable observed ∧raw.derivation=observed.derivation ∧
      PermEq raw observed ∧CompleteDerivation (other.append observed) := by
  induction raw generalizing m with
  | nil t =>
    exact ⟨.nil t,.nil t,rfl,.refl _,by simpa only [ParallelHistory.append_nil] using complete⟩
  | @cons t middle target F step tail ih =>
    cases certified with
    | cons head rest =>
      by_cases empty : F=[]
      · subst F
        have endpoint : middle=t := step.endpoint (ParallelStep.empty t)
        subst middle
        have priorPerm : PermEq (prior.append (.single step)) other := by
          simpa only [ParallelHistory.append_nil] using PermEq.comp permutation (PermEq.empty step)
        obtain ⟨observed,positive,same,permTail,completeTail⟩ :=
          ih (prior.append (.single step)) other priorPerm rest complete
        refine ⟨observed,positive,?_,?_,completeTail⟩
        · apply Derivation.ext
          change step.paths++tail.derivation.paths=observed.derivation.paths
          rw [step.empty_paths,List.nil_append,same]
        · exact .trans (.comp (.empty step) (.refl tail)) permTail
      · have whole : CompleteFamilyStep prior step := head.resolve_left empty
        have nextComplete : CompleteDerivation (other.append (.single step)) :=
          .step complete (whole.prefix_permutation permutation)
        obtain ⟨observed,positive,same,permTail,completeTail⟩ :=
          ih (prior.append (.single step)) (other.append (.single step))
            (permutation.append _) rest nextComplete
        refine ⟨.cons step observed,.cons empty positive,?_,?_,?_⟩
        · change step.derivation.append tail.derivation=step.derivation.append observed.derivation
          rw [same]
        · exact .comp (.refl (.single step)) permTail
        · simpa only [ParallelHistory.append_assoc,ParallelHistory.single,ParallelHistory.append] using completeTail

/-- Assemble already certified actual family events and remove their empty
boundaries. The theorem preserves the literal derivation, not just endpoints;
it neither certifies arbitrary nonempty selections nor completes an arbitrary
derivation. Reachable REP must separately supply the family premises. -/
theorem FamilyStepsOrSilent.observable_complete {m t u : Term}
    {prior : ParallelHistory m t} {raw : ParallelHistory t u}
    (certified : FamilyStepsOrSilent prior raw)
    (complete : CompleteDerivation prior) :
    ∃ observed : ParallelHistory t u,
      ParallelHistory.Observable observed ∧raw.derivation=observed.derivation ∧
      PermEq raw observed ∧CompleteDerivation (prior.append observed) :=
  normalize_family_steps raw prior prior (.refl _) certified complete

end Lamping.Lambda
