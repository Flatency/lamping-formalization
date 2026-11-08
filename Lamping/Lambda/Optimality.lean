import Lamping.Lambda.CompleteFamilyRounds
import Lamping.Lambda.WholeFamilyCopyPartition

namespace Lamping.Lambda

/-- The computed family of each complete round enumerates exactly the used
family classes, with one distinct class per round. -/
theorem CompleteDerivation.familyRoundEnumeration {m t : Term}
    {history : ParallelHistory m t} (complete : CompleteDerivation history) :
    let rounds := roundFamilySupport history
    rounds.length = history.length ∧
      (∀ family : FamilyClass m,
        (∃ i : Fin rounds.length, rounds.get i = family) ↔ family ∈ familySupport history) ∧
      (∀ i j : Fin rounds.length, rounds.get i = rounds.get j → i = j) := by
  let rounds := roundFamilySupport history
  refine ⟨complete.roundFamilySupport_length, ?_, ?_⟩
  · intro family
    exact (List.mem_iff_get (a := family) (l := rounds)).symm.trans
      (complete.roundFamilySupport_support family)
  · intro i j equal
    apply Fin.ext
    apply List.getElem?_inj i.isLt complete.roundFamilySupport_nodup
    simpa only [List.getElem?_eq_getElem i.isLt, List.getElem?_eq_getElem j.isLt,
      List.get_eq_getElem] using congrArg some equal

end Lamping.Lambda

