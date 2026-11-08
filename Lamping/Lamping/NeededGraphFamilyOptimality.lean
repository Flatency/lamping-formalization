import Lamping.Lamping.NeededGraphExecution
import Lamping.Lambda.WholeFamilyCopyPartition

namespace Lamping.AG.Readback
open Graph Lambda Lambda.Labelled

private theorem compare_same_root_partitions {m m' n : Term}
    (sameRoot : m = m') {prior : ParallelHistory m n}
    (complete : CompleteDerivation prior) (needful : CallByNeedHistory prior) (normal : BetaNF n) :
    ∀ {u : Term} (competitor : ParallelHistory m' u), BetaNF u →
      ∀ plan : CopyUnitPlan competitor, plan.Partitioned (.nil m') →
        (wholeFamilyCopyUnitPlan prior).units ≤ plan.units := by
  subst m'
  exact (complete.wholeFamilyCopyUnitPlan_minimal needful normal).2

/-- The actual initialized executable reaches a graph with beta-normal
readback. Its projected complete, needed history realizes the minimum
copy-unit count over every strict copy partition of every normalizing
history from the same input term. -/
theorem normalizeNeededGraph_family_optimal (term : Term)
    (closed : Closed term) (normalizable : HasNF term) :
    let result := (normalizeNeededGraph term closed normalizable).val
    BetaNF result.term ∧
      ∃ (current : LTerm) (schemas : List Schema)
        (raw prior : ParallelHistory (initLabels term).erase current.erase),
        GraphTrace (ActualNet.initial (initLabels term).erase) result.graph.graph schemas ∧
        LabelledGraphProjection (ActualNet.initial (initLabels term).erase) result.graph.graph
          (.inl ()) schemas (initLabels term) current raw ∧
        raw.derivation = prior.derivation ∧ CompleteDerivation prior ∧ CallByNeedHistory prior ∧
        current.erase = result.term ∧
        (wholeFamilyCopyUnitPlan prior).Partitioned (.nil (initLabels term).erase) ∧
        (wholeFamilyCopyUnitPlan prior).units = prior.length ∧
        ∀ {u : Term} (competitor : ParallelHistory term u), BetaNF u →
          ∀ plan : CopyUnitPlan competitor, plan.Partitioned (.nil term) →
            (wholeFamilyCopyUnitPlan prior).units ≤ plan.units := by
  obtain ⟨normal, current, schemas, raw, prior, trace, projection, same,
    complete, needful, erased⟩ := normalizeNeededGraph_spec term closed normalizable
  have currentNormal : BetaNF current.erase := erased.symm ▸ normal
  exact ⟨normal, current, schemas, raw, prior, trace, projection, same, complete,
    needful, erased, complete.wholeFamilyCopyUnitPlan_partitioned,
    wholeFamilyCopyUnitPlan_units prior,
    compare_same_root_partitions (erase_initLabels term) complete needful currentNormal⟩

#print axioms Lamping.AG.Readback.normalizeNeededGraph_family_optimal

end Lamping.AG.Readback
