import Lamping.Lambda.HistoryPreorder
import Lamping.Lambda.PointedRuns
import Lamping.Lambda.ExtractionContexts
namespace Lamping.Lambda

def RedexWithHistory.prepend (pre : ParallelHistory m t) (a : RedexWithHistory t) :
    RedexWithHistory m := ⟨a.target,pre.append a.history,a.redex⟩

theorem Copy.prepend {a b : RedexWithHistory t} (copy : Copy a b) (pre : ParallelHistory m t) :
    Copy (a.prepend pre) (b.prepend pre) := by
  obtain ⟨extension,perm,residual⟩ := copy
  refine ⟨extension,?_,residual⟩
  change PermEq ((pre.append a.history).append extension) (pre.append b.history)
  rw [ParallelHistory.append_assoc]
  exact PermEq.prepend pre perm

theorem FamilyEq.prepend {a b : RedexWithHistory t} (family : FamilyEq a b) (pre : ParallelHistory m t) :
    FamilyEq (a.prepend pre) (b.prepend pre) := by
  induction family with
  | copy h => exact .copy (h.prepend pre)
  | symm h ih => exact .symm ih
  | trans h k ih ik => exact .trans ih ik

theorem RunRepresents.prepend {r : ExtractionRun t} {a : RedexWithHistory t}
    (represented : RunRepresents r a) (pre : ParallelHistory m t) (ha : Atomic pre) :
    RunRepresents (r.prepend pre ha) (a.prepend pre) := by
  obtain ⟨last,atomic,history⟩ := represented
  refine ⟨last,ha.append atomic,?_⟩
  change pre.append r.history=(pre.append a.history).append (.single (singleContraction last))
  rw [history,ParallelHistory.append_assoc]

theorem Copy.history_prefix {a b : RedexWithHistory m} (copy : Copy a b) :
    HistoryPrefix a.history b.history := by
  obtain ⟨extension,perm,_⟩ := copy
  exact ⟨extension,perm⟩

theorem HistoryPrefix.cancel_prefix (pre : ParallelHistory m t)
    {a : ParallelHistory t u} {b : ParallelHistory t v}
    (order : HistoryPrefix (pre.append a) (pre.append b)) : HistoryPrefix a b := by
  obtain ⟨extension,perm⟩ := order
  refine ⟨extension,?_⟩
  rw [ParallelHistory.append_assoc] at perm
  exact perm.cancel_prefix pre

end Lamping.Lambda
