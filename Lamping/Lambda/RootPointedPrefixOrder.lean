import Lamping.Lambda.RootPointedProjection
import Lamping.Lambda.PrefixProjection
import Lamping.Lambda.PointedPrefixOperations
namespace Lamping.Lambda

theorem HistoryPrefix.projected_head_le {R : BetaAt t p u}
    (a : RedexWithHistory t) (b : RedexWithHistory u)
    (order : HistoryPrefix a.history ((ParallelHistory.single (singleContraction R)).append b.history))
    (program : ParallelHistory u z) (last : ParallelStep F a.target z)
    (row : StepProjection (singleContraction R) a.history program last) :
    HistoryPrefix program b.history := by
  obtain ⟨w,G,bottom,vertical,headedRow⟩ := StepProjection.exists_projection
    (singleContraction R) ((ParallelHistory.single (singleContraction R)).append b.history)
  have projected := order.project_beta R row headedRow
  obtain ⟨endpoint,permutation⟩ := headedRow.same_beta_head_permutation R b.history
  rcases b with ⟨bTarget,bHistory,bRedex⟩
  change w=bTarget at endpoint
  cases endpoint
  have tailPrefix : HistoryPrefix bottom bHistory :=
    ⟨.nil _,by rw [ParallelHistory.append_nil]; exact permutation⟩
  exact projected.trans tailPrefix

/-- The two nested prefix relations in the root-deletion case of AG5.4.4.
 The right prefix is obtained by projecting the supplied extension through
 its own actual beta head, then deleting only genuine empty developments. -/
theorem RootExtraction.pointed_prefix_order {R : BetaAt t p u}
    {source : ExtractionRun u} {target : ExtractionRun t}
    (root : RootExtraction R source target)
    (a0 : RedexWithHistory u) (a : RedexWithHistory t) (b : RedexWithHistory u)
    (sourceRep : RunRepresents source a0) (targetRep : RunRepresents target a)
    (order : HistoryPrefix a.history ((ParallelHistory.single (singleContraction R)).append b.history)) :
    ∃ (z : Term) (F : List Path) (program : ParallelHistory u z) (last : ParallelStep F a.target z),
      StepProjection (singleContraction R) a.history program last ∧
      HistoryPrefix a0.history program ∧ HistoryPrefix program b.history := by
  obtain ⟨z,F,program,last,row,first⟩ := root.pointed_prefix_projection a0 a sourceRep targetRep
  obtain ⟨w,G,bottom,vertical,headedRow⟩ := StepProjection.exists_projection
    (singleContraction R) ((ParallelHistory.single (singleContraction R)).append b.history)
  have projected := order.project_beta R row headedRow
  obtain ⟨endpoint,permutation⟩ := headedRow.same_beta_head_permutation R b.history
  rcases b with ⟨bTarget,bHistory,bRedex⟩
  change w=bTarget at endpoint
  cases endpoint
  have tailPrefix : HistoryPrefix bottom bHistory :=
    ⟨.nil _,by rw [ParallelHistory.append_nil]; exact permutation⟩
  exact ⟨z,F,program,last,row,first,projected.trans tailPrefix⟩

end Lamping.Lambda
