import Lamping.Lamping.ActionMatching
import Lamping.Lamping.RootCancellationMatching
import Lamping.Lamping.GraphRootInputPreservation
namespace Lamping.AG
open Graph Lambda
section
variable {B : Type} [FiniteNames B]

/-- The six auxiliary schemas preserve the same syntax and root inputs.
Beta is deliberately excluded: its finite old syntax development is a
separate obligation. Every intermediate property is proved from the steps. -/
theorem GraphTrace.auxiliary_rootInputs_matches
    {g h : ActualNet B} {schemas : List Schema} (trace : GraphTrace g h schemas)
    (auxiliary : ∀ s∈schemas,IsCancellation s ∨ IsAction s)
    {directions : B → Bool} {heights : B → Int} {root : B}
    (flow : FlowBalance g.net directions) (positive : directions root=true)
    (balance : IndexedLevelBalance g.net heights) (rootDepth : heights root=0)
    (inputs : RootInputs g.net root) (oldT : Transparency g.net root)
    {t : Term} (matching : Matches g.net root t) : RootInputs h.net root ∧Matches h.net root t := by
  induction trace with
  | iso same => exact ⟨same.rootInputs inputs,same.matches matching⟩
  | cons step tail ih =>
    have nextInputs := step.rootInputs flow positive balance rootDepth inputs oldT matching
    have nextMatching := (auxiliary _ List.mem_cons_self).elim
      (fun cancel => step.cancellation_matches_rootInputs cancel flow positive inputs balance rootDepth oldT matching)
      (fun action => step.action_matches_rootInputs action flow positive balance rootDepth inputs oldT matching)
    obtain ⟨newFlow⟩ := step.flowBalance flow
    obtain ⟨newBalance⟩ := step.indexed_balance balance
    have nextT := step.transparency_indexed flow positive balance rootDepth oldT
    exact ih (fun s member => auxiliary s (List.mem_cons_of_mem _ member))
      newFlow newBalance nextInputs nextT nextMatching

theorem GraphTrace.auxiliary_matches
    {g h : ActualNet B} {schemas : List Schema} (trace : GraphTrace g h schemas)
    (auxiliary : ∀ s∈schemas,IsCancellation s ∨ IsAction s)
    {directions : B → Bool} {heights : B → Int} {root : B}
    (flow : FlowBalance g.net directions) (positive : directions root=true)
    (balance : IndexedLevelBalance g.net heights) (rootDepth : heights root=0)
    (inputs : RootInputs g.net root) (oldT : Transparency g.net root)
    {t : Term} (matching : Matches g.net root t) : Matches h.net root t :=
  (trace.auxiliary_rootInputs_matches auxiliary flow positive balance rootDepth inputs oldT matching).2
end
end Lamping.AG
