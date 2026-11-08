import Lamping.Lambda.FamilyDevelopmentJoin
namespace Lamping.Checks.FamilyDevelopments
open Lambda

example (relative : RelativeFamilies σ X) (development : DevelopsFamilies ρ X) :
    HistoryPrefix σ ρ := relative.prefix_development development

def invalid : ParallelStep [[.fn],[.fn]] (.var 0) (.var 0) :=
  ⟨[],.var 0,⟨.nil _,rfl⟩,rfl⟩

theorem invalid_relative : RelativeFamilies (.single invalid) (fun _ => False) := by
  intro a used
  cases used with
  | @head _ _ _ _ _ _ _ _ r selected family =>
    have member := (mem_redexPositions (.var 0) r.val).mpr r.property
    have eq : r.val=[] := by simpa [positions] using (List.mem_filter.mp member).1
    have property := r.property
    simp [eq,subtermAt,IsRedex] at property
  | tail impossible => cases impossible

/-- Nonempty repeated invalid selections do not become family events and
do not require a Valid-selection premise in the finite coverage theorem. -/
example : HistoryPrefix (.single invalid) (.nil (.var 0)) := by
  apply invalid_relative.prefix_development
  constructor
  · intro a used; cases used
  · intro r; exact id

#print axioms StepProjection.final_selection_actual
#print axioms StepProjection.selected_copy
#print axioms HistoryProjection.used_left
#print axioms FamilyUsedAt.empty_of_absent
#print axioms RelativeFamilies.prefix_development
end Lamping.Checks.FamilyDevelopments
