import Lamping.Lambda.ContractumPositionOrigins
namespace Lamping.Lambda
/-- A free index is renamed above exactly the local occurrence's binders. -/
theorem occurrenceRenaming_free_index (rho : Nat → Nat) (p : Path) (k : Nat) :
    occurrenceRenaming rho p (k+binderDepth p)=rho k+binderDepth p := by
  induction p generalizing rho k with
  | nil => rfl
  | cons step rest ih =>
    cases step with
    | fn | arg => exact ih rho k
    | body =>
      change occurrenceRenaming (liftRen rho) rest (k+(binderDepth rest+1))=rho k+(binderDepth rest+1)
      rw [show k+(binderDepth rest+1)=(k+1)+binderDepth rest by omega,ih]
      simp only [liftRen]
      omega
/-- A shifted copy has an outer-bound variable at this position exactly
when the ORIGINAL argument has the corresponding variable. Internal binders
are protected by occurrenceRenaming; no free-variable-only syntax shortcut. -/
theorem shifted_outer_variable_iff (argument : Term) (p : Path) (outer shift : Nat) :
    subtermAt (rename (fun i => i+shift) argument) p=
      some (.var ((outer+shift)+binderDepth p)) ↔
    subtermAt argument p=some (.var (outer+binderDepth p)) := by
  constructor
  · intro shifted
    have undo : rename (fun i => i-shift) (rename (fun i => i+shift) argument)=argument := by
      rw [rename_comp]
      have functions : (fun i => (i+shift)-shift)=(id : Nat → Nat) := by funext i; change (i+shift)-shift=i; omega
      change rename (fun i => (i+shift)-shift) argument=argument
      rw [functions]
      exact rename_id argument
    have reflected := subtermAt_rename (fun i => i-shift) (rename (fun i => i+shift) argument) p
    rw [undo,shifted] at reflected
    simp only [Option.map_some,rename,occurrenceRenaming_free_index] at reflected
    simpa only [Nat.add_sub_cancel] using reflected
  · intro old
    rw [subtermAt_rename,old]
    simp only [Option.map_some,rename,occurrenceRenaming_free_index]
/-- Exact local copy-coordinate/binder reflection inside a beta contractum. -/
theorem contract_copied_outer_variable_iff {body argument : Term} {q : Path}
    (occurs : ArgumentOccurrence body q) (z : Path) (outer : Nat) :
    subtermAt (contract body argument) (q++z)=some (.var (outer+binderDepth (q++z))) ↔
    subtermAt argument z=some (.var (outer+binderDepth z)) := by
  rw [subtermAt_append,argument_copy occurs argument,Option.bind_some]
  simpa only [binderDepth_append,Nat.add_assoc] using
    shifted_outer_variable_iff argument z outer (binderDepth q)
/-- A real contextual inner beta, followed by an actual copy position,
reflects binding to its surrounding outer lambda back to the ORIGINAL
argument leaf. This is a syntax theorem, not graph generatedness. -/
theorem BetaAt.nested_copied_outer_variable_iff
    (step : BetaAt before site after)
    (lookup : subtermAt before site=some (.app (.lam body) argument))
    (occurs : ArgumentOccurrence body q) (z : Path) :
    subtermAt after (site++(q++z))=some (.var (binderDepth (site++(q++z)))) ↔
    subtermAt argument z=some (.var (binderDepth site+binderDepth z)) := by
  have actual := step.contract_lookup lookup
  rw [subtermAt_append,actual,Option.bind_some,binderDepth_append]
  exact contract_copied_outer_variable_iff occurs z (binderDepth site)
end Lamping.Lambda

