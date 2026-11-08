import Lamping.Lambda.LabelAtomicOrigins
import Lamping.Lambda.Labels
import Lamping.Lambda.LabelHistories
import Lamping.Lambda.InitialFamilies

namespace Lamping.Checks.Phase5Review
open Lambda Lambda.Labelled

def identity : Term := .lam (.var 0)
def creationSource : Term := .app (.app identity identity) identity
def creationInitial : LTerm := initLabels creationSource
def creationTarget : LTerm :=
  .app (Label.atom 0)
    (LTerm.contract (Label.atom 1) (Label.atom 2)
      (.var (Label.atom 3) 0) (.lam (Label.atom 4) (.var (Label.atom 5) 0)))
    (.lam (Label.atom 6) (.var (Label.atom 7) 0))

theorem creation_init : INIT creationInitial := init_is_INIT creationSource
theorem actual_creation : LBETA creationInitial creationTarget :=
  .fn (.root (Label.atom 1) (Label.atom 2)
    (.var (Label.atom 3) 0) (.lam (Label.atom 4) (.var (Label.atom 5) 0)))
theorem source_root_not_redex : creationInitial.degree = none := rfl
theorem created_compound_degree : creationTarget.degree = some
    (((Label.atom 1).concat (Label.atom 2).over).concat
      ((Label.atom 3).concat ((Label.atom 2).under.concat (Label.atom 4)))) := rfl
theorem compound_degree_outer_length :
    creationTarget.degree.map Label.length = some 5 := rfl
theorem creation_target_erase : creationTarget.erase = .app identity identity := rfl

/-- A late reset destroys the shared-source degree; INIT belongs to the source. -/
theorem late_reset_changes_created_degree :
    (initLabels creationTarget.erase).degree ≠ creationTarget.degree := by
  decide

def repeatedIdentity : LTerm := .lam (Label.atom 0) (.var (Label.atom 0) 0)
def repeatedSource : LTerm := .app (Label.atom 0)
  (.app (Label.atom 0) repeatedIdentity repeatedIdentity)
  (.app (Label.atom 0) repeatedIdentity repeatedIdentity)
def repeatedLeft : RedexOcc repeatedSource.erase := ⟨[.fn],_,rfl,True.intro⟩
def repeatedRight : RedexOcc repeatedSource.erase := ⟨[.arg],_,rfl,True.intro⟩

theorem repeated_degrees_equal :
    repeatedSource.degreeAt repeatedLeft.val = repeatedSource.degreeAt repeatedRight.val := rfl

/-- Equality of degrees without INIT does not imply the genuine historical family. -/
theorem repeated_different_families :
    ¬ FamilyEq ⟨repeatedSource.erase,.nil _,repeatedLeft⟩
      ⟨repeatedSource.erase,.nil _,repeatedRight⟩ := by
  intro hf
  have eq := congrArg Subtype.val ((initial_families_injective _ _).mp hf)
  cases eq

#print axioms actual_creation
#print axioms created_compound_degree
#print axioms late_reset_changes_created_degree
#print axioms repeated_different_families

def repeatedAfter : LTerm := .app (Label.atom 0)
  (LTerm.contract (Label.atom 0) (Label.atom 0) (.var (Label.atom 0) 0) repeatedIdentity)
  (.app (Label.atom 0) repeatedIdentity repeatedIdentity)

theorem repeated_step_history : History [[.fn]] repeatedSource repeatedAfter :=
  .cons (.fn (.root _ _ _ _)) (.nil _)

def repeatedAfterRight : RedexOcc repeatedAfter.erase := ⟨[.arg],_,rfl,True.intro⟩

theorem repeated_source_not_INIT : ¬ INIT repeatedSource := by
  intro h
  have nodup := h.2
  simp [repeatedSource,repeatedIdentity,LTerm.labels] at nodup

/-- Atomic residual reflection retains its real meaning without INIT: the
unrelated contraction changes the left branch but the right old redex survives. -/
theorem repeated_actual_atomic_residual :
    ∃ r : RedexOcc repeatedSource.erase,
      (⟨[[.fn]],repeated_step_history.betaHistory⟩ : Derivation _ _).Residual r repeatedAfterRight :=
  repeated_step_history.atomic_degree_residual repeatedAfterRight (Label.atom 0) rfl ⟨0,rfl⟩

#print axioms repeated_actual_atomic_residual
end Lamping.Checks.Phase5Review

