import Lamping.Lambda.FamilyDevelopments
import Lamping.Lambda.NormalForms
import Lamping.Lambda.NeededFamilyInclusion

namespace Lamping.Lambda

/-- Enumerate actual valid source redexes selected by F. Repeated/invalid
names in F are tested by membership, never charged as additional events.
All returned path data come from the computable syntax traversal. -/
def selectedRedexes (t : Term) (F : List Path) : List (RedexOcc t) :=
  (redexPositions t).attach.filterMap fun p =>
    if p.val∈F then some ⟨p.val,(mem_redexPositions t p.val).mp p.property⟩ else none

theorem mem_selectedRedexes (t : Term) (F : List Path) (r : RedexOcc t) :
    r∈selectedRedexes t F ↔ r.val∈F := by
  constructor
  · intro member
    obtain ⟨p,_member,picked⟩ := List.mem_filterMap.mp member
    by_cases selected : p.val∈F
    · rw [if_pos selected] at picked
      have same := Option.some.inj picked
      have pathEq := congrArg Subtype.val same
      exact pathEq ▸ selected
    · rw [if_neg selected] at picked
      cases picked
  · intro selected
    let p : {path : Path // path∈redexPositions t} :=
      ⟨r.val,(mem_redexPositions t r.val).mpr r.property⟩
    apply List.mem_filterMap.mpr
    refine ⟨p,?_,?_⟩
    · simp
    · rw [if_pos selected]

/-- The existing genuine Copy/FamilyEq quotient, without a new degree-based
definition or an equality decision procedure on families. -/
def familyClassOf {m : Term} (a : RedexWithHistory m) : FamilyClass m :=
  Quotient.mk (familySetoid m) a

theorem familyClassOf_eq_iff {m : Term} (a b : RedexWithHistory m) :
    familyClassOf a=familyClassOf b ↔ FamilyEq a b := by
  constructor
  · exact Quotient.exact
  · intro family
    change Quotient.mk (familySetoid m) a=Quotient.mk (familySetoid m) b
    exact Quotient.sound family

/-- Each actual selected occurrence is paired with its original exact prefix.
The step argument fixes the actual batch; its proof supplies no chosen data. -/
def stepFamilySupport {m t u : Term} {F : List Path}
    (pre : ParallelHistory m t) (_step : ParallelStep F t u) : List (FamilyClass m) :=
  (selectedRedexes t F).map fun r => familyClassOf ⟨t,pre,r⟩

theorem mem_stepFamilySupport {m t u : Term} {F : List Path}
    (pre : ParallelHistory m t) (step : ParallelStep F t u) (a : RedexWithHistory m) :
    familyClassOf a∈stepFamilySupport pre step ↔
      ∃ r : RedexOcc t,r.val∈F ∧ FamilyEq ⟨t,pre,r⟩ a := by
  constructor
  · intro member
    obtain ⟨r,selected,same⟩ := List.mem_map.mp member
    exact ⟨r,(mem_selectedRedexes t F r).mp selected,
      (familyClassOf_eq_iff ⟨t,pre,r⟩ a).mp same⟩
  · rintro ⟨r,selected,family⟩
    exact List.mem_map.mpr ⟨r,(mem_selectedRedexes t F r).mpr selected,
      (familyClassOf_eq_iff ⟨t,pre,r⟩ a).mpr family⟩

/-- A concrete finite list for actual used family support, retaining actual
source terms, batch boundaries and original prefixes. Duplicate quotient
entries are allowed; no infinite quotient cardinal is asserted. -/
def familySupportAt {m t u : Term} (pre : ParallelHistory m t)
    (rho : ParallelHistory t u) : List (FamilyClass m) :=
  match rho with
  | .nil _ => []
  | .cons step tail =>
      stepFamilySupport pre step++familySupportAt (pre.append (.single step)) tail

theorem mem_familySupportAt {m t u : Term} (pre : ParallelHistory m t)
    (rho : ParallelHistory t u) (a : RedexWithHistory m) :
    familyClassOf a∈familySupportAt pre rho ↔ FamilyUsedAt pre rho a := by
  induction rho with
  | nil =>
    constructor
    · intro impossible;cases impossible
    · intro impossible;cases impossible
  | cons step tail ih =>
    change familyClassOf a∈stepFamilySupport pre step++
      familySupportAt (pre.append (.single step)) tail ↔FamilyUsedAt pre (.cons step tail) a
    rw [List.mem_append,mem_stepFamilySupport,ih]
    constructor
    · rintro (⟨r,selected,family⟩|later)
      · exact .head selected family
      · exact .tail later
    · intro used
      cases used with
      | head selected family => exact .inl ⟨_,selected,family⟩
      | tail later => exact .inr later

def familySupport {m t : Term} (rho : ParallelHistory m t) : List (FamilyClass m) :=
  familySupportAt (.nil m) rho

/-- AG FAM is the membership predicate of this explicit finite quotient list.
No assumption about completeness, neededness, normality or labels is required. -/
theorem mem_familySupport {m t : Term} (rho : ParallelHistory m t) (a : RedexWithHistory m) :
    familyClassOf a∈familySupport rho ↔ FamilyUsed rho a :=
  mem_familySupportAt (.nil m) rho a

/-- The already proved directional Needed-family inclusion transports to the
explicit finite supports. Quotient elimination stays inside this proposition;
no representative is chosen to construct runtime data. -/
theorem CompleteDerivation.finite_familySupport_subset
    {m t n : Term} {rho : ParallelHistory m t}
    (complete : CompleteDerivation rho) (needful : CallByNeedHistory rho)
    (sigma : ParallelHistory m n) (normal : BetaNF n) :
    ∀ family : FamilyClass m,family∈familySupport rho → family∈familySupport sigma := by
  intro family
  refine Quotient.inductionOn family ?_
  intro a member
  apply (mem_familySupport sigma a).mpr
  exact complete.needed_family_inclusion needful sigma normal a ((mem_familySupport rho a).mp member)

#print axioms Lamping.Lambda.selectedRedexes
#print axioms Lamping.Lambda.mem_selectedRedexes
#print axioms Lamping.Lambda.familyClassOf
#print axioms Lamping.Lambda.familyClassOf_eq_iff
#print axioms Lamping.Lambda.stepFamilySupport
#print axioms Lamping.Lambda.mem_stepFamilySupport
#print axioms Lamping.Lambda.familySupportAt
#print axioms Lamping.Lambda.mem_familySupportAt
#print axioms Lamping.Lambda.familySupport
#print axioms Lamping.Lambda.mem_familySupport
#print axioms Lamping.Lambda.CompleteDerivation.finite_familySupport_subset

end Lamping.Lambda
