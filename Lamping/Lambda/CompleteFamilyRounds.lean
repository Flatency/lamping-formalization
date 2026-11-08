import Lamping.Lambda.FiniteFamilySupport
import Lamping.Lambda.CompleteFamiliesExhaustion

namespace Lamping.Lambda

/-- The first actual syntax-enumerated selected occurrence. Completeness is
not an input to this data computation, and no semantic witness is selected. -/
def firstSelectedRedex (t : Term) (F : List Path) : Option (RedexOcc t) :=
  (selectedRedexes t F).head?

theorem firstSelectedRedex_selected (t : Term) (F : List Path) (r : RedexOcc t)
    (chosen : firstSelectedRedex t F=some r) : r.val∈F := by
  apply (mem_selectedRedexes t F r).mp
  obtain ⟨tail,split⟩ := List.head?_eq_some_iff.mp chosen
  rw [split]
  exact List.mem_cons_self

/-- CompleteFamilyStep proves the already computed Option succeeds. Its
existential representative is used only to refute the none branch in Prop. -/
theorem CompleteFamilyStep.firstSelectedRedex_some
    {m t u : Term} {F : List Path} {pre : ParallelHistory m t}
    {step : ParallelStep F t u} (whole : CompleteFamilyStep pre step) :
    ∃ r : RedexOcc t,firstSelectedRedex t F=some r := by
  cases chosen : firstSelectedRedex t F with
  | none =>
    have empty : selectedRedexes t F=[] := List.head?_eq_none_iff.mp chosen
    obtain ⟨_valid,r,selected,_family⟩ := whole
    have member := (mem_selectedRedexes t F r).mpr selected
    rw [empty] at member
    cases member
  | some r => exact ⟨r,rfl⟩

def stepRoundFamily {m t u : Term} {F : List Path}
    (pre : ParallelHistory m t) (_step : ParallelStep F t u) : Option (FamilyClass m) :=
  (firstSelectedRedex t F).map fun r => familyClassOf ⟨t,pre,r⟩

/-- One computed class per successful actual first-valid selection; arbitrary
non-complete histories may have none and are not assigned a unit by assertion. -/
def roundFamilySupportAt {m t u : Term} (pre : ParallelHistory m t)
    (rho : ParallelHistory t u) : List (FamilyClass m) :=
  match rho with
  | .nil _ => []
  | .cons step tail =>
      (stepRoundFamily pre step).toList++roundFamilySupportAt (pre.append (.single step)) tail

def roundFamilySupport {m t : Term} (rho : ParallelHistory m t) : List (FamilyClass m) :=
  roundFamilySupportAt (.nil m) rho

theorem roundFamilySupportAt_append {m t u v : Term}
    (pre : ParallelHistory m t) (rho : ParallelHistory t u) (sigma : ParallelHistory u v) :
    roundFamilySupportAt pre (rho.append sigma)=
      roundFamilySupportAt pre rho++roundFamilySupportAt (pre.append rho) sigma := by
  induction rho with
  | nil => simp only [ParallelHistory.append,roundFamilySupportAt,ParallelHistory.append_nil,List.nil_append]
  | cons step tail ih =>
    change (stepRoundFamily pre step).toList++
      roundFamilySupportAt (pre.append (.single step)) (tail.append sigma)=
      ((stepRoundFamily pre step).toList++roundFamilySupportAt (pre.append (.single step)) tail)++
        roundFamilySupportAt (pre.append (.cons step tail)) sigma
    rw [ih,List.append_assoc]
    have samePrefix : (pre.append (.single step)).append tail=pre.append (.cons step tail) := by
      rw [ParallelHistory.append_assoc]
      rfl
    rw [samePrefix]

theorem roundFamilySupport_append {m t u : Term}
    (rho : ParallelHistory m t) (sigma : ParallelHistory t u) :
    roundFamilySupport (rho.append sigma)=
      roundFamilySupport rho++roundFamilySupportAt rho sigma :=
  roundFamilySupportAt_append (.nil m) rho sigma

theorem roundFamilySupportAt_single {m t u : Term} {F : List Path}
    (pre : ParallelHistory m t) (step : ParallelStep F t u) (r : RedexOcc t)
    (chosen : firstSelectedRedex t F=some r) :
    roundFamilySupportAt pre (.single step)=[familyClassOf ⟨t,pre,r⟩] := by
  simp only [ParallelHistory.single,roundFamilySupportAt,stepRoundFamily,chosen,
    Option.map_some,Option.toList,List.append_nil]

/-- Whole-family closure relates every actual selected member to the
computed representative. The resulting list has exactly the FAM support. -/
theorem CompleteDerivation.mem_roundFamilySupport {m t : Term}
    {rho : ParallelHistory m t} (complete : CompleteDerivation rho) (a : RedexWithHistory m) :
    familyClassOf a∈roundFamilySupport rho ↔ FamilyUsed rho a := by
  induction complete with
  | nil =>
    constructor
    · intro impossible;cases impossible
    · intro impossible;cases impossible
  | @step v t pre F step previous whole ih =>
    obtain ⟨r,chosen⟩ := whole.firstSelectedRedex_some
    have selected := firstSelectedRedex_selected _ _ r chosen
    rw [roundFamilySupport_append,roundFamilySupportAt_single pre step r chosen,List.mem_append]
    constructor
    · rintro (old|fresh)
      · exact (FamilyUsedAt.append_iff (.nil m) pre (.single step) a).mpr (.inl (ih.mp old))
      · have family : FamilyEq ⟨_,pre,r⟩ a :=
          (familyClassOf_eq_iff ⟨_,pre,r⟩ a).mp (List.mem_singleton.mp fresh).symm
        exact (FamilyUsedAt.append_iff (.nil m) pre (.single step) a).mpr (.inr (.head selected family))
    · intro used
      rcases (FamilyUsedAt.append_iff (.nil m) pre (.single step) a).mp used with old | fresh
      · exact .inl (ih.mpr old)
      · change FamilyUsedAt pre (.single step) a at fresh
        cases fresh with
        | head selectedOther family =>
          have sameFamily := whole.same_family r _ selected selectedOther
          have classEq := (familyClassOf_eq_iff ⟨_,pre,r⟩ a).mpr (sameFamily.trans family)
          exact .inr (List.mem_singleton.mpr classEq.symm)
        | tail impossible => cases impossible

private theorem round_nodup_snoc {A : Type} {xs : List A} {x : A}
    (distinct : xs.Nodup) (fresh : x∉xs) : (xs++[x]).Nodup := by
  revert distinct fresh
  induction xs with
  | nil => intro _distinct _fresh;simp
  | cons first xs ih =>
    intro distinct fresh
    have parts := List.nodup_cons.mp distinct
    apply List.nodup_cons.mpr
    constructor
    · intro member
      rcases List.mem_append.mp member with old | last
      · exact parts.1 old
      · have same : first=x := List.mem_singleton.mp last
        apply fresh
        rw [←same]
        exact List.mem_cons_self
    · apply ih parts.2
      intro member
      exact fresh (List.mem_cons_of_mem _ member)

/-- No family is charged twice in complete rounds. This invokes the existing
PUBLIC theorem on the actual earlier prefix and its actual nil future tail;
no caller noFuture field or new exhaustion axiom is assumed. -/
theorem CompleteDerivation.roundFamilySupport_nodup {m t : Term}
    {rho : ParallelHistory m t} (complete : CompleteDerivation rho) :
    (roundFamilySupport rho).Nodup := by
  induction complete with
  | nil => simp [roundFamilySupport,roundFamilySupportAt]
  | @step v t pre F step previous whole ih =>
    obtain ⟨r,chosen⟩ := whole.firstSelectedRedex_some
    rw [roundFamilySupport_append,roundFamilySupportAt_single pre step r chosen]
    apply round_nodup_snoc ih
    intro member
    have used := (previous.mem_roundFamilySupport ⟨_,pre,r⟩).mp member
    apply previous.no_future_family (.nil _) r
    simpa only [ParallelHistory.append_nil] using used

/-- One representative for each complete nonempty family round. Empty raw
selections in arbitrary histories are not silently counted by this theorem. -/
theorem CompleteDerivation.roundFamilySupport_length {m t : Term}
    {rho : ParallelHistory m t} (complete : CompleteDerivation rho) :
    (roundFamilySupport rho).length=rho.length := by
  induction complete with
  | nil => rfl
  | @step v t pre F step previous whole ih =>
    obtain ⟨r,chosen⟩ := whole.firstSelectedRedex_some
    rw [roundFamilySupport_append,roundFamilySupportAt_single pre step r chosen]
    simp only [List.length_append,List.length_singleton,ih,ParallelHistory.length_append,
      ParallelHistory.single,ParallelHistory.length]

/-- The no-duplicate round list and the general finite support represent the
same actual historical family predicate, without arbitrary PermEq FAM equality. -/
theorem CompleteDerivation.roundFamilySupport_support {m t : Term}
    {rho : ParallelHistory m t} (complete : CompleteDerivation rho) :
    ∀ family : FamilyClass m,family∈roundFamilySupport rho ↔family∈familySupport rho := by
  intro family
  refine Quotient.inductionOn family ?_
  intro a
  exact (complete.mem_roundFamilySupport a).trans (mem_familySupport rho a).symm

#print axioms Lamping.Lambda.firstSelectedRedex
#print axioms Lamping.Lambda.firstSelectedRedex_selected
#print axioms Lamping.Lambda.CompleteFamilyStep.firstSelectedRedex_some
#print axioms Lamping.Lambda.stepRoundFamily
#print axioms Lamping.Lambda.roundFamilySupportAt
#print axioms Lamping.Lambda.roundFamilySupport
#print axioms Lamping.Lambda.roundFamilySupportAt_append
#print axioms Lamping.Lambda.roundFamilySupport_append
#print axioms Lamping.Lambda.roundFamilySupportAt_single
#print axioms Lamping.Lambda.CompleteDerivation.mem_roundFamilySupport
#print axioms Lamping.Lambda.CompleteDerivation.roundFamilySupport_nodup
#print axioms Lamping.Lambda.CompleteDerivation.roundFamilySupport_length
#print axioms Lamping.Lambda.CompleteDerivation.roundFamilySupport_support

end Lamping.Lambda
