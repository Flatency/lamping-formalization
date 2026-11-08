import Lamping.Lambda.LabelAtomicOrigins
import Lamping.Lambda.CanonicalPrefixStandard
namespace Lamping.Lambda.Labelled

/-- The full INIT base case: equality with an initial redex degree is exactly
being its genuine old-name residual along the chosen actual history. -/
theorem History.initial_degree_residual_iff (history : History ps t u) (initial : INIT t)
    (r : RedexOcc t.erase) (s : RedexOcc u.erase) :
    t.degreeAt r.val=u.degreeAt s.val ↔
      (⟨ps,history.betaHistory⟩ : Derivation t.erase u.erase).Residual r s := by
  constructor
  · intro equal
    obtain ⟨l,atInitial⟩ := degreeAt_exists t r
    have atFinal : u.degreeAt s.val=some l := equal.symm.trans atInitial
    obtain ⟨b,atLambda⟩ := LTerm.degreeAt_lambda atInitial
    have atomic : IsAtomic l := initial.1 l (LTerm.label_mem_of_subterm atLambda)
    obtain ⟨old,residual⟩ := history.atomic_degree_residual s l atFinal atomic
    have transported := Labelled.Derivation.residual_degree
      (⟨ps,history.betaHistory⟩ : Derivation t.erase u.erase) t u rfl history old s residual
    have oldDegree : t.degreeAt old.val=some l := transported.symm.trans atFinal
    have equalPath := LTerm.initial_degree_injective initial atInitial oldDegree
    have same : r=old := Subtype.ext equalPath
    cases same
    exact residual
  · intro residual
    exact (Labelled.Derivation.residual_degree
      (⟨ps,history.betaHistory⟩ : Derivation t.erase u.erase) t u rfl history r s residual).symm

/-- An atomic final degree admits no nonempty canonical ordinary prefix.
Old-tag reflection supplies an actual initial ancestor, so rule (i) applies. -/
theorem History.atomic_degree_normal_prefix_empty
    (program : ParallelHistory t.erase u.erase) (ordinary : Atomic program)
    (history : History program.derivation.paths t u) (last : BetaAt u.erase p n)
    (normal : ExtractionNormal (.of (program.append (.single (singleContraction last)))
      (ordinary.append (.single last))))
    (degree : u.degreeAt p=some l) (atomic : IsAtomic l) : program.length=0 := by
  by_cases empty : program.length=0
  · exact empty
  · have positive : 0<program.length := Nat.pos_of_ne_zero empty
    obtain ⟨r,residual⟩ := history.atomic_degree_residual ⟨p,last.redex⟩ l degree atomic
    have same : (⟨program.derivation.paths,history.betaHistory⟩ : Derivation t.erase u.erase)=program.derivation :=
      Lamping.Lambda.Derivation.ext rfl
    rw [same] at residual
    exact False.elim (normal_no_old_last program ordinary positive last normal r residual)

/-- Initial redex versus arbitrary history, under the same arbitrary INIT
source labelling. The historical family relation is the existing one. -/
theorem initial_family_iff_degree (t : LTerm) (initial : INIT t)
    (r : RedexOcc t.erase) (a : RedexWithHistory t.erase) :
    FamilyEq ⟨t.erase,.nil _,r⟩ a ↔
      degreeAlong t [] r.val=degreeAlong t a.history.derivation.paths a.redex.val := by
  constructor
  · intro family
    exact Labelled.FamilyEq.degreeAlong family t rfl
  · intro equal
    rcases a with ⟨n,program,s⟩
    obtain ⟨u,history,erased⟩ := lift_history program.derivation.valid t rfl
    cases erased
    have sourceDegree : degreeAlong t [] r.val=t.degreeAt r.val := by
      simp [degreeAlong,LTerm.replay]
    rw [sourceDegree,degreeAlong_witness history] at equal
    have residual := (history.initial_degree_residual_iff initial r s).mp equal
    have same : (⟨program.derivation.paths,history.betaHistory⟩ : Derivation t.erase u.erase)=program.derivation :=
      Lamping.Lambda.Derivation.ext rfl
    rw [same] at residual
    exact (initial_family_iff r ⟨u.erase,program,s⟩).mpr residual

/-- The two-history iff is fully proved whenever one transported degree is
atomic. Both histories retain the same original INIT labelling. -/
theorem atomic_family_iff_degree (t : LTerm) (initial : INIT t)
    (a b : RedexWithHistory t.erase)
    (atomic : ∃ n,degreeAlong t a.history.derivation.paths a.redex.val=some (Label.atom n)) :
    FamilyEq a b ↔ degreeAlong t a.history.derivation.paths a.redex.val=
      degreeAlong t b.history.derivation.paths b.redex.val := by
  constructor
  · intro family; exact Labelled.FamilyEq.degreeAlong family t rfl
  · intro equal
    rcases a with ⟨n,program,s⟩
    obtain ⟨u,history,erased⟩ := lift_history program.derivation.valid t rfl
    cases erased
    obtain ⟨k,atomic⟩ := atomic
    rw [degreeAlong_witness history] at atomic
    obtain ⟨r,residual⟩ := history.atomic_degree_residual s (Label.atom k) atomic ⟨k,rfl⟩
    have same : (⟨program.derivation.paths,history.betaHistory⟩ : Derivation t.erase u.erase)=program.derivation :=
      Lamping.Lambda.Derivation.ext rfl
    rw [same] at residual
    have initialFamily := (initial_family_iff r ⟨u.erase,program,s⟩).mpr residual
    have initialDegree := Labelled.FamilyEq.degreeAlong initialFamily t rfl
    have otherFamily := (initial_family_iff_degree t initial r b).mpr (initialDegree.trans equal)
    exact FamilyEq.trans initialFamily.symm otherFamily
end Lamping.Lambda.Labelled
