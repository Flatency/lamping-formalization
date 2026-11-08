import Lamping.Lambda.ExtractionConfluence
import Lamping.Lambda.ResidualOrigins
import Lamping.Lambda.ProjectionFamilies
namespace Lamping.Lambda

/-- A one-tile ordinary projection transports its source redex to the
actual projected singleton. -/
theorem StepProjection.singleton_residual {step : ParallelStep F t u}
    (A : BetaAt t a x) (S : BetaAt u q v) {last : ParallelStep G x v}
    (row : StepProjection step (.single (singleContraction A))
      (.single (singleContraction S)) last) :
    step.derivation.Residual ⟨a,A.redex⟩ ⟨q,S.redex⟩ := by
  obtain ⟨mid,K,pre,vertical,tail,hpre,he⟩ := row.split_last (.nil t) (singleContraction A)
  have empty := hpre.length
  cases pre with
  | nil =>
    have paths : tail.paths=[q] := by
      have hp := congrArg (fun h => h.derivation.paths) he
      simpa only [ParallelHistory.append,ParallelHistory.single_derivation] using hp.symm
    have transported := vertical.singleton_projection_residual ⟨a,A.redex⟩ ⟨q,S.redex⟩ tail paths
    have perm := hpre.permutation
    simp only [ParallelHistory.append_nil,ParallelHistory.append] at perm
    have compat := perm.residual ⟨a,A.redex⟩ ⟨q,S.redex⟩
    simp only [ParallelHistory.single_derivation] at compat
    exact compat.mpr transported
  | cons => simp [ParallelHistory.length] at empty

/-- The local (i,i) extraction peak at the same final pair has identical
targets: a final old redex cannot have two different source redex names. -/
theorem residual_extraction_target_unique
    (pre : ParallelHistory m t) (ha : Atomic pre)
    (R : BetaAt t p u) (S : BetaAt u q v)
    (A : BetaAt t a x) (B : BetaAt t b y)
    (hA : (singleContraction R).derivation.Residual ⟨a,A.redex⟩ ⟨q,S.redex⟩)
    (hB : (singleContraction R).derivation.Residual ⟨b,B.redex⟩ ⟨q,S.redex⟩) :
    ExtractionRun.of (pre.append (.single (singleContraction A))) (ha.append (.single A)) =
      .of (pre.append (.single (singleContraction B))) (ha.append (.single B)) := by
  have names := Derivation.residual_unique_source (singleContraction R).derivation
    ⟨a,A.redex⟩ ⟨b,B.redex⟩ ⟨q,S.redex⟩ hA hB
  have path : a=b := congrArg Subtype.val names
  subst b
  have target := A.unique B
  subst y
  rfl

theorem residual_extraction_peak_join
    (pre : ParallelHistory m t) (ha : Atomic pre)
    (R : BetaAt t p u) (S : BetaAt u q v)
    (A : BetaAt t a x) (B : BetaAt t b y)
    (hA : (singleContraction R).derivation.Residual ⟨a,A.redex⟩ ⟨q,S.redex⟩)
    (hB : (singleContraction R).derivation.Residual ⟨b,B.redex⟩ ⟨q,S.redex⟩) :
    ExtractionJoin
      (.of (pre.append (.single (singleContraction A))) (ha.append (.single A)))
      (.of (pre.append (.single (singleContraction B))) (ha.append (.single B))) := by
  rw [residual_extraction_target_unique pre ha R S A B hA hB]
  exact ⟨_,.refl _,.refl _⟩

/-- The (i,ii) and (i,iii) peaks with singleton horizontal histories close
at the same target. Their geometric side conditions are unnecessary for
this leaf: the genuine projection supplies the old-redex residual. -/
theorem residual_projection_peak_join
    (pre : ParallelHistory m t) (ha : Atomic pre)
    (R : BetaAt t p u) (S : BetaAt u q v)
    (A : BetaAt t a x) (B : BetaAt t b y)
    (hA : (singleContraction R).derivation.Residual ⟨a,A.redex⟩ ⟨q,S.redex⟩)
    {last : ParallelStep G y v}
    (row : StepProjection (singleContraction R) (.single (singleContraction B))
      (.single (singleContraction S)) last) :
    ExtractionJoin
      (.of (pre.append (.single (singleContraction A))) (ha.append (.single A)))
      (.of (pre.append (.single (singleContraction B))) (ha.append (.single B))) :=
  residual_extraction_peak_join pre ha R S A B hA (row.singleton_residual B S)

end Lamping.Lambda
