import Lamping.Lambda.RootDisjointTailPeak
import Lamping.Lambda.ExtractionNormalTransport
namespace Lamping.Lambda

theorem StepProjection.disjoint_normal_reflect (R : BetaAt t p u)
    (row : StepProjection (singleContraction R) original projected last)
    (ho : Atomic original) (hp : Atomic projected) (positive : 0<original.length)
    (apart : DisjointPositions p site) (inside : Internal site original)
    (normal : ExtractionNormal (.of projected hp)) : ExtractionNormal (.of original ho) := by
  have samePaths := row.disjoint_paths R ho hp apart inside
  have projectedInside : Internal site projected := by intro q hq; exact inside q (samePaths ▸ hq)
  have lookupExists : ∃a,subtermAt t site=some a := by
    cases ho with
    | nil => simp only [ParallelHistory.length] at positive; omega
    | cons A ht =>
      have scope := inside _ (by change (_ : Path)∈_::_; exact List.mem_cons_self)
      obtain ⟨q,hq⟩ := scope
      obtain ⟨redex,hr,_⟩ := A.redex
      rw [hq] at hr
      obtain ⟨a,ha,_⟩ := prefix_exists hr
      exact ⟨a,ha⟩
  obtain ⟨a,lookup⟩ := lookupExists
  have lookup' : subtermAt u site=some a := (R.disjoint_subterm apart).trans lookup
  obtain ⟨C,cp,ct⟩ := SyntaxContext.of_lookup lookup
  obtain ⟨D,dp,dt⟩ := SyntaxContext.of_lookup lookup'
  cases ct
  cases dt
  obtain ⟨b,localOriginal,hoa,_,_,pathsO⟩ :=
    C.reflectHistory original ho (by simpa only [cp] using inside)
  obtain ⟨c,localProjected,hpc,_,_,pathsP⟩ :=
    D.reflectHistory projected hp (by simpa only [dp] using projectedInside)
  let ro : ExtractionRun a := .of localOriginal hoa
  let rp : ExtractionRun a := .of localProjected hpc
  have localSame : rp=ro := by
    apply ExtractionRun.ext_paths
    apply mapped_prefix_paths_injective site
    change localProjected.derivation.paths.map (fun q => site++q)=
      localOriginal.derivation.paths.map (fun q => site++q)
    rw [←dp,←pathsP,dp,←cp,←pathsO]
    exact samePaths.symm
  have actualOriginal : ExtractionRun.of original ho=C.liftRun ro := by
    apply ExtractionRun.ext_paths
    rw [C.liftRun_paths]
    exact pathsO
  have actualProjected : ExtractionRun.of projected hp=D.liftRun rp := by
    apply ExtractionRun.ext_paths
    rw [D.liftRun_paths]
    exact pathsP
  rw [actualProjected] at normal
  have localNormal := D.normal_of_lift normal
  rw [localSame] at localNormal
  rw [actualOriginal]
  exact localNormal.lift_context C

end Lamping.Lambda
