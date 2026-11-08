import Lamping.Lambda.RootArgumentTailPeak
import Lamping.Lambda.ExtractionNormalTransport
namespace Lamping.Lambda

/-- The two actual programs of an argument lift are context lifts of one
 local program, with exactly the specified binder shift in the copy. -/
theorem ArgumentLift.run_contexts {R : BetaAt t p u}
    (lift : ArgumentLift R copy original) (hc : Atomic copy) (ho : Atomic original) :
    ∃ (C D : SyntaxContext) (program : ExtractionRun lift.argument)
      (ce : C.plug lift.argument=t)
      (de : D.plug (Lambda.rename (fun i => i+binderDepth lift.occurrence) lift.argument)=u),
      ExtractionRun.of original ho=(C.liftRun program).castSource ce ∧
      ExtractionRun.of copy hc=(D.liftRun (program.rename (fun i => i+binderDepth lift.occurrence))).castSource de := by
  rcases lift with ⟨body,argument,redex,occurrence,isVariable,localPaths,copyPaths,originalPaths,parallelization⟩
  let lift : ArgumentLift R copy original :=
    ⟨body,argument,redex,occurrence,isVariable,localPaths,copyPaths,originalPaths,parallelization⟩
  have argumentLookup : subtermAt t (p++[.arg])=some argument := by
    rw [subtermAt_append,redex]
    cases argument <;> rfl
  have copyLookup : subtermAt u (p++occurrence)=some (Lambda.rename (fun i => i+binderDepth occurrence) argument) := by
    rw [subtermAt_append,R.contract_lookup redex,Option.bind_some]
    exact argument_copy isVariable argument
  obtain ⟨C,cp,ct⟩ := SyntaxContext.of_lookup argumentLookup
  obtain ⟨D,dp,dt⟩ := SyntaxContext.of_lookup copyLookup
  cases ct
  cases dt
  obtain ⟨a,localOriginal,hoa,_,_,pathsO⟩ :=
    C.reflectHistory original ho (by simpa only [cp] using lift.original_internal)
  obtain ⟨b,localCopy,hcb,_,_,pathsC⟩ :=
    D.reflectHistory copy hc (by simpa only [dp] using lift.copy_internal)
  have localOriginalPaths : localOriginal.derivation.paths=localPaths := by
    apply mapped_prefix_paths_injective (p++[.arg])
    rw [←cp,←pathsO]
    simpa only [cp] using originalPaths
  have localCopyPaths : localCopy.derivation.paths=localPaths := by
    apply mapped_prefix_paths_injective (p++occurrence)
    rw [←dp,←pathsC]
    simpa only [dp] using copyPaths
  refine ⟨C,D,.of localOriginal hoa,rfl,rfl,?_,?_⟩
  · apply ExtractionRun.ext_paths
    simp only [ExtractionRun.castSource_paths,C.liftRun_paths,ExtractionRun.of]
    exact pathsO
  · apply ExtractionRun.ext_paths
    simp only [ExtractionRun.castSource_paths,D.liftRun_paths,ExtractionRun.rename_paths,ExtractionRun.of]
    rw [pathsC,dp,localCopyPaths,localOriginalPaths]

theorem ExtractionNormal.castSource_iff (eq : t=u) (r : ExtractionRun t) :
    ExtractionNormal (r.castSource eq) ↔ ExtractionNormal r := by cases eq; rfl

/-- Normality of the designated argument copy implies normality of the
 original argument program. This uses actual context/shift transport. -/
theorem ArgumentLift.normal_original {R : BetaAt t p u}
    (lift : ArgumentLift R copy original) (hc : Atomic copy) (ho : Atomic original)
    (normal : ExtractionNormal (.of copy hc)) : ExtractionNormal (.of original ho) := by
  obtain ⟨C,D,program,ce,de,originalEq,copyEq⟩ := lift.run_contexts hc ho
  rw [copyEq] at normal
  have localNormal := (D.normal_of_lift ((ExtractionNormal.castSource_iff de _).mp normal)).rename_reflect
  rw [originalEq]
  exact (ExtractionNormal.castSource_iff ce _).mpr (localNormal.lift_context C)

end Lamping.Lambda
