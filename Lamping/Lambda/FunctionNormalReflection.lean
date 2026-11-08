import Lamping.Lambda.SubstitutionExtraction
import Lamping.Lambda.SyntaxContextComposition
import Lamping.Lambda.ArgumentRunContexts
namespace Lamping.Lambda

/-- A function-part projection reflects extraction normality. Its local
 bottom is the actual substituted body program, with the same ordered paths. -/
theorem StepProjection.function_normal_reflect (R : BetaAt t p u)
    (row : StepProjection (singleContraction R) original projected last)
    (ho : Atomic original) (hp : Atomic projected)
    (inside : Internal (p++[.fn]) original)
    (normal : ExtractionNormal (.of projected hp)) : ExtractionNormal (.of original ho) := by
  obtain ⟨body,arg,lookup,replaced⟩ := R
  let R : BetaAt t p u := ⟨body,arg,lookup,replaced⟩
  obtain ⟨C,cp,ct⟩ := SyntaxContext.of_lookup lookup
  cases ct
  let root : BetaAt (.app (.lam body) arg) [] (contract body arg) := ⟨body,arg,rfl,rfl⟩
  have lifted : BetaAt (C.plug (.app (.lam body) arg)) p (C.plug (contract body arg)) := by
    simpa only [cp,List.append_nil] using C.liftBeta root
  have endpoint := R.unique lifted
  cases endpoint
  obtain ⟨program,sourcePaths,targetPaths⟩ := row.function_paths R ho hp inside
  let E := C.compose (.frame (.fn arg) (.frame .body .hole))
  have ep : E.path=p++[.fn,.body] := by
    simp only [E,C.compose_path,cp,SyntaxContext.path,SyntaxFrame.edge]
  have et : E.plug body=C.plug (.app (.lam body) arg) := by
    simp only [E,C.compose_plug]
    rfl
  have originalScope : Internal E.path original := by
    intro name hq
    rw [sourcePaths] at hq
    obtain ⟨q,_,he⟩ := List.mem_map.mp hq
    exact ⟨q,by simpa only [ep] using he.symm⟩
  have projectedScope : Internal C.path projected := by
    intro name hq
    rw [targetPaths] at hq
    obtain ⟨q,_,he⟩ := List.mem_map.mp hq
    exact ⟨q,by simpa only [cp] using he.symm⟩
  have sourceLookup : subtermAt (C.plug (.app (.lam body) arg)) E.path=some body := by
    rw [←et]
    exact E.lookup body
  obtain ⟨originalProgram,a,pathsO,localHistory,_⟩ := originalScope.extract sourceLookup
  obtain ⟨ordinary,localAtomic,localPaths⟩ := localHistory.atomic
  let localRun : ExtractionRun body := .of ordinary localAtomic
  obtain ⟨b,localProjected,hpb,_,_,pathsP⟩ := C.reflectHistory projected hp projectedScope
  have localProgram : ordinary.derivation.paths=program := by
    apply mapped_prefix_paths_injective (p++[.fn,.body])
    rw [localPaths,←ep,←pathsO]
    simpa only [ep] using sourcePaths
  have projectedProgram : localProjected.derivation.paths=program := by
    apply mapped_prefix_paths_injective p
    rw [←cp,←pathsP]
    simpa only [cp] using targetPaths
  have projectedEq : ExtractionRun.of projected hp=C.liftRun (.of localProjected hpb) := by
    apply ExtractionRun.ext_paths
    rw [C.liftRun_paths]
    exact pathsP
  have substitutedEq : ExtractionRun.of localProjected hpb=localRun.subst (singleSub arg) := by
    apply ExtractionRun.ext_paths
    rw [ExtractionRun.subst_paths]
    exact projectedProgram.trans localProgram.symm
  rw [projectedEq] at normal
  have localNormal := C.normal_of_lift normal
  rw [substitutedEq] at localNormal
  have originalNormal := localNormal.subst_reflect
  have originalEq : ExtractionRun.of original ho=
      (E.liftRun localRun).castSource et := by
    apply ExtractionRun.ext_paths
    rw [ExtractionRun.castSource_paths,E.liftRun_paths]
    apply pathsO.trans
    change originalProgram.map (fun q => E.path++q)=ordinary.derivation.paths.map (fun q => E.path++q)
    rw [localPaths]
  rw [originalEq]
  exact (ExtractionNormal.castSource_iff et _).mpr (originalNormal.lift_context E)

end Lamping.Lambda
