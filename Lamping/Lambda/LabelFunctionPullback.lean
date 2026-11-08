import Lamping.Lambda.ExtractionAtRoot
import Lamping.Lambda.LabelRegionalBodyPullback
import Lamping.Lambda.AtomicRowExistence
import Lamping.Lambda.FunctionRowPaths
namespace Lamping.Lambda.Labelled

/-- Build the actual rule-(iii) projection row for a supplied old-body
program. Its projected schedule is exactly the supplied body schedule. -/
theorem body_program_function_projection (program : BetaHistory ps body target) (argument : Term) :
    ∃ (v : Term) (original : ParallelHistory (.app (.lam body) argument) v),
      ∃ _ordinary : Atomic original,
      Internal [.fn] original ∧
      original.derivation.paths=ps.map (fun q => [.fn,.body]++q) ∧
      ∃ (w : Term) (G : List Path) (projected : ParallelHistory (contract body argument) w)
        (last : ParallelStep G v w), Atomic projected ∧
        StepProjection (singleContraction (show BetaAt (.app (.lam body) argument) [] (contract body argument) from
          ⟨body,argument,rfl,rfl⟩)) original projected last ∧ projected.derivation.paths=ps := by
  obtain ⟨v,lifted,_⟩ := program.prefix_lift
    (t := .app (.lam body) argument) (site := [.fn,.body]) (by simp [subtermAt])
  obtain ⟨original,ordinary,paths⟩ := lifted.atomic
  have inside : Internal [.fn] original := by
    intro p member
    rw [paths] at member
    obtain ⟨q,_,same⟩ := List.mem_map.mp member
    exact ⟨.body::q,same.symm⟩
  let head : BetaAt (.app (.lam body) argument) [] (contract body argument) := ⟨body,argument,rfl,rfl⟩
  obtain ⟨w,G,projected,last,projectedAtomic,row⟩ := ordinary.function_projection head inside
  obtain ⟨qs,upper,lower⟩ := row.function_paths head ordinary projectedAtomic inside
  have same : qs=ps := mapped_prefix_paths_injective [.fn,.body] (upper.symm.trans paths)
  refine ⟨v,original,ordinary,inside,paths,w,G,projected,last,projectedAtomic,row,?_⟩
  simpa [same] using lower

/-- An actual nonempty old-body program makes the corresponding headed
beta program reducible by the original function-part extraction rule. The
projection is built above, then matched to the supplied actual tail by its
entire ordered schedule. -/
theorem body_program_not_normal (program : BetaHistory ps body target)
    (tail : ParallelHistory (contract body argument) final) (ordinary : Atomic tail)
    (paths : tail.derivation.paths=ps) (positive : 0<ps.length) :
    ¬ExtractionNormal (.of (.cons (singleContraction
      (show BetaAt (.app (.lam body) argument) [] (contract body argument) from ⟨body,argument,rfl,rfl⟩)) tail)
      (.cons ⟨body,argument,rfl,rfl⟩ ordinary)) := by
  intro normal
  obtain ⟨v,original,originalAtomic,inside,upper,w,G,projected,last,projectedAtomic,row,lower⟩ :=
    body_program_function_projection program argument
  let head : BetaAt (.app (.lam body) argument) [] (contract body argument) := ⟨body,argument,rfl,rfl⟩
  have originalPositive : 0<original.length := by
    have lengths := congrArg List.length upper
    rw [originalAtomic.paths_length,List.length_map] at lengths
    omega
  have extraction := (RootExtraction.functionPart (R := head) original originalAtomic projected projectedAtomic last row
    originalPositive inside).step
  have sourceEq : ExtractionRun.of (.cons (singleContraction head) projected) (.cons head projectedAtomic)=
      ExtractionRun.of (.cons (singleContraction head) tail) (.cons head ordinary) := by
    apply ExtractionRun.ext_paths
    change []::projected.derivation.paths=[]::tail.derivation.paths
    rw [lower,paths]
  change ExtractionStep (ExtractionRun.of (.cons (singleContraction head) projected) (.cons head projectedAtomic))
    (ExtractionRun.of original originalAtomic) at extraction
  rw [sourceEq] at extraction
  exact normal ⟨_,extraction⟩

/-- A real regional post-beta history with outside-only arguments supplies
the old-body program required by rule (iii). The caller supplies an actual
ordinary presentation of that same complete schedule. -/
theorem RegionalHistory.contract_not_normal
    (regional : RegionalHistory region ps (LTerm.contract beta alpha body argument) u)
    (outside : LTerm.OutsideRegion region argument) (positive : 0<ps.length)
    (tail : ParallelHistory (contract body.erase argument.erase) final) (ordinary : Atomic tail)
    (paths : tail.derivation.paths=ps) :
    ¬ExtractionNormal (.of (.cons (singleContraction
      (show BetaAt (.app (.lam body.erase) argument.erase) [] (contract body.erase argument.erase) from
        ⟨body.erase,argument.erase,rfl,rfl⟩)) tail)
      (.cons ⟨body.erase,argument.erase,rfl,rfl⟩ ordinary)) := by
  obtain ⟨oldTarget,program,_⟩ := regional.contract_body_reflect outside
  exact body_program_not_normal program.betaHistory tail ordinary paths positive
end Lamping.Lambda.Labelled







