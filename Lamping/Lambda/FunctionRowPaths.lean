import Lamping.Lambda.RegionProjectionHead
import Lamping.Lambda.ArgumentLiftSplits
namespace Lamping.Lambda

/-- Function-part projection removes precisely the outer function lambda's
 two path edges. The actual ordered ordinary program is retained. -/
theorem StepProjection.function_paths (R : BetaAt t p u)
    (row : StepProjection (singleContraction R) σ τ last)
    (ha : Atomic σ) (hb : Atomic τ) (inside : Internal (p++[.fn]) σ) :
    ∃program : List Path,σ.derivation.paths=program.map (fun q => (p++[.fn,.body])++q) ∧
      τ.derivation.paths=program.map (fun q => p++q) := by
  induction ha generalizing u with
  | nil =>
    cases hb with
    | nil => exact ⟨[],rfl,rfl⟩
    | cons B ht => have len := row.length; simp only [ParallelHistory.length] at len; omega
  | @cons t a v upperEnd upper A hu ih =>
    cases hb with
    | nil => have len := row.length; simp only [ParallelHistory.length] at len; omega
    | @cons u b w lowerEnd lower B hl =>
      have aInside : ∃q,a=(p++[.fn])++q := inside a
        (by change a∈a::upper.derivation.paths; exact List.mem_cons_self)
      have old := row.head_singleton_residual A B
      obtain ⟨q,source,target⟩ := R.function_residual_coordinates ⟨a,A.redex⟩ ⟨b,B.redex⟩ aInside old
      change a=(p++[.fn,.body])++q at source
      change b=p++q at target
      obtain ⟨R1,_,tailRow⟩ := row.region_head R A B (.inr rfl) aInside
      have upperInside : Internal (p++[.fn]) upper := by
        intro name hp
        exact inside name (by change name∈a::upper.derivation.paths; exact List.mem_cons_of_mem _ hp)
      obtain ⟨program,sourcePaths,targetPaths⟩ := ih R1 tailRow hl upperInside
      refine ⟨q::program,?_,?_⟩
      · change a::upper.derivation.paths=((p++[.fn,.body])++q)::program.map _
        rw [source,sourcePaths]
      · change b::lower.derivation.paths=(p++q)::program.map _
        rw [target,targetPaths]

/-- The same path formula restricted to a prescribed source subregion. -/
theorem StepProjection.function_paths_at (R : BetaAt t p u)
    {program : List Path}
    (row : StepProjection (singleContraction R) σ τ last)
    (ha : Atomic σ) (hb : Atomic τ) (inside : Internal (p++[.fn]) σ)
    (paths : σ.derivation.paths=program.map (fun q => ((p++[.fn,.body])++site)++q)) :
    τ.derivation.paths=program.map (fun q => (p++site)++q) := by
  obtain ⟨localProgram,sourcePaths,targetPaths⟩ := row.function_paths R ha hb inside
  have localEq : localProgram=program.map (fun q => site++q) := by
    apply mapped_prefix_paths_injective (p++[.fn,.body])
    rw [←sourcePaths,paths,List.map_map]
    simp only [Function.comp_def,List.append_assoc]
  rw [targetPaths,localEq,List.map_map]
  simp only [Function.comp_def,List.append_assoc]

/-- Conversely, the supplied bottom program fixes the unique old function
 program, with the two removed edges restored. -/
theorem StepProjection.function_paths_reflect_at (R : BetaAt t p u)
    {program : List Path}
    (row : StepProjection (singleContraction R) σ τ last)
    (ha : Atomic σ) (hb : Atomic τ) (inside : Internal (p++[.fn]) σ)
    (paths : τ.derivation.paths=program.map (fun q => (p++site)++q)) :
    σ.derivation.paths=program.map (fun q => ((p++[.fn,.body])++site)++q) := by
  obtain ⟨localProgram,sourcePaths,targetPaths⟩ := row.function_paths R ha hb inside
  have localEq : localProgram=program.map (fun q => site++q) := by
    apply mapped_prefix_paths_injective p
    rw [←targetPaths,paths,List.map_map]
    simp only [Function.comp_def,List.append_assoc]
  rw [sourcePaths,localEq,List.map_map]
  simp only [Function.comp_def,List.append_assoc]

end Lamping.Lambda
