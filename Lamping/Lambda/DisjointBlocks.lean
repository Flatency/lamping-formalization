import Lamping.Lambda.StandardBlockReflection
namespace Lamping.Lambda

/-- A finite forest of actual ordinary phases in subtrees disjoint from a
protected position. Only source geometry and actual programs are recorded. -/
inductive DisjointBlocks (cut : Path) : ParallelHistory t u → Prop where
  | nil (t) : DisjointBlocks cut (.nil t)
  | cons {phase : ParallelHistory t v} {tail : ParallelHistory v u}
      (ordinary : Atomic phase) (inside : Internal site phase)
      (apart : DisjointPositions cut site) (rest : DisjointBlocks cut tail) :
      DisjointBlocks cut (phase.append tail)

theorem DisjointPositions.prefix (apart : DisjointPositions p q) (pre : Path) :
    DisjointPositions (pre++p) (pre++q) := by
  induction pre with
  | nil => exact apart
  | cons s pre ih => exact ih.cons s

theorem DisjointBlocks.atomic (blocks : DisjointBlocks cut ρ) : Atomic ρ := by
  induction blocks with
  | nil t => exact .nil t
  | cons ordinary _ _ _ ih => exact ordinary.append ih

theorem DisjointBlocks.append (first : DisjointBlocks cut ρ)
    (last : DisjointBlocks cut σ) : DisjointBlocks cut (ρ.append σ) := by
  induction first with
  | nil => exact last
  | cons ordinary inside apart rest ih =>
    rw [ParallelHistory.append_assoc]
    exact .cons ordinary inside apart (ih last)

/-- Lift a forest into a given contextual ordinary schedule. The actual
global intermediate terms and phases are obtained by schedule splitting. -/
theorem DisjointBlocks.mapped {ρ : ParallelHistory a b} (blocks : DisjointBlocks cut ρ)
    {global : ParallelHistory T U} (ordinary : Atomic global)
    (paths : global.derivation.paths=ρ.derivation.paths.map (fun p => pre++p)) :
    DisjointBlocks (pre++cut) global := by
  induction blocks generalizing T U with
  | nil a =>
    cases ordinary with
    | nil T => exact .nil T
    | cons head rest => change _::_=[] at paths; cases paths
  | @cons a v b site phase tail phaseAtomic inside apart rest ih =>
    obtain ⟨M,first,last,firstAtomic,lastAtomic,whole,_,firstPaths,lastPaths⟩ :=
      ordinary.split_mapped_program phaseAtomic rest.atomic paths
    rw [whole]
    refine .cons firstAtomic ?_ (apart.prefix pre) (ih lastAtomic lastPaths)
    intro p hp
    rw [firstPaths] at hp
    obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hp
    obtain ⟨r,eq⟩ := inside q hq
    exact ⟨r,by rw [eq,List.append_assoc]⟩

end Lamping.Lambda

