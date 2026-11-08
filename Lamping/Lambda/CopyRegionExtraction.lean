import Lamping.Lambda.StandardProtectedBlocks
import Lamping.Lambda.CopyInitialExtraction
namespace Lamping.Lambda

/-- A final occurrence disjoint from every actual contraction has its
unique-position actual old ancestor, recovered backwards through the program. -/
theorem Atomic.apart_pointed_ancestor {ρ : ParallelHistory t u} (ordinary : Atomic ρ)
    (last : RedexOcc u)
    (apart : ∀ p∈ρ.derivation.paths,DisjointPositions p last.val) :
    ∃ initial : RedexOcc t, initial.val=last.val ∧ ρ.derivation.Residual initial last := by
  induction ordinary with
  | nil t => exact ⟨last,rfl,(Derivation.residual_nil last last).mpr rfl⟩
  | @cons t p mid u tail head atomic ih =>
    have tailApart : ∀ q∈tail.derivation.paths,DisjointPositions q last.val := by
      intro q hq; exact apart q (by simp [ParallelHistory.derivation,Derivation.append,hq])
    obtain ⟨middle,same,rest⟩ := ih last tailApart
    have headApart : DisjointPositions p middle.val := by
      rw [same]
      exact apart p (by simp [ParallelHistory.derivation,Derivation.append,ParallelStep.derivation,singleContraction])
    obtain ⟨initial,firstSame,first⟩ := head.disjoint_initial_ancestor middle headApart
    exact ⟨initial,firstSame.trans same,by
      change (singleContraction head).derivation.append tail.derivation |>.Residual initial last
      exact (Derivation.residual_append _ _ initial last).mpr ⟨middle,first,rest⟩⟩

/-- Delete an arbitrary actual disjoint suffix by genuine residual extraction
steps. The redex at the shorter pre is constructed, not supplied. -/
theorem Atomic.extract_apart_suffix (pre : ParallelHistory m t) (prefixAtomic : Atomic pre)
    {suffix : ParallelHistory t u} (ordinary : Atomic suffix) (last : BetaAt u p v)
    (apart : ∀ q∈suffix.derivation.paths,DisjointPositions q p) :
    ∃ w, ∃ initial : BetaAt t p w,
      Extraction (.of ((pre.append suffix).append (.single (singleContraction last)))
        ((prefixAtomic.append ordinary).append (.single last)))
        (.of (pre.append (.single (singleContraction initial))) (prefixAtomic.append (.single initial))) := by
  obtain ⟨ancestor,same,residual⟩ := ordinary.apart_pointed_ancestor ⟨p,last.redex⟩ apart
  change ancestor.val=p at same
  obtain ⟨w,initial⟩ := ancestor.contract_exists
  have atP : BetaAt t p w := by rw [←same]; exact initial
  have removed := (ordinary.extract_initial_residual ancestor last residual initial).prepend pre prefixAtomic
  refine ⟨w,atP,?_⟩
  have sourceEq : ExtractionRun.prepend pre prefixAtomic
      (.of (suffix.append (.single (singleContraction last))) (ordinary.append (.single last))) =
      .of ((pre.append suffix).append (.single (singleContraction last)))
        ((prefixAtomic.append ordinary).append (.single last)) := by
    apply ExtractionRun.ext_paths
    simp only [ExtractionRun.prepend,ExtractionRun.of,ParallelHistory.derivation_append,Derivation.append,List.append_assoc]
  have targetEq : ExtractionRun.prepend pre prefixAtomic
      (.of (.single (singleContraction initial)) (.single initial)) =
      .of (pre.append (.single (singleContraction atP))) (prefixAtomic.append (.single atP)) := by
    apply ExtractionRun.ext_paths
    simp only [ExtractionRun.prepend,ExtractionRun.of,ParallelHistory.derivation_append,
      Derivation.append,ParallelHistory.single_derivation,ParallelStep.derivation,singleContraction]
    rw [same]
  rw [sourceEq,targetEq] at removed
  exact removed

theorem DisjointBlocks.paths_apart_descendant (blocks : DisjointBlocks cut ρ)
    (p : Path) : ∀ q∈ρ.derivation.paths,DisjointPositions q (cut++p) := by
  induction blocks with
  | nil t => intro q hq; cases hq
  | @cons t v u site phase tail ordinary inside apart rest ih =>
    intro q hq
    rw [ParallelHistory.derivation_append] at hq
    change q∈phase.derivation.paths++tail.derivation.paths at hq
    rcases List.mem_append.mp hq with first | later
    · obtain ⟨r,eq⟩ := inside q first
      rw [eq]
      exact (apart.descend_left p).symm.descend_left r
    · exact ih q later

/-- A final redex in the protected function part permits deletion of all
actual argument and disjoint phases, keeping its genuine function ancestor. -/
theorem ProtectedBlocks.extract_function_pointed {ρ : ParallelHistory t u}
    (blocks : ProtectedBlocks cut ρ) (ordinary : Atomic ρ) (last : BetaAt u p v)
    (atFunction : p=(cut++[.fn])++q) :
    ∃ mid w, ∃ function : ParallelHistory t mid, ∃ initial : BetaAt mid p w,
      ∃ hf : Atomic function, Internal (cut++[.fn]) function ∧
      Extraction (.of (ρ.append (.single (singleContraction last))) (ordinary.append (.single last)))
        (.of (function.append (.single (singleContraction initial)))
          (hf.append (.single initial))) := by
  obtain ⟨mid,endArg,function,argument,outside,hf,ha,whole,fi,ai,forest⟩ := blocks
  have apart : ∀ r∈(argument.append outside).derivation.paths,DisjointPositions r p := by
    intro r hr
    rw [ParallelHistory.derivation_append] at hr
    change r∈argument.derivation.paths++outside.derivation.paths at hr
    rcases List.mem_append.mp hr with first | later
    · obtain ⟨s,eq⟩ := ai r first
      rw [eq,atFunction]
      have base : DisjointPositions (cut++[.arg]) (cut++[.fn]) :=
        (DisjointPositions.head_ne (by intro eq; cases eq) : DisjointPositions [.arg] [.fn]).prefix cut
      exact ((base.descend_left s).symm.descend_left q).symm
    · rw [atFunction,List.append_assoc]
      exact forest.paths_apart_descendant ([.fn]++q) r later
  obtain ⟨w,initial,removed⟩ := Atomic.extract_apart_suffix function hf (ha.append forest.atomic) last apart
  refine ⟨mid,w,function,initial,hf,fi,?_⟩
  have sourceEq : ExtractionRun.of (ρ.append (.single (singleContraction last))) (ordinary.append (.single last)) =
      .of ((function.append (argument.append outside)).append (.single (singleContraction last)))
        ((hf.append (ha.append forest.atomic)).append (.single last)) := by
    apply ExtractionRun.ext_paths
    change (ρ.append (.single (singleContraction last))).derivation.paths =
      ((function.append (argument.append outside)).append (.single (singleContraction last))).derivation.paths
    rw [whole]
  rw [sourceEq]
  exact removed

end Lamping.Lambda

