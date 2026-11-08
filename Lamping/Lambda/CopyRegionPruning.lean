import Lamping.Lambda.CopyRegionAncestry
namespace Lamping.Lambda
theorem ProtectedBlocks.prune_function_pointed {ρ : ParallelHistory t u}
    (blocks : ProtectedBlocks cut ρ) (ordinary : Atomic ρ) (last : BetaAt u p v)
    (atFunction : p=(cut++[.fn])++q) :
    ∃ mid w, ∃ function : ParallelHistory t mid, ∃ initial : BetaAt mid p w,
      ∃ hf : Atomic function, Internal (cut++[.fn]) function ∧
      Pruning (.of (ρ.append (.single (singleContraction last))) (ordinary.append (.single last)))
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
  obtain ⟨w,initial,removed⟩ := Atomic.prune_apart_suffix function hf (ha.append forest.atomic) last apart
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

theorem ProtectedBlocks.prune_argument_pointed {ρ : ParallelHistory t u}
    (blocks : ProtectedBlocks cut ρ) (ordinary : Atomic ρ) (last : BetaAt u p v)
    (atArgument : p=(cut++[.arg])++q) :
    ∃ w, ∃ source : ParallelHistory t w, ∃ sourceAtomic : Atomic source,
      Internal (cut++[.arg]) source ∧
      Pruning (.of (ρ.append (.single (singleContraction last))) (ordinary.append (.single last)))
        (.of source sourceAtomic) := by
  obtain ⟨mid,endArg,function,argument,outside,hf,ha,whole,fi,ai,forest⟩ := blocks
  have apart : ∀ r∈outside.derivation.paths,DisjointPositions r p := by
    intro r hr
    rw [atArgument,List.append_assoc]
    exact forest.paths_apart_descendant ([.arg]++q) r hr
  obtain ⟨w,initial,removed⟩ := Atomic.prune_apart_suffix (function.append argument)
    (hf.append ha) forest.atomic last apart
  have programInside : Internal (cut++[.arg]) (argument.append (.single (singleContraction initial))) := by
    intro r hr
    rw [ParallelHistory.derivation_append] at hr
    change r∈argument.derivation.paths++[p] at hr
    rcases List.mem_append.mp hr with earlier | last
    · exact ai r earlier
    · exact ⟨q,(List.mem_singleton.mp last).trans atArgument⟩
  have functionApart : ∀ r∈function.derivation.paths,DisjointPositions r (cut++[.arg]) := by
    intro r hr
    obtain ⟨s,eq⟩ := fi r hr
    rw [eq]
    have base : DisjointPositions (cut++[.fn]) (cut++[.arg]) :=
      (DisjointPositions.head_ne (by intro eq; cases eq) : DisjointPositions [.fn] [.arg]).prefix cut
    exact base.descend_left s
  obtain ⟨z,source,sourceAtomic,_,sourceInside,removedFunction⟩ := hf.prune_disjoint_prefix
    (argument.append (.single (singleContraction initial))) (ha.append (.single initial)) programInside
    (by simp [ParallelHistory.length_append,ParallelHistory.single,ParallelHistory.length]) functionApart
  refine ⟨z,source,sourceAtomic,sourceInside,?_⟩
  have sourceEq : ExtractionRun.of (ρ.append (.single (singleContraction last))) (ordinary.append (.single last)) =
      .of (((function.append argument).append outside).append (.single (singleContraction last)))
        (((hf.append ha).append forest.atomic).append (.single last)) := by
    apply ExtractionRun.ext_paths
    change (ρ.append (.single (singleContraction last))).derivation.paths =
      (((function.append argument).append outside).append (.single (singleContraction last))).derivation.paths
    simp only [whole,ParallelHistory.append_assoc]
  have middleEq : ExtractionRun.of ((function.append argument).append (.single (singleContraction initial)))
      ((hf.append ha).append (.single initial)) =
      .of (function.append (argument.append (.single (singleContraction initial))))
        (hf.append (ha.append (.single initial))) := by
    apply ExtractionRun.ext_paths
    simp only [ExtractionRun.of,ParallelHistory.derivation_append,Derivation.append,List.append_assoc]
  rw [sourceEq]
  exact removed.trans (by rw [middleEq]; exact removedFunction)

theorem Atomic.prune_local_program {ρ : ParallelHistory t u} (ordinary : Atomic ρ)
    (last : BetaAt u p v) (atSite : p=site++q)
    (geometry : ∀ r∈ρ.derivation.paths,(∃s,r=site++s) ∨ DisjointPositions r site) :
    ∃ w, ∃ source : ParallelHistory t w, ∃ sourceAtomic : Atomic source,
      0<source.length ∧ Internal site source ∧
      Pruning (.of (ρ.append (.single (singleContraction last))) (ordinary.append (.single last)))
        (.of source sourceAtomic) := by
  induction ordinary with
  | nil t =>
    refine ⟨v,.single (singleContraction last), .single last,(by simp [ParallelHistory.single,ParallelHistory.length]),?_,.refl _⟩
    intro r hr
    have eq : r=p := by simpa [ParallelHistory.single_derivation,ParallelStep.derivation,singleContraction] using hr
    exact ⟨q,eq.trans atSite⟩
  | @cons t r mid u tail R atomic ih =>
    have tailGeometry : ∀ s∈tail.derivation.paths,(∃a,s=site++a) ∨ DisjointPositions s site := by
      intro s hs; exact geometry s (by simp [ParallelHistory.derivation,Derivation.append,hs])
    obtain ⟨w,middle,middleAtomic,positive,inside,removed⟩ := ih last tailGeometry
    have headGeometry := geometry r (by
      simp [ParallelHistory.derivation,Derivation.append,ParallelStep.derivation,singleContraction])
    have first := removed.prepend (.single (singleContraction R)) (.single R)
    rcases headGeometry with atHead | separate
    · refine ⟨w,.cons (singleContraction R) middle,.cons R middleAtomic,?_,?_,?_⟩
      · simp only [ParallelHistory.length]; omega
      · intro s hs
        change s∈r::middle.derivation.paths at hs
        rcases List.mem_cons.mp hs with eq | later
        · obtain ⟨a,eq'⟩ := atHead
          exact ⟨a,eq.trans eq'⟩
        · exact inside s later
      · simpa only [ExtractionRun.prepend,ExtractionRun.of,ParallelHistory.single,ParallelHistory.append] using first
    · obtain ⟨z,source,sourceAtomic,paths,sourceInside,second⟩ := (Atomic.single R).prune_disjoint_prefix
        middle middleAtomic inside positive (by
          intro s hs
          have eq : s=r := by simpa [ParallelHistory.single_derivation,ParallelStep.derivation,singleContraction] using hs
          simpa [eq] using separate)
      have sourcePositive : 0<source.length := by
        have eq := congrArg List.length paths
        rw [sourceAtomic.paths_length,middleAtomic.paths_length] at eq
        omega
      refine ⟨z,source,sourceAtomic,sourcePositive,sourceInside,?_⟩
      exact .trans (by simpa only [ExtractionRun.prepend,ExtractionRun.of,ParallelHistory.single,ParallelHistory.append] using first) second

/-- AG5.2.9's right-disjoint source region is an actual single sibling
program, selected from the final occurrence rather than assumed for the
whole outside forest. -/
theorem RightHistory.prune_right_pointed {ρ : ParallelHistory t u}
    (right : RightHistory cut ρ) (ordinary : Atomic ρ) (last : BetaAt u p v)
    (before : LeftOf cut p) (apart : DisjointPositions cut p) :
    ∃ site, DisjointPositions cut site ∧
      ∃ w, ∃ source : ParallelHistory t w, ∃ sourceAtomic : Atomic source,
        0<source.length ∧ Internal site source ∧
        Pruning (.of (ρ.append (.single (singleContraction last))) (ordinary.append (.single last)))
          (.of source sourceAtomic) := by
  obtain ⟨site,q,atSite,separate,geometry⟩ := before.right_sibling apart
  obtain ⟨w,source,sourceAtomic,positive,inside,removed⟩ := ordinary.prune_local_program last atSite (by
    intro r hr; exact geometry r (right.paths_right r hr))
  exact ⟨site,separate,w,source,sourceAtomic,positive,inside,removed⟩

end Lamping.Lambda

