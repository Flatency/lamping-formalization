import Lamping.Lambda.LabelRegions
import Lamping.Lambda.RightSiblingExtraction
import Lamping.Lambda.ExtractionClosure
import Lamping.Lambda.ExtractionAtRoot
namespace Lamping.Lambda.Labelled

/-- In an extraction normal pointed program, a region containing the final
contraction also contains the whole program whenever each earlier contraction
is actually internal or disjoint. The proof uses the original extraction rules
via extract_local_program, not a region closure assumption on canonical forms. -/
theorem normal_internal_of_geometry {program : ParallelHistory m n}
    (ordinary : Atomic program) (last : BetaAt n p u)
    (normal : ExtractionNormal (.of (program.append (.single (singleContraction last)))
      (ordinary.append (.single last))))
    (atSite : p=site++suffix)
    (geometry : ∀ q∈program.derivation.paths,
      (∃ s,q=site++s) ∨ DisjointPositions q site) :
    Internal site (program.append (.single (singleContraction last))) := by
  obtain ⟨w,source,atomic,positive,inside,extraction⟩ :=
    ordinary.extract_local_program last atSite geometry
  have same := normal.target_eq extraction
  have paths := congrArg (fun r : ExtractionRun m => r.history.derivation.paths) same
  change (program.append (.single (singleContraction last))).derivation.paths=source.derivation.paths at paths
  intro q member
  apply inside q
  change q∈source.derivation.paths
  rw [←paths]
  exact member

/-- A normal headed program cannot continue wholly inside one specified
argument copy. The mirrored original program and rule-(iv) lift are actually
constructed from that internal schedule. -/
theorem normal_head_not_argument_copy (head : BetaAt m p n)
    (redex : subtermAt m p=some (.app (.lam body) argument))
    (occurs : ArgumentOccurrence body occurrence)
    (program : ParallelHistory n u) (ordinary : Atomic program)
    (positive : 0<program.length)
    (normal : ExtractionNormal (.of (.cons (singleContraction head) program)
      (.cons head ordinary))) :
    ¬ Internal (p++occurrence) program := by
  intro inside
  obtain ⟨w,original,atomic,lift,_⟩ :=
    argument_lift_exists head redex occurs program inside
  exact normal ⟨_,(RootExtraction.argumentPart program ordinary original atomic positive lift).step⟩

theorem normal_head_not_disjoint_internal (head : BetaAt m p n)
    (program : ParallelHistory n u) (ordinary : Atomic program)
    (positive : 0<program.length) (apart : DisjointPositions p site)
    (normal : ExtractionNormal (.of (.cons (singleContraction head) program)
      (.cons head ordinary))) :
    ¬ Internal site program := by
  intro inside
  obtain ⟨w,source,atomic,paths,sourceInside,extraction⟩ :=
    (Atomic.single head).extract_disjoint_prefix program ordinary inside positive (by
      intro q member
      have eq : q=p := by
        simpa [ParallelHistory.single_derivation,ParallelStep.derivation,singleContraction] using member
      simpa [eq] using apart)
  have same := normal.target_eq (by
    simpa only [ParallelHistory.single,ParallelHistory.append,Atomic.append] using extraction)
  have schedules := congrArg (fun r : ExtractionRun m => r.history.derivation.paths) same
  change p::program.derivation.paths=source.derivation.paths at schedules
  rw [paths] at schedules
  have lengths := congrArg List.length schedules
  simp only [List.length_cons] at lengths
  omega

/-- Canonicality of a nonempty actual suffix follows from the proved
ordinary-prefix lifting of each extraction rule and standard-history suffix
restriction. No arbitrary reindexing of extraction steps is assumed. -/
theorem canonical_of_prepend (pre : ParallelHistory m n) (ordinary : Atomic pre)
    (tail : ExtractionRun n) (positive : 0<tail.rank)
    (canonical : CanonicalRun (tail.prepend pre ordinary)) : CanonicalRun tail := by
  refine ⟨positive,?_,?_⟩
  · exact Standard.suffix canonical.2.1
  · exact ExtractionNormal.of_prepend canonical.2.2

end Lamping.Lambda.Labelled

