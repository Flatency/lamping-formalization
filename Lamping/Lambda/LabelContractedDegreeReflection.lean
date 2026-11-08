import Lamping.Lambda.LabelAnchoredWalkReflection
import Lamping.Lambda.LabelCanonicalFirstRedex
namespace Lamping.Lambda.Labelled

/-- Canonicality supplies a real non-argument image anchor in the actual
local degree. Otherwise every local edge image would support the old
argument, forcing the original fired head degree into that disjoint region. -/
theorem History.canonical_degree_image_anchor {body argument : LTerm} {localDegree : Label}
    (head : StepAt p t middle) (rest : History ps middle u) (last : StepAt q u v)
    (initial : INIT t) (source : t.subterm p=some (.app beta (.lam alpha body) argument))
    (run : ExtractionRun t.erase) (canonical : CanonicalRun run)
    (paths : run.history.derivation.paths=p::(ps++[q]))
    (degree : u.degreeAt q=some l) (localImage : localDegree.relabel (initialRelabelling middle 0)=l) :
    ∃ e∈localDegree.edgeWord,¬(initialRelabelling middle 0 e.atom).Supported (SourceRegion argument) := by
  classical
  apply Classical.byContradiction
  intro absent
  have wordSupport : EdgeWord.Within (fun n => (initialRelabelling middle 0 n).Supported (SourceRegion argument)) localDegree.edgeWord := by
    intro e member
    apply Classical.byContradiction
    intro outside
    exact absent ⟨e,member,outside⟩
  have localSupport := (Label.supported_iff_within _ localDegree).mpr wordSupport
  have globalSupport : l.Supported (SourceRegion argument) :=
    localImage ▸ (Label.supported_relabel _ _ localDegree).mpr localSupport
  have headDegree : t.degreeAt p=some alpha := by simp [LTerm.degreeAt,source,LTerm.degree]
  have headSupport := History.canonical_first_support head rest last initial run canonical paths headDegree degree globalSupport
  obtain ⟨a,atomic⟩ := initial.1 alpha (by
    exact LTerm.labels_subset_of_subterm source alpha (List.mem_cons_of_mem _ (List.mem_append_left _ List.mem_cons_self)))
  have argumentMember : alpha∈argument.labels := by cases atomic; exact headSupport
  have headInitial := initial.subterm source
  have apart := (List.nodup_append.mp (List.nodup_cons.mp headInitial.2).2).2.2
  exact apart alpha List.mem_cons_self alpha argumentMember rfl

/-- Contracted Label (AG6.2.12): after the same actual first beta, equal
original global degrees reflect to equal degrees in the common local INIT
basis. Only the left whole pointed run needs canonicality; the right is any
actual same-source tail. The original global labels are never reset. -/
theorem StepAt.canonical_same_degree_local_reflection {localLeft localRight : Label}
    (head : StepAt p t middle) (initial : INIT t)
    (left : History ps middle u) (leftBasis : History ps (initLabels middle.erase) z)
    (last : StepAt q u final)
    (right : History qs middle v) (rightBasis : History qs (initLabels middle.erase) z')
    (run : ExtractionRun t.erase) (canonical : CanonicalRun run)
    (paths : run.history.derivation.paths=p::(ps++[q]))
    (leftDegree : u.degreeAt q=some l) (leftLocal : z.degreeAt q=some localLeft)
    (rightDegree : v.degreeAt r=some l) (rightLocal : z'.degreeAt r=some localRight) :
    localLeft=localRight := by
  obtain ⟨beta,alpha,body,argument,source,_⟩ := head.head_lookups
  have headDegree : t.degreeAt p=some alpha := by simp [LTerm.degreeAt,source,LTerm.degree]
  obtain ⟨a,atomic⟩ := initial.1 alpha (by
    exact LTerm.labels_subset_of_subterm source alpha (List.mem_cons_of_mem _ (List.mem_append_left _ List.mem_cons_self)))
  have atomicHeadDegree : t.degreeAt p=some (Label.atom a) := by simpa only [atomic] using headDegree
  have image : localLeft.relabel (initialRelabelling middle 0)=l :=
    Option.some.inj ((left.local_degree_transport leftBasis leftLocal).1.symm.trans leftDegree)
  obtain ⟨appId,lamId,leftRoute⟩ := (leftBasis.generated_source_routes (init_is_INIT _)).degree_route leftLocal
  obtain ⟨appId',lamId',rightRoute⟩ := (rightBasis.generated_source_routes (init_is_INIT _)).degree_route rightLocal
  have sameCodeImage := head.same_degree_imageCode initial atomicHeadDegree left leftBasis right rightBasis leftDegree leftLocal rightDegree rightLocal false
  have anchor := History.canonical_degree_image_anchor head left last initial source run canonical paths leftDegree image
  obtain ⟨tail,ordinary,tailPaths⟩ := (left.append (.cons last (.nil _))).betaHistory.atomic
  have runEq : run=ExtractionRun.of (.cons (singleContraction head.betaAt) tail) (.cons head.betaAt ordinary) := by
    apply ExtractionRun.ext_paths
    change run.history.derivation.paths=p::tail.derivation.paths
    rw [paths,tailPaths]
  have standard : Standard (.cons (singleContraction head.betaAt) tail) := by
    rw [runEq] at canonical
    exact canonical.2.1
  have wholePaths : (ParallelHistory.cons (singleContraction head.betaAt) tail).derivation.paths=(p::ps)++[q] := by
    change p::tail.derivation.paths=(p::ps)++[q]
    rw [tailPaths]
    rfl
  have reflected := (History.cons head left).standard_anchored_degree_code_reflection head initial source last
    tail ordinary standard wholePaths leftDegree image leftRoute.pathCode rightRoute.pathCode sameCodeImage anchor
  exact Label.pathCode_injective false reflected.2.2
end Lamping.Lambda.Labelled
