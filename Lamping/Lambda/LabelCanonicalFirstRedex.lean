import Lamping.Lambda.LabelCanonicalSupport
namespace Lamping.Lambda.Labelled

/-- The actual first degree is supported by every predicate supporting the
last degree of the same canonical pointed history. -/
theorem History.canonical_first_support (head : StepAt p t middle)
    (rest : History ps middle u) (last : StepAt q u v) (initial : INIT t)
    (run : ExtractionRun t.erase) (canonical : CanonicalRun run)
    (paths : run.history.derivation.paths=p::(ps++[q]))
    (headDegree : t.degreeAt p=some alpha) (degree : u.degreeAt q=some l)
    (support : l.Supported region) : alpha.Supported region := by
  have colours := (History.cons head rest).canonical_degree_support last initial run canonical paths degree support
  cases colours with
  | cons step firstDegree firstSupport tail =>
    have equal := Option.some.inj (headDegree.symm.trans firstDegree)
    exact equal.symm ▸ firstSupport

/-- A canonical pointed run cannot have its final degree recursively avoid
its initial atomic head degree. Standardness is retained through CanonicalRun. -/
theorem History.canonical_head_not_silent (head : StepAt p t middle)
    (rest : History ps middle u) (last : StepAt q u v) (initial : INIT t)
    (run : ExtractionRun t.erase) (canonical : CanonicalRun run)
    (paths : run.history.derivation.paths=p::(ps++[q]))
    (headDegree : t.degreeAt p=some (Label.atom a)) (degree : u.degreeAt q=some l) :
    ¬l.Supported (fun n => n≠a) := by
  intro avoid
  exact (History.canonical_first_support head rest last initial run canonical paths headDegree degree avoid) rfl

/-- Exercise 6.2.15 for an arbitrary original argument occurrence and any
actual canonical pointed run, with no supplied per-event colour premise. -/
theorem History.canonical_argument_internal (prefixHistory : History ps t u) (last : StepAt q u v)
    (initial : INIT t) (run : ExtractionRun t.erase) (canonical : CanonicalRun run)
    (paths : run.history.derivation.paths=ps++[q]) (degree : u.degreeAt q=some l)
    (support : l.Supported (SourceRegion argument))
    (atHead : SourceSubterm [] .external t headSite env ctx (.app beta (.lam alpha body) argument)) :
    Internal (headSite++[.arg]) run.history := by
  have colours := prefixHistory.canonical_degree_support last initial run canonical paths degree support
  intro site member
  exact colours.argument_internal initial atHead site (paths ▸ member)

/-- The actual first event belongs to the finite source-degree candidate set.
The proper prefix is nonempty here; the one-event case is treated separately. -/
theorem History.canonical_first_candidate (head : StepAt p t middle)
    (rest : History ps middle u) (last : StepAt q u v) (initial : INIT t)
    (run : ExtractionRun t.erase) (canonical : CanonicalRun run)
    (paths : run.history.derivation.paths=p::(ps++[q])) (degree : u.degreeAt q=some l) :
    p∈degreeCandidates t l := by
  obtain ⟨alpha,headDegree⟩ := degreeAt_exists t ⟨p,head.betaAt.redex⟩
  obtain ⟨headBody,atLambda⟩ := LTerm.degreeAt_lambda headDegree
  obtain ⟨a,equal⟩ := initial.1 alpha (LTerm.label_mem_of_subterm atLambda)
  cases equal
  have supported : l.Supported (fun n => ∃ e∈l.edgeWord,e.atom=n) :=
    (Label.supported_iff_within _ _).mpr (fun e member => ⟨e,member,rfl⟩)
  have member := History.canonical_first_support head rest last initial run canonical paths headDegree degree supported
  exact (mem_degreeCandidates t l p).mpr
    ⟨(mem_redexPositions t.erase p).mpr head.betaAt.redex,a,headDegree,member⟩

/-- First Redex, with a nonempty proper prefix: the actual head is exactly
an LO degree candidate, for the same arbitrary INIT source and schedule. -/
theorem History.canonical_first_leftmost (head : StepAt p t middle)
    (rest : History ps middle u) (last : StepAt q u v) (initial : INIT t)
    (run : ExtractionRun t.erase) (canonical : CanonicalRun run)
    (paths : run.history.derivation.paths=p::(ps++[q])) (degree : u.degreeAt q=some l) :
    LeftmostSelected (degreeCandidates t l) (⟨p,head.betaAt.redex⟩ : RedexOcc t.erase) := by
  have candidate := History.canonical_first_candidate head rest last initial run canonical paths degree
  refine ⟨candidate,?_⟩
  intro other otherCandidate before
  obtain ⟨tail,ordinary,tailPaths⟩ := (rest.append (.cons last (.nil _))).betaHistory.atomic
  have runEq : run=ExtractionRun.of (.cons (singleContraction head.betaAt) tail) (.cons head.betaAt ordinary) := by
    apply ExtractionRun.ext_paths
    change run.history.derivation.paths=p::tail.derivation.paths
    rw [paths,tailPaths]
  rw [runEq] at canonical
  exact (History.cons head rest).candidate_not_left_of_head last initial degree head.betaAt tail ordinary
    (by change p::tail.derivation.paths=(p::ps)++[q]; rw [tailPaths]; rfl) canonical.2.1 other otherCandidate before
end Lamping.Lambda.Labelled
