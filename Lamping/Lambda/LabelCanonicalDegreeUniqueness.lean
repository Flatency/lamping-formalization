import Lamping.Lambda.LabelContractedDegreeReflection
import Lamping.Lambda.LabelAtomicFamilies
namespace Lamping.Lambda.Labelled

private theorem canonical_atomic_prefix_empty
    (history : History ps t u) (last : StepAt q u v)
    (run : ExtractionRun t.erase) (canonical : CanonicalRun run)
    (paths : run.history.derivation.paths=ps++[q])
    (degree : u.degreeAt q=some l) (atomic : IsAtomic l) : ps=[] := by
  obtain ⟨program,ordinary,programPaths⟩ := history.betaHistory.atomic
  have runEq : run=ExtractionRun.of (program.append (.single (singleContraction last.betaAt))) (ordinary.append (.single last.betaAt)) := by
    apply ExtractionRun.ext_paths
    change run.history.derivation.paths=(program.append (.single (singleContraction last.betaAt))).derivation.paths
    rw [ParallelHistory.derivation_append]
    change run.history.derivation.paths=program.derivation.paths++[q]
    rw [paths,programPaths]
  have labelled : History program.derivation.paths t u := programPaths.symm ▸ history
  have normal := canonical.2.2
  rw [runEq] at normal
  have empty := labelled.atomic_degree_normal_prefix_empty program ordinary last.betaAt normal degree atomic
  have lengths := congrArg List.length programPaths
  rw [ordinary.paths_length,empty] at lengths
  exact List.eq_nil_of_length_eq_zero lengths.symm

private theorem canonical_tail {t middle u v : LTerm}
    (head : StepAt p t middle) (rest : History ps middle u) (last : StepAt q u v)
    (run : ExtractionRun t.erase) (canonical : CanonicalRun run)
    (paths : run.history.derivation.paths=p::(ps++[q])) :
    ∃ tailRun : ExtractionRun middle.erase,CanonicalRun tailRun ∧ tailRun.history.derivation.paths=ps++[q] := by
  obtain ⟨tail,ordinary,tailPaths⟩ := (rest.append (.cons last (.nil _))).betaHistory.atomic
  have runEq : run=ExtractionRun.of (.cons (singleContraction head.betaAt) tail) (.cons head.betaAt ordinary) := by
    apply ExtractionRun.ext_paths
    change run.history.derivation.paths=p::tail.derivation.paths
    rw [paths,tailPaths]
  rw [runEq] at canonical
  have positive : 0<tail.length := by
    have lengths := congrArg List.length tailPaths
    rw [ordinary.paths_length,List.length_append] at lengths
    simp only [List.length_singleton] at lengths
    omega
  let tailRun : ExtractionRun middle.erase := .of tail ordinary
  have tailCanonical : CanonicalRun tailRun := by
    refine ⟨positive,?_,?_⟩
    · exact canonical.2.1.suffix (ρ := .single (singleContraction head.betaAt)) (σ := tail)
    · exact ExtractionNormal.of_prepend (r := tailRun)
        (pre := .single (singleContraction head.betaAt)) (ha := .single head.betaAt) canonical.2.2
  exact ⟨tailRun,tailCanonical,tailPaths⟩

private theorem canonical_cast_source (equal : source=target) (run : ExtractionRun source) :
    CanonicalRun (run.castSource equal) ↔ CanonicalRun run := by cases equal; rfl

private def CanonicalDegreeUniqueAt (n : Nat) : Prop :=
  ∀ {t u v u' v' : LTerm} {ps qs : List Path} {q r : Path} {l : Label},
    History ps t u → StepAt q u v → History qs t u' → StepAt r u' v' → INIT t →
    (run other : ExtractionRun t.erase) → CanonicalRun run → CanonicalRun other →
    run.history.derivation.paths=ps++[q] → other.history.derivation.paths=qs++[r] →
    u.degreeAt q=some l → u'.degreeAt r=some l → ps.length=n → ps++[q]=qs++[r]

private theorem canonical_degree_unique_all : ∀ n,CanonicalDegreeUniqueAt n := by
  classical
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro t u v u' v' ps qs q r l left last right last' initial run other canonical canonical' paths paths' degree degree' count
    cases left with
    | nil t =>
      obtain ⟨body,lookup⟩ := LTerm.degreeAt_lambda degree
      have atomic := initial.1 l (LTerm.label_mem_of_subterm lookup)
      have empty := canonical_atomic_prefix_empty right last' other canonical' paths' degree' atomic
      subst qs
      cases right with
      | nil =>
        have equal := LTerm.initial_degree_injective initial degree degree'
        cases equal
        rfl
    | @cons headSite source middle restPaths current head rest =>
      cases right with
      | nil =>
        obtain ⟨body,lookup⟩ := LTerm.degreeAt_lambda degree'
        have atomic := initial.1 l (LTerm.label_mem_of_subterm lookup)
        have impossible := canonical_atomic_prefix_empty (History.cons head rest) last run canonical paths degree atomic
        cases impossible
      | @cons otherSite source otherMiddle otherPaths otherCurrent otherHead otherRest =>
        have first := History.canonical_first_leftmost head rest last initial run canonical paths degree
        have second := History.canonical_first_leftmost otherHead otherRest last' initial other canonical' paths' degree'
        have sameHead := degree_candidate_unique _ l _ _ first second
        have sameSite := congrArg Subtype.val sameHead
        change headSite=otherSite at sameSite
        cases sameSite
        have sameMiddle := head.deterministic otherHead
        cases sameMiddle
        obtain ⟨basisCurrent,basisRest,erasedCurrent,_⟩ := rest.local_initial_basis
        obtain ⟨basisTarget,basisLast,_⟩ := lift_betaAt (t := basisCurrent) (by rw [erasedCurrent]; exact last.betaAt)
        obtain ⟨localLeft,leftDegree⟩ := degreeAt_exists basisCurrent ⟨q,basisLast.betaAt.redex⟩
        obtain ⟨basisOther,basisOtherRest,erasedOther,_⟩ := otherRest.local_initial_basis
        obtain ⟨basisOtherTarget,basisOtherLast,_⟩ := lift_betaAt (t := basisOther) (by rw [erasedOther]; exact last'.betaAt)
        obtain ⟨localRight,rightDegree⟩ := degreeAt_exists basisOther ⟨r,basisOtherLast.betaAt.redex⟩
        have sameLocal := head.canonical_same_degree_local_reflection initial rest basisRest last otherRest basisOtherRest
          run canonical paths degree leftDegree degree' rightDegree
        obtain ⟨tailRun,tailCanonical,tailPaths⟩ := canonical_tail head rest last run canonical paths
        obtain ⟨otherTailRun,otherTailCanonical,otherTailPaths⟩ := canonical_tail otherHead otherRest last' other canonical' paths'
        let basisRun := tailRun.castSource (erase_initLabels middle.erase).symm
        let otherBasisRun := otherTailRun.castSource (erase_initLabels middle.erase).symm
        have basisCanonical : CanonicalRun basisRun := by
          exact (canonical_cast_source (erase_initLabels middle.erase).symm tailRun).mpr tailCanonical
        have otherBasisCanonical : CanonicalRun otherBasisRun := by
          exact (canonical_cast_source (erase_initLabels middle.erase).symm otherTailRun).mpr otherTailCanonical
        have basisPaths : basisRun.history.derivation.paths=restPaths++[q] := by
          rw [ExtractionRun.castSource_paths]
          exact tailPaths
        have otherBasisPaths : otherBasisRun.history.derivation.paths=otherPaths++[r] := by
          rw [ExtractionRun.castSource_paths]
          exact otherTailPaths
        have shorter : restPaths.length<n := by simp only [List.length_cons] at count; omega
        have tailEqual := ih restPaths.length shorter basisRest basisLast basisOtherRest basisOtherLast (init_is_INIT middle.erase)
          basisRun otherBasisRun basisCanonical otherBasisCanonical basisPaths otherBasisPaths leftDegree (sameLocal.symm ▸ rightDegree) rfl
        exact congrArg (headSite::·) tailEqual

/-- Equal degrees in the same original INIT labelling determine the entire
canonical pointed schedule, including both proper prefix and final event. -/
theorem History.canonical_degree_paths_unique
    (left : History ps t u) (last : StepAt q u v) (right : History qs t u') (last' : StepAt r u' v')
    (initial : INIT t) (run other : ExtractionRun t.erase)
    (canonical : CanonicalRun run) (canonical' : CanonicalRun other)
    (paths : run.history.derivation.paths=ps++[q]) (paths' : other.history.derivation.paths=qs++[r])
    (degree : u.degreeAt q=some l) (degree' : u'.degreeAt r=some l) : ps++[q]=qs++[r] :=
  canonical_degree_unique_all ps.length left last right last' initial run other canonical canonical' paths paths' degree degree' rfl

/-- Thus equal transported degrees determine the actual canonical runs,
not merely equal final terms or an equivalent history. -/
theorem History.canonical_degree_runs_unique
    (left : History ps t u) (last : StepAt q u v) (right : History qs t u') (last' : StepAt r u' v')
    (initial : INIT t) (run other : ExtractionRun t.erase)
    (canonical : CanonicalRun run) (canonical' : CanonicalRun other)
    (paths : run.history.derivation.paths=ps++[q]) (paths' : other.history.derivation.paths=qs++[r])
    (degree : u.degreeAt q=some l) (degree' : u'.degreeAt r=some l) : run=other := by
  apply ExtractionRun.ext_paths
  exact paths.trans ((left.canonical_degree_paths_unique last right last' initial run other canonical canonical'
    paths paths' degree degree').trans paths'.symm)

end Lamping.Lambda.Labelled



