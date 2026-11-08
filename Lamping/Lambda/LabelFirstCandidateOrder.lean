import Lamping.Lambda.LabelDegreeAtoms
import Lamping.Lambda.LabelFirstRedex
import Lamping.Lambda.StandardizationNoReturn
import Lamping.Lambda.AtomicHistories
namespace Lamping.Lambda.Labelled

/-- Recover the actual labelled application, not just its function label. -/
theorem LTerm.degreeAt_redex {t : LTerm} (degree : t.degreeAt p=some alpha) :
    ∃ beta body argument,t.subterm p=some (.app beta (.lam alpha body) argument) := by
  obtain ⟨sub,lookup,value⟩ := Option.bind_eq_some_iff.mp degree
  cases sub with
  | var => simp [LTerm.degree] at value
  | lam => simp [LTerm.degree] at value
  | app beta fn arg =>
    cases fn with
    | var => simp [LTerm.degree] at value
    | app => simp [LTerm.degree] at value
    | lam l b =>
      have equal : l=alpha := Option.some.inj value
      cases equal
      exact ⟨beta,b,arg,lookup⟩

/-- An actual atomic event supplies the frozen source-use relation for the
same ordinary program. Exact path equality fixes the whole program. -/
theorem FiresAtom.used_source (fired : FiresAtom ps t u n) (initial : INIT t)
    (r : RedexOcc t.erase) (degree : t.degreeAt r.val=some (Label.atom n))
    (program : ParallelHistory t.erase u.erase) (ordinary : Atomic program)
    (paths : program.derivation.paths=ps) : UsedSource program r := by
  obtain ⟨before,site,after,v,w,schedule,pre,event,post,residual⟩ :=
    fired.initial_residual initial r degree
  obtain ⟨preProgram,preAtomic,prePaths⟩ := pre.betaHistory.atomic
  obtain ⟨postProgram,postAtomic,postPaths⟩ := post.betaHistory.atomic
  have equal : program=preProgram.append (.cons (singleContraction event.betaAt) postProgram) := by
    apply ordinary.paths_injective (preAtomic.append (.cons event.betaAt postAtomic))
    simpa only [ParallelHistory.derivation_append,Derivation.append,
      ParallelHistory.derivation, singleContraction_paths,prePaths,postPaths] using paths.trans schedule
  have preEq : preProgram.derivation=(⟨before,pre.betaHistory⟩ : Derivation t.erase v.erase) :=
    Lamping.Lambda.Derivation.ext prePaths
  exact ⟨v.erase,w.erase,[site],preProgram,singleContraction event.betaAt,postProgram,
    ⟨site,event.betaAt.redex⟩,equal,List.mem_singleton_self _,by simpa only [preEq] using residual⟩
/-- Every initial degree candidate is genuinely used somewhere in the full
pointed run, even when its proper prefix contains unrelated contractions. -/
theorem History.degree_candidate_used (history : History ps t u) (last : StepAt q u v)
    (initial : INIT t) (degree : u.degreeAt q=some l)
    (r : RedexOcc t.erase) (candidate : r.val∈degreeCandidates t l)
    (program : ParallelHistory t.erase v.erase) (ordinary : Atomic program)
    (paths : program.derivation.paths=ps++[q]) : UsedSource program r := by
  obtain ⟨_,n,initialDegree,e,member,equal⟩ := (mem_degreeCandidates t l r.val).mp candidate
  obtain ⟨beta,body,argument,lookup⟩ := LTerm.degreeAt_redex initialDegree
  obtain ⟨env,ctx,atHead⟩ := SourceSubterm.of_lookup t lookup [] .external
  have occurs : ¬l.Supported (fun m => m≠n) := by
    intro support
    have different := (Label.supported_iff_within _ l).mp support e member
    exact different equal
  have fired := history.pointed_fires_initial_atom last initial atHead degree occurs
  exact fired.used_source initial r initialDegree program ordinary paths

private theorem standard_head_no_return (first : BetaAt a p b) (tail : ParallelHistory b c)
    (standard : Standard (.cons (singleContraction first) tail)) :
    DoesNotReturnLeft ⟨p,first.redex⟩ (.cons (singleContraction first) tail) := by
  cases standard with
  | cons _ witness lo noReturn rest =>
    have same : witness=⟨p,first.redex⟩ := Subtype.ext (List.mem_singleton.mp lo.1)
    subst witness
    exact noReturn

/-- Real standardness forbids every final-degree candidate strictly before
the actual head contraction. This is one direction of First Redex ordering. -/
theorem History.candidate_not_left_of_head (history : History ps t u) (last : StepAt q u v)
    (initial : INIT t) (degree : u.degreeAt q=some l)
    (first : BetaAt t.erase head mid) (tail : ParallelHistory mid v.erase)
    (ordinary : Atomic tail)
    (paths : (ParallelHistory.cons (singleContraction first) tail).derivation.paths=ps++[q])
    (standard : Standard (.cons (singleContraction first) tail))
    (r : RedexOcc t.erase) (candidate : r.val∈degreeCandidates t l) : ¬LeftOf r.val head := by
  have used := history.degree_candidate_used last initial degree r candidate
    (.cons (singleContraction first) tail) (.cons first ordinary) paths
  intro before
  exact (standard_head_no_return first tail standard).no_used_left (.cons first ordinary) r before used

/-- The computed LO degree candidate is at or later than the actual first
contraction in a standard pointed run. Membership of that head remains a
separate canonical-support obligation. -/
theorem History.head_le_degree_candidate (history : History ps t u) (last : StepAt q u v)
    (initial : INIT t) (degree : u.degreeAt q=some l)
    (first : BetaAt t.erase head mid) (tail : ParallelHistory mid v.erase)
    (ordinary : Atomic tail)
    (paths : (ParallelHistory.cons (singleContraction first) tail).derivation.paths=ps++[q])
    (standard : Standard (.cons (singleContraction first) tail))
    (r : RedexOcc t.erase) (candidate : LeftmostSelected (degreeCandidates t l) r) :
    head=r.val ∨ LeftOf head r.val := by
  let actualHead : RedexOcc t.erase := ⟨head,first.redex⟩
  rcases actualHead.compare r with same | before | after
  · exact .inl (congrArg Subtype.val same)
  · exact .inr before
  · exact False.elim (history.candidate_not_left_of_head last initial degree first tail ordinary paths standard r candidate.1 after)
end Lamping.Lambda.Labelled
