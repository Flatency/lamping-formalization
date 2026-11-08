import Lamping.Lambda.OrdinaryChildSplit
import Lamping.Lambda.ArgumentCommutation
import Lamping.Lambda.StandardizationNoReturn
namespace Lamping.Lambda
private theorem head_no_return (head : BetaAt t p u) (tail : ParallelHistory u v)
    (standard : Standard (.cons (singleContraction head) tail)) :
    DoesNotReturnLeft ⟨p,head.redex⟩ (.cons (singleContraction head) tail) := by
  cases standard with
  | cons _ witness lo noReturn rest =>
    have same : witness=⟨p,head.redex⟩ := Subtype.ext (List.mem_singleton.mp lo.1)
    subst witness
    exact noReturn

/-- Once a standard root-preserving application history starts in its
argument, its function remains untouched. A first later function contraction
would be a genuine forbidden use of an earlier initial redex. -/
theorem Atomic.app_arg_stays {tail : ParallelHistory t u} (tailAtomic : Atomic tail)
    (head : BetaAt (.app f a) (.arg::p) t)
    (noRoot : ∀ q∈(ParallelHistory.cons (singleContraction head) tail).derivation.paths,q≠[])
    (standard : Standard (.cons (singleContraction head) tail)) :
    Internal [.arg] (.cons (singleContraction head) tail) := by
  rcases (Atomic.cons head tailAtomic).app_first_fn rfl noRoot with right | ⟨a',f',q,sourcePre,next,suffix,eq,inside⟩
  · exact right
  · have apart : ∀ pos∈sourcePre.derivation.paths, DisjointPositions (.fn::q) pos := by
      intro pos hp
      obtain ⟨r,atArg⟩ := inside pos hp
      rw [atArg]
      exact DisjointPositions.head_ne (by intro eq; cases eq)
    have fixed := sourcePre.derivation.valid.subterm_fixed_apart apart
    have oldValid := next.redex
    rw [fixed] at oldValid
    let initial : RedexOcc (.app f a) := ⟨.fn::q,oldValid⟩
    let selected : RedexOcc (.app f a') := ⟨.fn::q,next.redex⟩
    have paths : ∀ pos∈sourcePre.derivation.paths, LeftOf initial.val pos := by
      intro pos hp
      obtain ⟨r,atArg⟩ := inside pos hp
      rw [atArg]
      exact .branch q r
    have residual := (sourcePre.derivation.left_fixed initial paths selected).mpr rfl
    have used : UsedSource (.cons (singleContraction head) tail) initial :=
      ⟨.app f a',.app f' a',[_],sourcePre,singleContraction next,suffix,selected,eq,by simp [selected],residual⟩
    exact False.elim ((head_no_return head tail standard).no_used_left (.cons head tailAtomic) initial (.branch q p) used)

/-- A standard ordinary history preserving the application root has a literal
function phase followed by an argument phase, extracted from its actual steps. -/
theorem Atomic.standard_app_blocks {ρ : ParallelHistory t u} (ordinary : Atomic ρ)
    (shape : t=.app f a) (noRoot : ∀ p∈ρ.derivation.paths,p≠[]) (standard : Standard ρ) :
    ∃ (mid : Term) (fnPart : ParallelHistory t mid) (argPart : ParallelHistory mid u),
      Atomic fnPart ∧ Atomic argPart ∧ ρ=fnPart.append argPart ∧
      Internal [.fn] fnPart ∧ Internal [.arg] argPart := by
  induction ordinary generalizing f a with
  | nil t =>
    refine ⟨t,.nil t,.nil t,.nil t,.nil t,rfl,?_,?_⟩
    all_goals intro p hp; cases hp
  | @cons t p mid u tail head tailAtomic ih =>
    have nonempty : p≠[] := noRoot p (by
      simp [ParallelHistory.derivation,Derivation.append,ParallelStep.derivation,singleContraction])
    have tailNoRoot : ∀ p∈tail.derivation.paths,p≠[] := by
      intro p hp; exact noRoot p (by simp [ParallelHistory.derivation,Derivation.append,hp])
    have tailStandard : Standard tail := standard.suffix (ρ:=.single (singleContraction head)) (σ:=tail)
    subst t
    cases p with
    | nil => exact False.elim (nonempty rfl)
    | cons e p =>
      cases e with
      | body => obtain ⟨redex,lookup,_⟩ := head.redex; simp [subtermAt] at lookup
      | arg =>
        refine ⟨.app f a,.nil _,.cons (singleContraction head) tail,.nil _,.cons head tailAtomic,rfl,?_,
          tailAtomic.app_arg_stays head noRoot standard⟩
        intro p hp; cases hp
      | fn =>
        obtain ⟨f',_,midEq⟩ := (SyntaxFrame.fn a).beta_reflect head
        change mid=.app f' a at midEq
        subst mid
        obtain ⟨last,fnPart,argPart,fnAtomic,argAtomic,eq,fnInside,argInside⟩ := ih rfl tailNoRoot tailStandard
        refine ⟨last,.cons (singleContraction head) fnPart,argPart,.cons head fnAtomic,argAtomic,?_,?_,argInside⟩
        · rw [eq]; rfl
        · intro q hq
          change q∈(.fn::p)::fnPart.derivation.paths at hq
          rcases List.mem_cons.mp hq with same | later
          · exact ⟨p,same⟩
          · exact fnInside q later
end Lamping.Lambda
