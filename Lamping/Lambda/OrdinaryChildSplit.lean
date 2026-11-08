import Lamping.Lambda.ArgumentHeadPreservation
import Lamping.Lambda.UsedSourceContexts
namespace Lamping.Lambda
/-- Find the first actual function-child contraction in a root-preserving
ordinary application history, retaining the entire preceding argument prefix. -/
theorem Atomic.app_first_fn {ρ : ParallelHistory t u} (ordinary : Atomic ρ)
    (shape : t=.app f a) (noRoot : ∀ p∈ρ.derivation.paths, p≠[]) :
    Internal [.arg] ρ ∨
    ∃ (a' f' : Term) (q : Path) (sourcePre : ParallelHistory t (.app f a'))
      (head : BetaAt (.app f a') (.fn::q) (.app f' a')) (tail : ParallelHistory (.app f' a') u),
      ρ=sourcePre.append (.cons (singleContraction head) tail) ∧ Internal [.arg] sourcePre := by
  induction ordinary generalizing f a with
  | nil t => exact Or.inl (by intro p hp; cases hp)
  | @cons t p mid u tail head tailAtomic ih =>
    have nonempty : p≠[] := noRoot p (by
      simp [ParallelHistory.derivation,Derivation.append,ParallelStep.derivation,singleContraction])
    have tailNoRoot : ∀ p∈tail.derivation.paths,p≠[] := by
      intro p hp
      exact noRoot p (by simp [ParallelHistory.derivation,Derivation.append,hp])
    subst t
    cases p with
    | nil => exact False.elim (nonempty rfl)
    | cons e p =>
      cases e with
      | body =>
        obtain ⟨redex,lookup,_⟩ := head.redex
        simp [subtermAt] at lookup
      | fn =>
        obtain ⟨f',_,midEq⟩ := (SyntaxFrame.fn a).beta_reflect head
        change mid=.app f' a at midEq
        subst mid
        exact Or.inr ⟨a,f',p,.nil _,head,tail,rfl,by intro p hp; cases hp⟩
      | arg =>
        obtain ⟨a',_,midEq⟩ := (SyntaxFrame.arg f).beta_reflect head
        change mid=.app f a' at midEq
        subst mid
        rcases ih rfl tailNoRoot with allRight | ⟨a'',f',q,sourcePre,next,rest,tailEq,inside⟩
        · refine Or.inl ?_
          intro q hq
          change q∈(.arg::p)::tail.derivation.paths at hq
          rcases List.mem_cons.mp hq with same | later
          · exact ⟨p,same⟩
          · exact allRight q later
        · refine Or.inr ⟨a'',f',q,.cons (singleContraction head) sourcePre,next,rest,?_,?_⟩
          · rw [tailEq]; rfl
          · intro q hq
            change q∈(.arg::p)::sourcePre.derivation.paths at hq
            rcases List.mem_cons.mp hq with same | later
            · exact ⟨p,same⟩
            · exact inside q later
end Lamping.Lambda
