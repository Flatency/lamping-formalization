import Lamping.Lambda.PrerequisitePrefixes
import Lamping.Lambda.PrerequisiteOrder
import Lamping.Lambda.ClosedVariableBinders
namespace Lamping.Lambda.Labelled

def NoPrerequisite (current : LTerm) (position : Path) : Prop :=
  ¬∃ edges,PrerequisiteChain current position edges

theorem PrerequisitePrefix.no_prerequisite (segment : PrerequisitePrefix current start edges finish)
    (undefined : NoPrerequisite current start) : NoPrerequisite current finish := by
  rintro ⟨tail,chain⟩
  exact undefined ⟨edges++tail,segment.close chain⟩

theorem no_prerequisite_root_lambda (lookup : current.subterm []=some (.lam stamp body)) :
    NoPrerequisite current [] := by
  rintro ⟨edges,chain⟩
  rcases chain.lambda_cases lookup with ⟨parent,a,arg,split,_,_⟩|⟨parent,step,tail,split,_,_,_⟩
  · have lengths := congrArg List.length split
    simp at lengths
  · have lengths := congrArg List.length split
    simp at lengths

/-- Undefined is witnessed by the actual finite dependency segment to the
root lambda, not by a successful empty chain or path completion. -/
theorem no_prerequisite_root_prefix {current sub : LTerm}
    (closed : Closed current.erase) (lookup : current.subterm position=some sub)
    (undefined : NoPrerequisite current position) :
    ∃ stamp body edges,current.subterm []=some (.lam stamp body) ∧
      PrerequisitePrefix current position edges [] := by
  have main : ∀ n position sub,prerequisiteOrder current position=n →
      current.subterm position=some sub →NoPrerequisite current position →
      ∃ stamp body edges,current.subterm []=some (.lam stamp body) ∧
        PrerequisitePrefix current position edges [] := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
      intro p sub order atSite noChain
      cases sub with
      | app stamp fn arg =>
        have notLambda : ∀ l b,fn≠.lam l b := by
          intro l b same; subst fn
          exact noChain ⟨[p++[.fn]],.redex_app atSite⟩
        have atFn : current.subterm (p++[.fn])=some fn := by
          rw [LTerm.subterm_append,atSite]; cases fn <;> rfl
        have dep := PrerequisiteDependency.app atSite notLambda
        have segment : PrerequisitePrefix current p [p++[.fn]] (p++[.fn]) :=
          .app atSite notLambda .refl
        obtain ⟨rootStamp,rootBody,edges,rootAt,tail⟩ := ih _ (by rw [←order]; exact dep.order_lt)
          (p++[.fn]) fn rfl atFn (segment.no_prerequisite noChain)
        exact ⟨rootStamp,rootBody,_,rootAt,.app atSite notLambda tail⟩
      | var stamp index =>
        obtain ⟨parent,rest,origin,body,split,binder,_leaf,_bare,depth⟩ :=
          current.closed_variable_binder closed atSite
        have dep := PrerequisiteDependency.var atSite binder split depth
        have segment : PrerequisitePrefix current p [] parent := .var atSite binder split depth .refl
        obtain ⟨rootStamp,rootBody,edges,rootAt,tail⟩ := ih _ (by rw [←order]; exact dep.order_lt)
          parent (.lam origin body) rfl binder (segment.no_prerequisite noChain)
        exact ⟨rootStamp,rootBody,edges,rootAt,.var atSite binder split depth tail⟩
      | lam stamp body =>
        obtain ⟨env,ctx,occurrence⟩ := SourceSubterm.of_lookup current atSite [] .external
        rcases occurrence.last_departure with ⟨rootEq,_⟩|⟨parent,step,term,split,parentAt,role⟩
        · subst p
          exact ⟨stamp,body,[],atSite,.refl⟩
        · have notFunction : step≠.fn := by
            intro same; subst step
            cases role
            have child := atSite
            rw [split,LTerm.subterm_append,parentAt] at child
            simp only [Option.bind_some,LTerm.subterm] at child
            have fnEq := Option.some.inj child
            cases fnEq
            exact noChain ⟨[parent++[.fn]],by simpa only [split] using PrerequisiteChain.redex_lam parentAt⟩
          have atChild : current.subterm (parent++[step])=some (.lam stamp body) := by rw [←split]; exact atSite
          have dep := PrerequisiteDependency.lam parentAt atChild notFunction
          have segment : PrerequisitePrefix current p [p] parent := by
            simpa only [split] using PrerequisitePrefix.lam atChild notFunction PrerequisitePrefix.refl
          obtain ⟨rootStamp,rootBody,edges,rootAt,tail⟩ := ih _ (by rw [←order,split]; exact dep.order_lt)
            parent term rfl parentAt (segment.no_prerequisite noChain)
          refine ⟨rootStamp,rootBody,p::edges,rootAt,?_⟩
          simpa only [split] using PrerequisitePrefix.lam atChild notFunction tail
  exact main _ position sub rfl lookup undefined
/-- A variable's undefined status is exactly its actual lexical binder's.
The binder is identified by its literal path and index, not by its label. -/
theorem no_prerequisite_variable_iff
    (lookup : current.subterm leaf=some (.var stamp index))
    (binder : current.subterm parent=some (.lam origin body))
    (split : leaf=parent++(.body::rest)) (depth : index=binderDepth rest) :
    NoPrerequisite current leaf ↔NoPrerequisite current parent := by
  constructor
  · intro noLeaf
    exact (PrerequisitePrefix.var lookup binder split depth .refl).no_prerequisite noLeaf
  · intro noParent ⟨edges,chain⟩
    obtain ⟨other,tail,otherStamp,otherBody,otherSplit,otherDepth,_otherLookup,otherChain⟩ := chain.variable_cases lookup
    have same := binding_prefix_depth_unique (split.symm.trans otherSplit) (depth.symm.trans otherDepth)
    rw [←same.1] at otherChain
    exact noParent ⟨edges,otherChain⟩

theorem no_prerequisite_application_iff
    (lookup : current.subterm p=some (.app stamp fn arg)) :
    NoPrerequisite current p ↔
      (∀ label body,fn≠.lam label body) ∧NoPrerequisite current (p++[.fn]) := by
  constructor
  · intro noApp
    have notLambda : ∀ label body,fn≠.lam label body := by
      intro label body same; subst fn
      exact noApp ⟨_,.redex_app lookup⟩
    exact ⟨notLambda,(PrerequisitePrefix.app lookup notLambda .refl).no_prerequisite noApp⟩
  · rintro ⟨notLambda,noFn⟩ ⟨edges,chain⟩
    rcases chain.app_cases lookup with ⟨label,body,same,_⟩|⟨_,tail,_same,child⟩
    · exact notLambda label body same
    · exact noFn ⟨tail,child⟩
end Lamping.Lambda.Labelled