import Lamping.Lambda.LabelRegions
namespace Lamping.Lambda.Labelled
theorem SourceSubterm.env_length
    (site : SourceSubterm outerEnv outerCtx original p env ctx sub) :
    env.length=outerEnv.length+binderDepth p := by
  induction site with
  | nil => rfl
  | fn _ ih => exact ih
  | arg _ ih => exact ih
  | body _ ih => simp only [List.length_cons,binderDepth] at *; omega

/-- An actual environment entry is either a lambda on the literal descent
inside this source term, or an entry of the supplied outside environment. -/
theorem SourceSubterm.binder_origin
    (atSite : SourceSubterm outerEnv outerCtx original p env ctx sub)
    (entry : env[index]?=some origin) :
    (∃ parent tail body,p=parent++(.body::tail) ∧
      original.subterm parent=some (.lam origin body) ∧ index=binderDepth tail) ∨
    (∃ j,index=j+binderDepth p ∧ outerEnv[j]?=some origin) := by
  induction atSite generalizing index origin with
  | nil => exact Or.inr ⟨index,rfl,entry⟩
  | fn _ ih =>
    rcases ih entry with ⟨parent,tail,body,split,atParent,depth⟩ | ⟨j,depth,atOuter⟩
    · exact Or.inl ⟨.fn::parent,tail,body,congrArg (Step.fn::·) split,atParent,depth⟩
    · exact Or.inr ⟨j,depth,atOuter⟩
  | arg _ ih =>
    rcases ih entry with ⟨parent,tail,body,split,atParent,depth⟩ | ⟨j,depth,atOuter⟩
    · exact Or.inl ⟨.arg::parent,tail,body,congrArg (Step.arg::·) split,atParent,depth⟩
    · exact Or.inr ⟨j,depth,atOuter⟩
  | @body label outside body path innerEnv innerCtx child port desc ih =>
    rcases ih entry with ⟨parent,tail,ancestor,split,atParent,depth⟩ | ⟨j,depth,atOuter⟩
    · exact Or.inl ⟨.body::parent,tail,ancestor,congrArg (Step.body::·) split,atParent,depth⟩
    · cases j with
      | zero =>
        have same : label=origin := Option.some.inj atOuter
        subst origin
        exact Or.inl ⟨[],path,body,rfl,rfl,by simpa only [Nat.zero_add] using depth⟩
      | succ j =>
        exact Or.inr ⟨j,by simp only [binderDepth] at *; omega,atOuter⟩
/-- At the whole source's empty binder environment, an actual entry must
come from a real lambda occurrence on this very syntax path. No INIT needed. -/
theorem SourceSubterm.bound_binder_occurrence
    (atSite : SourceSubterm [] outerCtx original p env ctx sub)
    (entry : env[index]?=some origin) :
    ∃ parent tail body,p=parent++(.body::tail) ∧
      original.subterm parent=some (.lam origin body) ∧ index=binderDepth tail := by
  rcases atSite.binder_origin entry with inside | ⟨j,_,impossible⟩
  · exact inside
  · simp at impossible
/-- The port identity used by SourceRoute variables identifies the same
actual lexical lambda occurrence, rather than just another equal label. -/
theorem SourceSubterm.sourceBinder_occurrence
    (atSite : SourceSubterm [] outerCtx original p env ctx sub)
    (bound : sourceBinder env index=.lamBind origin) :
    ∃ parent tail body,p=parent++(.body::tail) ∧
      original.subterm parent=some (.lam origin body) ∧ index=binderDepth tail := by
  apply atSite.bound_binder_occurrence
  unfold sourceBinder at bound
  cases entry : env[index]? with
  | none => rw [entry] at bound; cases bound
  | some actual =>
    rw [entry] at bound
    have same : actual=origin := SourcePort.lamBind.inj bound
    exact congrArg some same
end Lamping.Lambda.Labelled

namespace Lamping.Lambda
/-- A variable index picks one literal lambda-body prefix of a path. Even
repeated labels or identical node kinds cannot change that occurrence. -/
theorem binding_prefix_depth_unique {parent tail other rest : Path}
    (samePath : parent++(.body::tail)=other++(.body::rest))
    (sameDepth : binderDepth tail=binderDepth rest) : parent=other ∧ tail=rest := by
  induction parent generalizing other with
  | nil =>
    cases other with
    | nil => exact ⟨rfl,List.cons.inj samePath |>.2⟩
    | cons first suffix =>
      have heads := (List.cons.inj samePath).1
      have tails := (List.cons.inj samePath).2
      subst first
      have counts : binderDepth tail=binderDepth suffix+(binderDepth rest+1) :=
        (congrArg binderDepth tails).trans (binderDepth_append suffix (.body::rest))
      omega
  | cons first ancestorRest ih =>
    cases other with
    | nil =>
      have heads := (List.cons.inj samePath).1
      have tails := (List.cons.inj samePath).2
      subst first
      have counts : binderDepth ancestorRest+(binderDepth tail+1)=binderDepth rest :=
        (binderDepth_append ancestorRest (.body::tail)).symm.trans (congrArg binderDepth tails)
      omega
    | cons next suffix =>
      have heads := (List.cons.inj samePath).1
      have tails := (List.cons.inj samePath).2
      subst next
      have unique := ih tails
      exact ⟨congrArg (first::·) unique.1,unique.2⟩
end Lamping.Lambda




namespace Lamping.Lambda.Labelled
/-- The real old syntax parent fixes the original departure port. -/
inductive SourceDeparture : LTerm → Step → SourcePort → Prop where
  | fn : SourceDeparture (.app label fn arg) .fn (.appFn label)
  | arg : SourceDeparture (.app label fn arg) .arg (.appArg label)
  | body : SourceDeparture (.lam label body) .body (.lamBody label)

theorem SourceSubterm.last_departure
    (site : SourceSubterm outerEnv outerCtx original p env ctx sub) :
    (p=[] ∧ ctx=outerCtx) ∨ ∃ parent step term,p=parent++[step] ∧
      original.subterm parent=some term ∧ SourceDeparture term step ctx := by
  induction site with
  | nil => exact .inl ⟨rfl,rfl⟩
  | fn _ ih =>
    rcases ih with ⟨rfl,rfl⟩ | ⟨parent,step,term,split,lookup,role⟩
    · exact .inr ⟨[],.fn,_,rfl,rfl,.fn⟩
    · exact .inr ⟨.fn::parent,step,term,congrArg (Step.fn::·) split,lookup,role⟩
  | arg _ ih =>
    rcases ih with ⟨rfl,rfl⟩ | ⟨parent,step,term,split,lookup,role⟩
    · exact .inr ⟨[],.arg,_,rfl,rfl,.arg⟩
    · exact .inr ⟨.arg::parent,step,term,congrArg (Step.arg::·) split,lookup,role⟩
  | body _ ih =>
    rcases ih with ⟨rfl,rfl⟩ | ⟨parent,step,term,split,lookup,role⟩
    · exact .inr ⟨[],.body,_,rfl,rfl,.body⟩
    · exact .inr ⟨.body::parent,step,term,congrArg (Step.body::·) split,lookup,role⟩

end Lamping.Lambda.Labelled
