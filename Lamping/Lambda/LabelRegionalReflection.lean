import Lamping.Lambda.LabelInternalRegions
namespace Lamping.Lambda.Labelled

/-- Labelled beta is stable under actual capture-avoiding substitution at
its original site, with the exact substituted target. -/
theorem StepAt.subst (step : StepAt p t u) (sigma) : StepAt p (t.subst sigma) (u.subst sigma) := by
  induction step generalizing sigma with
  | root beta alpha body argument =>
    rw [LTerm.subst_contract]
    exact .root _ _ _ _
  | fn _ ih => exact .fn (ih sigma)
  | arg _ ih => exact .arg (ih sigma)
  | body _ ih => exact .body (ih (LTerm.lift sigma))

/-- The old root prefix is transported through the same real contraction. -/
theorem StepAt.prepend (step : StepAt p t u) (word) : StepAt p (t.prepend word) (u.prepend word) := by
  cases step with
  | root beta alpha body argument =>
    rw [←LTerm.contract_prepend_beta]
    exact .root _ _ _ _
  | fn step => exact .fn step
  | arg step => exact .arg step
  | body step => exact .body step

namespace LTerm
/-- Every redex degree is a node label, so an outside-only term has no
regional degree, at any actual redex position. -/
theorem OutsideRegion.degree_outside (outside : OutsideRegion region t)
    (degree : t.degreeAt p=some l) : ¬l.Supported region := by
  obtain ⟨body,lookup⟩ := degreeAt_lambda degree
  exact outside l (label_mem_of_subterm lookup)

theorem degree_root_function_label {fn argument : LTerm}
    (degree : (LTerm.app beta fn argument).degreeAt []=some l) : fn.label=l := by
  cases fn <;> simp_all [degreeAt,subterm,LTerm.degree,LTerm.label]

/-- Regional substituted redexes are actual old body redexes. Put arguments
outside the region cannot create such a redex at a former variable boundary. -/
theorem degreeAt_subst_reflect (t : LTerm)
    (values : ∀ i value,sigma i=.put value → OutsideRegion region value)
    (degree : (t.subst sigma).degreeAt p=some l) (support : l.Supported region) :
    t.degreeAt p=some l := by
  induction t generalizing sigma p with
  | var label i =>
    cases he : sigma i with
    | keep j =>
      cases p with
      | nil => simp [subst,he,degreeAt,subterm,LTerm.degree] at degree
      | cons step rest => cases step <;> simp [subst,he,degreeAt,subterm] at degree
    | put argument =>
      have outside := (values i argument he).prepend label
      exact False.elim (outside.degree_outside (by simpa only [subst,he] using degree) support)
  | lam label body ih =>
    cases p with
    | nil => simp [subst,degreeAt,subterm,LTerm.degree] at degree
    | cons step rest =>
      cases step with
      | fn => simp [subst,degreeAt,subterm] at degree
      | arg => simp [subst,degreeAt,subterm] at degree
      | body => exact ih (lift_outside_values values) degree
  | app label fn argument hf ha =>
    cases p with
    | nil =>
      cases fn with
      | lam alpha body =>
        simpa only [subst,degreeAt,subterm,Option.bind_some,LTerm.degree] using degree
      | app a f b => simp [subst,degreeAt,subterm,LTerm.degree] at degree
      | var name i =>
        cases he : sigma i with
        | keep j => simp [subst,he,degreeAt,subterm,LTerm.degree] at degree
        | put a =>
          have equal := degree_root_function_label (fn := a.prepend name) (argument := argument.subst sigma)
            (beta := label) (l := l) (by simpa only [subst,he] using degree)
          have outside := (values i a he).prepend name
          exact False.elim (outside (a.prepend name).label (label_mem_labels _) (equal.symm ▸ support))
    | cons step rest =>
      cases step with
      | body => simp [subst,degreeAt,subterm] at degree
      | fn => exact hf values degree
      | arg => exact ha values degree
end LTerm
/-- A regional contraction of a substituted body is exactly the substitution
of a real original-body contraction at that same site. -/
theorem StepAt.subst_reflect (step : StepAt p (t.subst sigma) u)
    (values : ∀ i value,sigma i=.put value → LTerm.OutsideRegion region value)
    (degree : (t.subst sigma).degreeAt p=some l) (support : l.Supported region) :
    ∃ oldTarget,StepAt p t oldTarget ∧ u=oldTarget.subst sigma := by
  have oldDegree := LTerm.degreeAt_subst_reflect t values degree support
  obtain ⟨beta,body,argument,lookup⟩ := LTerm.degreeAt_redex oldDegree
  let occurrence : RedexOcc t.erase := ⟨p,by
    refine ⟨.app (.lam body.erase) argument.erase,?_,True.intro⟩
    rw [←LTerm.erase_subterm,lookup]
    rfl⟩
  obtain ⟨target,contraction⟩ := occurrence.contract_exists
  obtain ⟨oldTarget,oldStep,_⟩ := lift_betaAt contraction
  exact ⟨oldTarget,oldStep,step.deterministic (oldStep.subst sigma)⟩

/-- A real history whose actual contracted degrees are supported. This is
an explicit syntactic colour condition, not canonicality or an origin field. -/
inductive RegionalHistory (region : Nat → Prop) : List Path → LTerm → LTerm → Prop where
  | nil (t) : RegionalHistory region [] t t
  | cons (step : StepAt p t u) (degree : t.degreeAt p=some l) (support : l.Supported region)
      (rest : RegionalHistory region ps u v) : RegionalHistory region (p::ps) t v

theorem RegionalHistory.history (regional : RegionalHistory region ps t u) : History ps t u := by
  induction regional with
  | nil => exact .nil _
  | cons step degree support tail ih => exact .cons step ih

/-- Every step is reflected to the original body with the exact full schedule;
substitution arguments remain unchanged because they contain no regional node. -/
theorem RegionalHistory.subst_reflect (regional : RegionalHistory region ps (t.subst sigma) u)
    (values : ∀ i value,sigma i=.put value → LTerm.OutsideRegion region value) :
    ∃ oldTarget,History ps t oldTarget ∧ u=oldTarget.subst sigma := by
  induction ps generalizing t u with
  | nil => cases regional; exact ⟨t,.nil _,rfl⟩
  | cons p ps ih =>
    cases regional with
    | cons step degree support rest =>
      obtain ⟨oldMiddle,oldStep,middleEq⟩ := step.subst_reflect values degree support
      rw [middleEq] at rest
      obtain ⟨oldTarget,oldTail,targetEq⟩ := ih rest
      exact ⟨oldTarget,.cons oldStep oldTail,targetEq⟩
end Lamping.Lambda.Labelled
