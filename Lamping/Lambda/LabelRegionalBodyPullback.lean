import Lamping.Lambda.LabelRegionalReflection
namespace Lamping.Lambda.Labelled

/-- A root-label prefix cannot change a redex degree at any syntax site. -/
theorem LTerm.degreeAt_prepend (t : LTerm) (word : Label) (p : Path) :
    (t.prepend word).degreeAt p=t.degreeAt p := by
  cases t with
  | var label i => cases p <;> simp [LTerm.prepend,LTerm.degreeAt,LTerm.subterm,LTerm.degree]
  | lam label body =>
    cases p with
    | nil => rfl
    | cons edge rest => cases edge <;> rfl
  | app label fn argument =>
    cases p with
    | nil => cases fn <;> rfl
    | cons edge rest => cases edge <;> rfl

/-- Strip a transported old root prefix from an actual step, retaining its
site and its exact target. No label support or INIT premise is needed. -/
theorem StepAt.prepend_reflect (step : StepAt p (t.prepend word) u) :
    ∃ oldTarget,StepAt p t oldTarget ∧ u=oldTarget.prepend word := by
  obtain ⟨oldTarget,oldStep,_⟩ := lift_betaAt (t := t) (by simpa using step.betaAt)
  exact ⟨oldTarget,oldStep,step.deterministic (oldStep.prepend word)⟩

/-- Prefix removal preserves the explicit regional colour of every actual
contraction, rather than merely its final degree. -/
theorem RegionalHistory.prepend_reflect
    (regional : RegionalHistory region ps (t.prepend word) u) :
    ∃ oldTarget,RegionalHistory region ps t oldTarget ∧ u=oldTarget.prepend word := by
  induction ps generalizing t u with
  | nil => cases regional; exact ⟨t,.nil _,rfl⟩
  | cons p ps ih =>
    cases regional with
    | cons step degree support rest =>
      obtain ⟨oldMiddle,oldStep,middleEq⟩ := step.prepend_reflect
      rw [middleEq] at rest
      obtain ⟨oldTarget,oldTail,targetEq⟩ := ih rest
      refine ⟨oldTarget,.cons oldStep ?_ support oldTail,targetEq⟩
      simpa only [LTerm.degreeAt_prepend] using degree

/-- An actual region-coloured history after a beta step pulls back to an
actual original-body history with the identical ordered schedule. Argument
labels must be outside the region; canonicality is not silently substituted
for the explicit colour premise. -/
theorem RegionalHistory.contract_body_reflect
    (regional : RegionalHistory region ps (LTerm.contract beta alpha body argument) u)
    (outside : LTerm.OutsideRegion region argument) :
    ∃ oldTarget,History ps body oldTarget ∧ u=LTerm.contract beta alpha oldTarget argument := by
  obtain ⟨middle,coloured,targetEq⟩ := regional.prepend_reflect
  have values : ∀ i value,LTerm.single (argument.prepend alpha.under) i=.put value →
      LTerm.OutsideRegion region value := by
    intro i value equal
    cases i with
    | zero => cases equal; exact outside.prepend alpha.under
    | succ i => cases equal
  obtain ⟨oldTarget,oldHistory,middleEq⟩ := coloured.subst_reflect values
  exact ⟨oldTarget,oldHistory,by rw [targetEq,middleEq]; rfl⟩
end Lamping.Lambda.Labelled

