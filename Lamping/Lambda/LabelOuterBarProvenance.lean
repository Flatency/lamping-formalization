import Lamping.Lambda.LabelHistories

namespace Lamping.Lambda.Labelled

/-- A policy on the immediate over/under payloads in the outer label word.
Unlike BarsSafe's atomic-region condition, this does not traverse payloads. -/
def Label.OuterBarsSafe (allowed : Label → Prop) : Label → Prop
  | .single (.atom _) => True
  | .single (.over payload) | .single (.under payload) => allowed payload
  | .cons (.atom _) rest => rest.OuterBarsSafe allowed
  | .cons (.over payload) rest | .cons (.under payload) rest =>
      allowed payload ∧rest.OuterBarsSafe allowed

theorem Label.outerBarsSafe_concat (allowed) : ∀ a b : Label,
    (a.concat b).OuterBarsSafe allowed ↔a.OuterBarsSafe allowed ∧b.OuterBarsSafe allowed
  | .single letter,b => by cases letter <;> simp [Label.concat,Label.OuterBarsSafe]
  | .cons letter rest,b => by
    cases letter <;> simp [Label.concat,Label.OuterBarsSafe,outerBarsSafe_concat allowed rest b,and_assoc]

namespace LTerm
def OuterBarsSafe (allowed : Label → Prop) : LTerm → Prop
  | .var label _ => label.OuterBarsSafe allowed
  | .lam label body => label.OuterBarsSafe allowed ∧body.OuterBarsSafe allowed
  | .app label fn arg => label.OuterBarsSafe allowed ∧fn.OuterBarsSafe allowed ∧arg.OuterBarsSafe allowed

theorem outerBarsSafe_iff (allowed) (term : LTerm) :
    term.OuterBarsSafe allowed ↔∀ label∈term.labels,label.OuterBarsSafe allowed := by
  induction term with
  | var => simp [OuterBarsSafe,labels]
  | lam _ _ ih => simp [OuterBarsSafe,labels,ih]
  | app _ _ _ hf ha => simp [OuterBarsSafe,labels,hf,ha,or_imp,forall_and]

theorem OuterBarsSafe.rename {term : LTerm} {allowed : Label → Prop}
    (safe : term.OuterBarsSafe allowed) (rho) :
    (term.rename rho).OuterBarsSafe allowed := by
  induction term generalizing rho with
  | var => exact safe
  | lam _ _ ih => exact ⟨safe.1,ih safe.2 _⟩
  | app _ _ _ hf ha => exact ⟨safe.1,hf safe.2.1 _,ha safe.2.2 _⟩

theorem OuterBarsSafe.prepend {term : LTerm} {allowed : Label → Prop} {prefixLabel : Label}
    (safe : term.OuterBarsSafe allowed) (prefixSafe : prefixLabel.OuterBarsSafe allowed) :
    (term.prepend prefixLabel).OuterBarsSafe allowed := by
  cases term with
  | var => exact (Label.outerBarsSafe_concat _ _ _).mpr ⟨prefixSafe,safe⟩
  | lam => exact ⟨(Label.outerBarsSafe_concat _ _ _).mpr ⟨prefixSafe,safe.1⟩,safe.2⟩
  | app => exact ⟨(Label.outerBarsSafe_concat _ _ _).mpr ⟨prefixSafe,safe.1⟩,safe.2⟩

def SubValue.OuterBarsSafe (allowed : Label → Prop) : SubValue → Prop
  | .keep _ => True
  | .put term => term.OuterBarsSafe allowed

theorem OuterBarsSafe.subst {term : LTerm} {allowed : Label → Prop} {sigma : Nat → SubValue}
    (safe : term.OuterBarsSafe allowed)
    (values : ∀ i,(sigma i).OuterBarsSafe allowed) :
    (term.subst sigma).OuterBarsSafe allowed := by
  induction term generalizing sigma with
  | var label i =>
    cases value : sigma i with
    | keep j => simpa only [LTerm.subst,value] using safe
    | put other =>
      have otherSafe : other.OuterBarsSafe allowed := by
        simpa only [value,SubValue.OuterBarsSafe] using values i
      simpa only [LTerm.subst,value] using otherSafe.prepend safe
  | lam _ _ ih =>
    refine ⟨safe.1,ih safe.2 ?_⟩
    intro i
    cases i with
    | zero => trivial
    | succ i =>
      cases value : sigma i with
      | keep j => simp only [lift,value,SubValue.OuterBarsSafe]
      | put other =>
        have otherSafe : other.OuterBarsSafe allowed := by
          simpa only [value,SubValue.OuterBarsSafe] using values i
        simpa only [lift,value,SubValue.OuterBarsSafe] using otherSafe.rename Nat.succ
  | app _ _ _ hf ha => exact ⟨safe.1,hf safe.2.1 values,ha safe.2.2 values⟩

theorem OuterBarsSafe.contract (bodySafe : body.OuterBarsSafe allowed)
    (argumentSafe : argument.OuterBarsSafe allowed)
    (appSafe : beta.OuterBarsSafe allowed) (degreeAllowed : allowed alpha) :
    (contract beta alpha body argument).OuterBarsSafe allowed := by
  apply OuterBarsSafe.prepend
  · apply bodySafe.subst
    intro i
    cases i with
    | zero => exact argumentSafe.prepend degreeAllowed
    | succ i => trivial
  · exact (Label.outerBarsSafe_concat _ _ _).mpr ⟨appSafe,degreeAllowed⟩
end LTerm

theorem INIT.outerBarsSafe (initial : INIT source) (allowed) : source.OuterBarsSafe allowed := by
  rw [LTerm.outerBarsSafe_iff]
  intro label member
  obtain ⟨n,rfl⟩ := initial.1 label member
  trivial

theorem StepAt.outerBarsSafe (step : StepAt path source target)
    (safe : source.OuterBarsSafe allowed)
    (degreeAllowed : ∀ degree,source.degreeAt path=some degree →allowed degree) :
    target.OuterBarsSafe allowed := by
  induction step with
  | root beta alpha body argument =>
    exact safe.2.1.2.contract safe.2.2 safe.1 (degreeAllowed alpha rfl)
  | fn _ ih => exact ⟨safe.1,ih safe.2.1 degreeAllowed,safe.2.2⟩
  | arg _ ih => exact ⟨safe.1,safe.2.1,ih safe.2.2 degreeAllowed⟩
  | body _ ih => exact ⟨safe.1,ih safe.2 degreeAllowed⟩

/-- One actual event of this exact labelled schedule, retaining both finite
prefix and suffix and the degree of the term immediately before firing. -/
def FiresDegree (degree : Label) (ps : List Path) (source target : LTerm) : Prop :=
  ∃ before path after current next,
    ps=before++path::after ∧History before source current ∧StepAt path current next ∧
    current.degreeAt path=some degree ∧History after next target

/-- An outer marker with a forbidden payload cannot appear without an
actual firing of that degree, unless that marker was already in the source.
No INIT, whole-family or completeness assumption is needed for provenance. -/
theorem History.outerBarsSafe_or_fires_degree (history : History ps source target)
    (safe : source.OuterBarsSafe (fun payload=>payload≠degree)) :
    target.OuterBarsSafe (fun payload=>payload≠degree) ∨FiresDegree degree ps source target := by
  induction history with
  | nil => exact .inl safe
  | @cons path source middle rest target step tail ih =>
    by_cases fires : source.degreeAt path=some degree
    · exact .inr ⟨[],path,rest,source,middle,rfl,.nil _,step,fires,tail⟩
    · have nextSafe := step.outerBarsSafe safe (by
        intro other atPath same
        subst other
        exact fires atPath)
      rcases ih nextSafe with finalSafe | fired
      · exact .inl finalSafe
      · obtain ⟨before,nextPath,after,current,next,equal,first,turn,atDegree,last⟩ := fired
        exact .inr ⟨path::before,nextPath,after,current,next,
          congrArg (path::·) equal,.cons step first,turn,atDegree,last⟩

theorem History.outerBarsSafe_of_no_firing (history : History ps source target)
    (safe : source.OuterBarsSafe (fun payload=>payload≠degree))
    (absent : ¬FiresDegree degree ps source target) :
    target.OuterBarsSafe (fun payload=>payload≠degree) :=
  (history.outerBarsSafe_or_fires_degree safe).resolve_right absent

/-- From an actual atomic INIT, every forbidden outer marker in a current
edge label has an actual degree-firing event in the SAME global schedule.
This is provenance only, not freshness for an unused historical family. -/
theorem History.outer_bar_fired (history : History ps source target) (initial : INIT source)
    (member : label∈target.labels)
    (marker : ¬label.OuterBarsSafe (fun payload=>payload≠degree)) :
    FiresDegree degree ps source target := by
  rcases history.outerBarsSafe_or_fires_degree (initial.outerBarsSafe _) with safe | fired
  · exact False.elim (marker ((LTerm.outerBarsSafe_iff _ _).mp safe label member))
  · exact fired

end Lamping.Lambda.Labelled
