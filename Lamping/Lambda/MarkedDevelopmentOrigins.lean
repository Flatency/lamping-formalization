import Lamping.Lambda.LabelDegreeAtoms
import Lamping.Lambda.LabelResiduals
namespace Lamping.Lambda.Labelled
/-- Exact degree membership in the original selected old names. -/
def SelectedDegree (original : LTerm) (old : List Path) (degree : Label) : Prop :=
  ∃ name,name∈old ∧ original.degreeAt name=some degree
/-- Real actual events with their proved degree guard. Top-level development
theorems derive this certificate from old-name relativity, never assume it. -/
inductive GuardedDegreeHistory (allowed : Label → Prop) : List Path → LTerm → LTerm → Prop where
  | nil (t) : GuardedDegreeHistory allowed [] t t
  | cons (step : StepAt p t u) (guard : ∀ degree,t.degreeAt p=some degree → allowed degree)
      (tail : GuardedDegreeHistory allowed ps u v) : GuardedDegreeHistory allowed (p::ps) t v

theorem GuardedDegreeHistory.history (guarded : GuardedDegreeHistory allowed ps t u) : History ps t u := by
  induction guarded with
  | nil => exact .nil _
  | cons step _ _ ih => exact .cons step ih
/-- Source selection and actual trace/degree alignment force the degree of
EVERY event, without an event-membership assumption from the caller. -/
theorem DegreeAligned.relative_guarded {original : LTerm}
    (relative : Marked.RelativeHistory ps m n) (selected : Marked.Selected old m)
    (aligned : DegreeAligned original.degreeAt m t) (labels : History ps t u) :
    GuardedDegreeHistory (SelectedDegree original old) ps t u := by
  induction relative generalizing t u with
  | nil => cases labels; exact .nil _
  | @cons site current next restSites last event tail ih =>
    cases labels with
    | cons step rest =>
      obtain ⟨name,member,trace⟩ := (Marked.active_iff_selected_trace selected _).mp event.active
      have guard : ∀ degree,t.degreeAt site=some degree → SelectedDegree original old degree := by
        intro degree atDegree
        exact ⟨name,member,(aligned.trace_degree trace).symm.trans atDegree⟩
      exact .cons step guard (ih (event.selected selected) (aligned.step event.reductionAt step) rest)

theorem SelectedDegree.atomic (initial : INIT original) (selected : SelectedDegree original old degree) :
    IsAtomic degree := by
  obtain ⟨_,_,atDegree⟩ := selected
  obtain ⟨_,atLambda⟩ := LTerm.degreeAt_lambda atDegree
  exact initial.1 degree (LTerm.label_mem_of_subterm atLambda)

mutual
  /-- Each bar payload is exactly allowed, AND all bars inside that payload
  satisfy the same condition. Ordinary outer atoms impose no restriction. -/
  def Label.BarsFrom (allowed : Label → Prop) : Label → Prop
    | .single letter => letter.BarsFrom allowed
    | .cons letter rest => letter.BarsFrom allowed ∧ rest.BarsFrom allowed
  def Letter.BarsFrom (allowed : Label → Prop) : Letter → Prop
    | .atom _ => True
    | .over degree | .under degree => allowed degree ∧ degree.BarsFrom allowed
end

theorem Label.barsFrom_concat (allowed) : ∀ a b : Label,
    (a.concat b).BarsFrom allowed ↔ a.BarsFrom allowed ∧ b.BarsFrom allowed
  | .single _,_ => Iff.rfl
  | .cons a l,b => by simp [Label.concat,Label.BarsFrom,barsFrom_concat,and_assoc]
namespace LTerm
def BarsFrom (allowed : Label → Prop) : LTerm → Prop
  | .var label _ => label.BarsFrom allowed
  | .lam label body => label.BarsFrom allowed ∧ body.BarsFrom allowed
  | .app label fn arg => label.BarsFrom allowed ∧ fn.BarsFrom allowed ∧ arg.BarsFrom allowed

theorem barsFrom_iff (allowed) (t : LTerm) :
    t.BarsFrom allowed ↔ ∀ label∈t.labels,label.BarsFrom allowed := by
  induction t with
  | var => simp [BarsFrom,labels]
  | lam _ _ ih => simp [BarsFrom,labels,ih]
  | app _ _ _ hf ha => simp [BarsFrom,labels,hf,ha,or_imp,forall_and]

theorem BarsFrom.rename {t : LTerm} (safe : t.BarsFrom allowed) (rho) :
    (t.rename rho).BarsFrom allowed := by
  induction t generalizing rho with
  | var => exact safe
  | lam _ _ ih => exact ⟨safe.1,ih safe.2 _⟩
  | app _ _ _ hf ha => exact ⟨safe.1,hf safe.2.1 _,ha safe.2.2 _⟩

theorem BarsFrom.prepend {t : LTerm} {barLabel : Label} (safe : t.BarsFrom allowed) (barPrefix : barLabel.BarsFrom allowed) :
    (t.prepend barLabel).BarsFrom allowed := by
  cases t with
  | var => exact (Label.barsFrom_concat _ _ _).mpr ⟨barPrefix,safe⟩
  | lam => exact ⟨(Label.barsFrom_concat _ _ _).mpr ⟨barPrefix,safe.1⟩,safe.2⟩
  | app => exact ⟨(Label.barsFrom_concat _ _ _).mpr ⟨barPrefix,safe.1⟩,safe.2⟩

def SubValue.BarsFrom (allowed : Label → Prop) : SubValue → Prop
  | .keep _ => True
  | .put t => t.BarsFrom allowed

theorem BarsFrom.subst {t : LTerm} {sigma : Nat → SubValue}
    (safe : t.BarsFrom allowed) (values : ∀ i,(sigma i).BarsFrom allowed) :
    (t.subst sigma).BarsFrom allowed := by
  induction t generalizing sigma with
  | var label i =>
    cases eq : sigma i with
    | keep j => simpa only [LTerm.subst,eq,BarsFrom] using safe
    | put u =>
      have safeValue : u.BarsFrom allowed := by simpa only [SubValue.BarsFrom,eq] using values i
      simpa only [LTerm.subst,eq] using safeValue.prepend safe
  | app _ _ _ hf ha => exact ⟨safe.1,hf safe.2.1 values,ha safe.2.2 values⟩
  | lam _ _ ih =>
    refine ⟨safe.1,ih safe.2 ?_⟩
    intro i
    cases i with
    | zero => trivial
    | succ i =>
      cases eq : sigma i with
      | keep j => simp [lift,eq,SubValue.BarsFrom]
      | put u =>
        have safeValue : u.BarsFrom allowed := by simpa only [SubValue.BarsFrom,eq] using values i
        simpa only [lift,eq,SubValue.BarsFrom] using safeValue.rename Nat.succ

theorem BarsFrom.contract {body arg : LTerm} (bodySafe : body.BarsFrom allowed)
    (argSafe : arg.BarsFrom allowed) (appSafe : beta.BarsFrom allowed)
    (degreeSafe : alpha.BarsFrom allowed) (selected : allowed alpha) :
    (contract beta alpha body arg).BarsFrom allowed := by
  apply BarsFrom.prepend
  · apply bodySafe.subst
    intro i
    cases i with
    | zero => exact argSafe.prepend ⟨selected,degreeSafe⟩
    | succ i => trivial
  · exact (Label.barsFrom_concat _ _ _).mpr ⟨appSafe,selected,degreeSafe⟩
end LTerm

theorem INIT.barsFrom (initial : INIT t) (allowed) : t.BarsFrom allowed := by
  rw [LTerm.barsFrom_iff]
  intro label member
  obtain ⟨_,rfl⟩ := initial.1 label member
  trivial

theorem StepAt.barsFrom (step : StepAt p t u) (safe : t.BarsFrom allowed)
    (guard : ∀ degree,t.degreeAt p=some degree → allowed degree) : u.BarsFrom allowed := by
  induction step with
  | root beta alpha body arg =>
    exact safe.2.1.2.contract safe.2.2 safe.1 safe.2.1.1 (guard alpha rfl)
  | fn _ ih => exact ⟨safe.1,ih safe.2.1 guard,safe.2.2⟩
  | arg _ ih => exact ⟨safe.1,safe.2.1,ih safe.2.2 guard⟩
  | body _ ih => exact ⟨safe.1,ih safe.2 guard⟩

theorem GuardedDegreeHistory.barsFrom (guarded : GuardedDegreeHistory allowed ps t u)
    (safe : t.BarsFrom allowed) : u.BarsFrom allowed := by
  induction guarded with
  | nil => exact safe
  | cons step guard _ ih => exact ih (step.barsFrom safe guard)
/-- Original INIT is used once. All later guards come from actual marked
old-name relativity aligned with this very labelled schedule; reducts are not reset. -/
theorem relative_development_origin_guards (initial : INIT original)
    (relative : Marked.RelativeHistory ps (Marked.mark old original.erase) marked)
    (labels : History ps original target) :
    GuardedDegreeHistory (SelectedDegree original old) ps original target ∧
      target.BarsFrom (SelectedDegree original old) := by
  have guarded := DegreeAligned.relative_guarded relative (Marked.selected_mark old original.erase)
    (DegreeAligned.initial original old) labels
  exact ⟨guarded,guarded.barsFrom (initial.barsFrom _)⟩
end Lamping.Lambda.Labelled


