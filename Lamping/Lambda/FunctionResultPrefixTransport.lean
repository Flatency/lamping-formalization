import Lamping.Lambda.FirstNewReadingOrigins
import Lamping.Lambda.PrerequisiteOrder
namespace Lamping.Lambda.Labelled
private inductive NodeHeadMatch : LTerm → LTerm → Prop where
  | var (stamp index) : NodeHeadMatch (.var stamp index) (.var stamp index)
  | app (stamp oldFn oldArg currentFn currentArg) :
      NodeHeadMatch (.app stamp oldFn oldArg) (.app stamp currentFn currentArg)
  | lam (stamp oldBody currentBody) : NodeHeadMatch (.lam stamp oldBody) (.lam stamp currentBody)
private theorem NodeHeadMatch.refl (t : LTerm) : NodeHeadMatch t t := by
  cases t <;> constructor
private theorem NodeHeadMatch.labels (same : NodeHeadMatch old current) : old.label=current.label := by
  cases same <;> rfl
private theorem StepAt.context_node_heads (step : StepAt site source target)
    (lookup : target.subterm p=some current)
    (outside : ¬∃suffix,p=site++suffix) :
    ∃ old,source.subterm p=some old ∧NodeHeadMatch old current := by
  induction step generalizing p current with
  | root beta alpha body argument => exact False.elim (outside ⟨p,rfl⟩)
  | @fn site fn currentFn stamp argument inner ih =>
    cases p with
    | nil =>
      have same : current=.app stamp currentFn argument := by simpa only [LTerm.subterm,Option.some.injEq] using lookup.symm
      subst current
      exact ⟨_,rfl,.app _ _ _ _ _⟩
    | cons child rest =>
      cases child with
      | body => cases lookup
      | arg => exact ⟨_,lookup,.refl _⟩
      | fn =>
        obtain ⟨old,oldLookup,same⟩ := ih lookup (by
          rintro ⟨suffix,equal⟩; exact outside ⟨suffix,congrArg (Step.fn::·) equal⟩)
        exact ⟨old,oldLookup,same⟩
  | @arg site argument currentArg stamp fn inner ih =>
    cases p with
    | nil =>
      have same : current=.app stamp fn currentArg := by simpa only [LTerm.subterm,Option.some.injEq] using lookup.symm
      subst current
      exact ⟨_,rfl,.app _ _ _ _ _⟩
    | cons child rest =>
      cases child with
      | body => cases lookup
      | fn => exact ⟨_,lookup,.refl _⟩
      | arg =>
        obtain ⟨old,oldLookup,same⟩ := ih lookup (by
          rintro ⟨suffix,equal⟩; exact outside ⟨suffix,congrArg (Step.arg::·) equal⟩)
        exact ⟨old,oldLookup,same⟩
  | @body site body currentBody stamp inner ih =>
    cases p with
    | nil =>
      have same : current=.lam stamp currentBody := by simpa only [LTerm.subterm,Option.some.injEq] using lookup.symm
      subst current
      exact ⟨_,rfl,.lam _ _ _⟩
    | cons child rest =>
      cases child with
      | fn | arg => cases lookup
      | body =>
        obtain ⟨old,oldLookup,same⟩ := ih lookup (by
          rintro ⟨suffix,equal⟩; exact outside ⟨suffix,congrArg (Step.body::·) equal⟩)
        exact ⟨old,oldLookup,same⟩
end Lamping.Lambda.Labelled
namespace Lamping.Lambda.Labelled
private theorem order_all_bound (t : LTerm) (p : Path) : prerequisiteOrder t p<prerequisiteNodeCount t := by
  induction t generalizing p with
  | var => cases p <;> simp only [prerequisiteOrder,prerequisiteNodeCount] <;> omega
  | lam stamp body ih =>
    cases p with
    | nil => simp only [prerequisiteOrder,prerequisiteNodeCount]; omega
    | cons step rest => cases step <;> simp only [prerequisiteOrder,prerequisiteNodeCount]; all_goals have bound := ih rest; omega
  | app stamp fn arg hf ha =>
    cases p with
    | nil => simp only [prerequisiteOrder,prerequisiteNodeCount]; have bound := ha []; omega
    | cons step rest => cases step <;> simp only [prerequisiteOrder,prerequisiteNodeCount]; all_goals have fb := hf rest; have ab := ha rest; omega
private theorem function_descendant_order (lookup : t.subterm parent=some (.app stamp fn arg)) (relative : Path) :
    prerequisiteOrder t ((parent++[.fn])++relative)<prerequisiteOrder t parent := by
  obtain ⟨offset,order⟩ := prerequisiteOrder_subtree lookup
  have root := order []
  have child := order (.fn::relative)
  simp only [List.append_nil,prerequisiteOrder] at root child
  have bound := order_all_bound fn relative
  simpa only [List.append_assoc,List.cons_append,List.nil_append] using (show prerequisiteOrder t (parent++(.fn::relative))<prerequisiteOrder t parent by omega)
private theorem PrerequisitePrefix.finish_order_le (segment : PrerequisitePrefix t start before finish) :
    prerequisiteOrder t finish≤prerequisiteOrder t start := by
  induction segment with
  | refl => exact Nat.le_refl _
  | app lookup notLambda tail ih => have less := (PrerequisiteDependency.app lookup notLambda).order_lt; omega
  | @lam parent child stamp body es finish lookup notFunction tail ih =>
    rw [LTerm.subterm_append] at lookup
    cases atParent : t.subterm parent with
    | none => rw [atParent] at lookup; cases lookup
    | some old =>
      rw [atParent] at lookup
      have actualChild : t.subterm (parent++[child])=some (.lam stamp body) := by rw [LTerm.subterm_append,atParent]; exact lookup
      have less := (PrerequisiteDependency.lam atParent actualChild notFunction).order_lt
      omega
  | var lookup binder split depth tail ih =>
    have less := (PrerequisiteDependency.var lookup binder split depth).order_lt
    omega
private theorem PrerequisitePrefix.outside_function
    (segment : PrerequisitePrefix t start before finish) (finishEq : finish=parent)
    (atParent : t.subterm parent=some (.app stamp fn arg)) :
    ¬∃relative,start=(parent++[.fn])++relative := by
  rintro ⟨relative,equal⟩
  have lower := segment.finish_order_le
  have upper := function_descendant_order atParent relative
  rw [finishEq] at lower
  rw [←equal] at upper
  omega

private theorem function_result_prefix_aux
    {source target : LTerm} {site parent start finish : Path}
    (step : StepAt site source target) (siteEq : site=parent++[.fn])
    (atParent : target.subterm parent=some (.app stamp fn arg))
    (segment : PrerequisitePrefix target start before finish) (finishEq : finish=parent) :
    PrerequisitePrefix source start before parent ∧before.map target.labelAt=before.map source.labelAt := by
  induction segment with
  | refl => exact ⟨by simpa only [finishEq] using (PrerequisitePrefix.refl (t := source) (p := parent)),rfl⟩
  | @app p a currentFn currentArg es endpoint lookup notLambda tail ih =>
    have outside := (PrerequisitePrefix.app lookup notLambda tail).outside_function finishEq atParent
    rw [←siteEq] at outside
    obtain ⟨old,oldLookup,same⟩ := step.context_node_heads lookup outside
    cases same with
    | app oldStamp oldFn oldArg _ _ =>
      have childLookup : target.subterm (p++[Step.fn])=some currentFn := by
        rw [LTerm.subterm_append,lookup]; cases currentFn <;> rfl
      have childOutside := tail.outside_function finishEq atParent
      rw [←siteEq] at childOutside
      obtain ⟨oldChild,oldChildLookup,childSame⟩ := step.context_node_heads childLookup childOutside
      have knownChild : source.subterm (p++[Step.fn])=some oldFn := by
        rw [LTerm.subterm_append,oldLookup]; cases oldFn <;> rfl
      have childEq : oldChild=oldFn := Option.some.inj (oldChildLookup.symm.trans knownChild)
      subst oldChild
      have oldNotLambda : ∀ s b,oldFn≠.lam s b := by
        intro s b impossible
        rw [impossible] at childSame
        cases childSame
        exact notLambda _ _ rfl
      refine ⟨.app oldLookup oldNotLambda (ih finishEq).1,?_⟩
      have headLabels : target.labelAt (p++[Step.fn])=source.labelAt (p++[Step.fn]) := by
        simp only [LTerm.labelAt,childLookup,knownChild,Option.map_some]
        exact congrArg some childSame.labels.symm
      simp only [List.map_cons]
      rw [headLabels,(ih finishEq).2]
  | @lam p child a body es endpoint lookup notFunction tail ih =>
    have outside := (PrerequisitePrefix.lam lookup notFunction tail).outside_function finishEq atParent
    rw [←siteEq] at outside
    obtain ⟨old,oldLookup,same⟩ := step.context_node_heads lookup outside
    cases same with
    | lam oldStamp oldBody _ =>
      refine ⟨.lam oldLookup notFunction (ih finishEq).1,?_⟩
      simp only [List.map_cons,LTerm.labelAt,lookup,oldLookup,Option.map_some]
      exact congrArg (some a::·) (ih finishEq).2
  | @var leaf a index binder origin body rest es endpoint lookup binderLookup split depth tail ih =>
    have outside := (PrerequisitePrefix.var lookup binderLookup split depth tail).outside_function finishEq atParent
    rw [←siteEq] at outside
    obtain ⟨old,oldLookup,same⟩ := step.context_node_heads lookup outside
    cases same with
    | var =>
      have binderOutside := tail.outside_function finishEq atParent
      rw [←siteEq] at binderOutside
      obtain ⟨oldBinder,oldBinderLookup,binderSame⟩ := step.context_node_heads binderLookup binderOutside
      cases binderSame with
      | lam => exact ⟨.var oldLookup oldBinderLookup split depth (ih finishEq).1,(ih finishEq).2⟩
end Lamping.Lambda.Labelled

namespace Lamping.Lambda.Labelled
/-- Before a genuine RESULT-FUNCTION reading, dependency order itself
keeps the whole finite prefix outside the contracted function subtree. -/
theorem StepAt.function_result_prefix_reflect
    {source target fn arg : LTerm} {stamp : Label} {site parent start : Path}
    (step : StepAt site source target) (siteEq : site=parent++[.fn])
    (atParent : target.subterm parent=some (.app stamp fn arg))
    (segment : PrerequisitePrefix target start before parent) :
    PrerequisitePrefix source start before parent ∧
      before.map target.labelAt=before.map source.labelAt :=
  function_result_prefix_aux step siteEq atParent segment rfl

/-- The old two-edge RESULT prerequisite is constructed, then appended
to the reflected actual finite prefix; no old-chain certificate is input. -/
theorem StepAt.function_result_prefix_old_chain
    {source target body argument fn arg : LTerm} {stamp : Label} {site parent start : Path} {beta alpha : Label}
    (step : StepAt site source target)
    (redex : source.subterm site=some (.app beta (.lam alpha body) argument))
    (siteEq : site=parent++[.fn])
    (atParent : target.subterm parent=some (.app stamp fn arg))
    (segment : PrerequisitePrefix target start before parent) :
    PrerequisiteChain source start (before++[site,site++[.fn]]) ∧
      before.map target.labelAt=before.map source.labelAt := by
  obtain ⟨oldPrefix,labels⟩ := step.function_result_prefix_reflect siteEq atParent segment
  have atSite : source.subterm (parent++[.fn])=some (.app beta (.lam alpha body) argument) := by
    simpa only [←siteEq] using redex
  have oldChain := result_function_old_chain atSite
  rw [←siteEq] at oldChain
  exact ⟨oldPrefix.close oldChain,labels⟩
end Lamping.Lambda.Labelled


namespace Lamping.Lambda.Labelled
/-- An actual app outside the contracted subtree retains its literal node
and stamp; its children may have changed internally. -/
theorem StepAt.context_app_origin
    {source target fn arg : LTerm} {site p : Path} {stamp : Label}
    (step : StepAt site source target)
    (lookup : target.subterm p=some (.app stamp fn arg))
    (outside : ¬∃ relative,p=site++relative) :
    ∃ oldFn oldArg,source.subterm p=some (.app stamp oldFn oldArg) := by
  obtain ⟨old,oldLookup,same⟩ := step.context_node_heads lookup outside
  cases same
  exact ⟨_,_,oldLookup⟩

/-- An actual outside lambda retains its literal occurrence and stamp. -/
theorem StepAt.context_lambda_origin
    {source target body : LTerm} {site p : Path} {stamp : Label}
    (step : StepAt site source target)
    (lookup : target.subterm p=some (.lam stamp body))
    (outside : ¬∃ relative,p=site++relative) :
    ∃ oldBody,source.subterm p=some (.lam stamp oldBody) := by
  obtain ⟨old,oldLookup,same⟩ := step.context_node_heads lookup outside
  cases same
  exact ⟨_,oldLookup⟩

/-- An actual outside variable retains its literal coordinate, stamp and
index; no source or label injectivity hypothesis is required. -/
theorem StepAt.context_variable_origin
    {source target : LTerm} {site p : Path} {stamp : Label} {index : Nat}
    (step : StepAt site source target)
    (lookup : target.subterm p=some (.var stamp index))
    (outside : ¬∃ relative,p=site++relative) :
    source.subterm p=some (.var stamp index) := by
  obtain ⟨old,oldLookup,same⟩ := step.context_node_heads lookup outside
  cases same
  exact oldLookup
end Lamping.Lambda.Labelled