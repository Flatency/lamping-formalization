import Lamping.Lamping.ComputedFocusSchemaDispatch

namespace Lamping.AG.ExposureScheduling
open Graph Lambda
section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable [DecidableEq N] [DecidableEq W]
variable {g : Net signature N B W} {root : B} {depths : B → Int}
variable {boundary : B → Bool}

/-- The recipe uses the two ports of this oriented corridor in their schema roles. -/
theorem executableOrientedSchemaRecipe_ports
    (route : TransparentCorridor g) (selected : Schema × Bool)
    (flow : Nonempty (FlowBalance g boundary)) (left right : Op)
    (ls : (g.label route.first.1).sort=.op left)
    (rs : (g.label route.last.1).sort=.op right)
    (lp : IsPrincipal (g:=g) route.first) (rp : IsPrincipal (g:=g) route.last)
    (fit : OrientedControlSchemaFits selected left right
      (g.label route.first.1).index (g.label route.last.1).index) :
    let oriented := orientSchemaCorridor route selected.2
    let recipe := executableOrientedSchemaRecipe route selected flow left right ls rs lp rp fit
    recipe.sourceIso.ports oriented.first = ⟨.inr (.inl ()),.inl ()⟩ ∧
    recipe.sourceIso.ports oriented.last = ⟨.inr (.inr ()),.inl ()⟩ := by
  unfold executableOrientedSchemaRecipe
  apply Readback.explicitRecipeOfPresentation_ports

-- Each scrutinee travels together with its dependent equality argument.
private theorem kindRec_op {C : Sort u} {actual : Kind} {op : Op}
    {onOp : (k : Op) → actual = .op k → C} {onGarbage : actual = .garbage → C}
    (known : actual = .op op) :
    Kind.rec (motive := fun k => actual = k → C) onOp onGarbage actual rfl = onOp op known := by
  let evaluate (x : {k : Kind // actual = k}) : C :=
    Kind.rec (motive := fun k => actual = k → C) onOp onGarbage x.val x.property
  have same : (⟨actual,rfl⟩ : {k : Kind // actual = k}) = ⟨.op op,known⟩ :=
    Subtype.ext known
  exact congrArg evaluate same

private theorem optionRec_some {A : Type v} {C : Sort u} {actual : Option A} {a : A}
    {onNone : actual = none → C} {onSome : (x : A) → actual = some x → C}
    (known : actual = some a) :
    Option.rec (motive := fun x => actual = x → C) onNone onSome actual rfl = onSome a known := by
  let evaluate (x : {k : Option A // actual = k}) : C :=
    Option.rec (motive := fun k => actual = k → C) onNone onSome x.val x.property
  have same : (⟨actual,rfl⟩ : {k : Option A // actual = k}) = ⟨some a,known⟩ :=
    Subtype.ext known
  exact congrArg evaluate same

-- Eliminate the transport of an equality-argument function after a case is chosen.
private theorem eqRec_apply {A : Sort u} {C : Sort v} {o a b : A} {h : a = b}
    {f : o = a → C} {k : o = b} :
    Eq.rec (motive := fun x _ => o = x → C) f h k = f (k.trans h.symm) := by
  cases h
  rfl

/-- The actual computed option returns the recipe for the same selected table
entry and the same corridor, with its two physical ports accounted for. -/
theorem executableComputedFocusRecipe_result {t : Term} {redex : RedexOcc t}
    (access : ActualRedexAccess g root redex) (inputs : RootInputs g root)
    (balance : IndexedLevelBalance g depths) (rootDepth : depths root=0)
    (flow : Nonempty (FlowBalance g boundary)) (focus : PhysicalControlFocus g)
    (chosen : selectPhysicalControlFocus g access.connection.edges=some focus)
    (data : FocusCorridorData g)
    (computed : computeFocusCorridorData access.connection focus=some data) :
    let route := FocusCorridorData.toTransparentCorridor access.connection focus chosen data computed
    ∃ selected, ∃ (recipe : Readback.ExplicitRewriteRecipe (Readback.ExecutableNet.ofNet g) selected.1),
      computeFocusSchema data=some selected ∧
      executableComputedFocusRecipe access inputs balance rootDepth flow focus chosen data computed=
        some ⟨selected.1,recipe⟩ ∧
      recipe.sourceIso.ports (orientSchemaCorridor route selected.2).first =
        ⟨.inr (.inl ()),.inl ()⟩ ∧
      recipe.sourceIso.ports (orientSchemaCorridor route selected.2).last =
        ⟨.inr (.inr ()),.inl ()⟩ := by
  let route := FocusCorridorData.toTransparentCorridor access.connection focus chosen data computed
  obtain ⟨left,right,selected,ls,rs,result,fit⟩ :=
    computeFocusSchema_correct access inputs balance rootDepth focus chosen data computed
  have ports := computeFocusCorridorData_principals access.connection focus chosen data computed
  let recipe := executableOrientedSchemaRecipe route selected flow left right
    ls rs ports.1 ports.2 fit
  refine ⟨selected,recipe,result,?_,?_⟩
  · unfold executableComputedFocusRecipe
    dsimp only
    rw [kindRec_op ls]
    rw [eqRec_apply]
    try dsimp only
    rw [kindRec_op rs]
    rw [eqRec_apply]
    try dsimp only
    rw [optionRec_some result]
    rw [eqRec_apply] <;> rfl
  · exact executableOrientedSchemaRecipe_ports route selected flow left right
      ls rs ports.1 ports.2 fit
end
end Lamping.AG.ExposureScheduling
