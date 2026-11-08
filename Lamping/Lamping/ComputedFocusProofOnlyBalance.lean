import Lamping.Lamping.ComputedLocalProgress

namespace Lamping.AG.ExposureScheduling
open Graph Lambda Lambda.Labelled
section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable [DecidableEq N] [DecidableEq W]
variable {g : Net signature N B W} {root : B}

omit [DecidableEq N] [DecidableEq W] in
private theorem focusFitFromRootBalance {t : Term} {redex : RedexOcc t}
    (access : ActualRedexAccess g root redex) (inputs : RootInputs g root)
    (balanced : ∃ depths : B → Int, depths root=0 ∧ Nonempty (IndexedLevelBalance g depths))
    (focus : PhysicalControlFocus g)
    (chosen : selectPhysicalControlFocus g access.connection.edges=some focus)
    (data : FocusCorridorData g)
    (computed : computeFocusCorridorData access.connection focus=some data)
    (left right : Op) (selected : Schema × Bool)
    (ls : (g.label data.first.1).sort=.op left)
    (rs : (g.label data.last.1).sort=.op right)
    (result : computeFocusSchema data=some selected) :
    OrientedControlSchemaFits selected left right
      (g.label data.first.1).index (g.label data.last.1).index := by
  obtain ⟨depths,rootDepth,⟨balance⟩⟩ := balanced
  obtain ⟨actualLeft,actualRight,actual,al,ar,chosenSchema,actualFit⟩ :=
    computeFocusSchema_correct access inputs balance rootDepth focus chosen data computed
  have eqLeft := Kind.op.inj (al.symm.trans ls)
  have eqRight := Kind.op.inj (ar.symm.trans rs)
  have eqSelected := Option.some.inj (chosenSchema.symm.trans result)
  cases eqLeft
  cases eqRight
  cases eqSelected
  exact actualFit

/-- The root balance is used only to certify the actual table result. -/
def executableComputedFocusRecipeOfRootBalance {boundary : B → Bool}
    {t : Term} {redex : RedexOcc t}
    (access : ActualRedexAccess g root redex) (inputs : RootInputs g root)
    (balanced : ∃ depths : B → Int, depths root=0 ∧ Nonempty (IndexedLevelBalance g depths))
    (flow : Nonempty (FlowBalance g boundary)) (focus : PhysicalControlFocus g)
    (chosen : selectPhysicalControlFocus g access.connection.edges=some focus)
    (data : FocusCorridorData g)
    (computed : computeFocusCorridorData access.connection focus=some data) :
    Option (Σ schema : Schema, Readback.ExplicitRewriteRecipe (Readback.ExecutableNet.ofNet g) schema) := by
  let route := FocusCorridorData.toTransparentCorridor access.connection focus chosen data computed
  cases ls : (g.label data.first.1).sort with
  | garbage => exact none
  | op left =>
    cases rs : (g.label data.last.1).sort with
    | garbage => exact none
    | op right =>
      cases result : computeFocusSchema data with
      | none => exact none
      | some selected =>
        have fit := focusFitFromRootBalance access inputs balanced focus chosen data computed
          left right selected ls rs result
        have ports := computeFocusCorridorData_principals access.connection focus chosen data computed
        exact some ⟨selected.1,executableOrientedSchemaRecipe route selected flow left right
          ls rs ports.1 ports.2 fit⟩

/-- Both dispatchers run the same cases with the same recipe data. -/
theorem executableComputedFocusRecipeOfRootBalance_eq {boundary : B → Bool}
    {t : Term} {redex : RedexOcc t} {depths : B → Int}
    (access : ActualRedexAccess g root redex) (inputs : RootInputs g root)
    (balanced : ∃ ds : B → Int, ds root=0 ∧ Nonempty (IndexedLevelBalance g ds))
    (balance : IndexedLevelBalance g depths) (rootDepth : depths root=0)
    (flow : Nonempty (FlowBalance g boundary)) (focus : PhysicalControlFocus g)
    (chosen : selectPhysicalControlFocus g access.connection.edges=some focus)
    (data : FocusCorridorData g)
    (computed : computeFocusCorridorData access.connection focus=some data) :
    executableComputedFocusRecipeOfRootBalance access inputs balanced flow focus chosen data computed =
      executableComputedFocusRecipe access inputs balance rootDepth flow focus chosen data computed := by
  cases ls : (g.label data.first.1).sort with
  | garbage =>
    simp only [executableComputedFocusRecipeOfRootBalance,executableComputedFocusRecipe]
  | op left =>
    cases rs : (g.label data.last.1).sort with
    | garbage =>
      simp only [executableComputedFocusRecipeOfRootBalance,executableComputedFocusRecipe]
    | op right =>
      cases result : computeFocusSchema data <;>
        simp only [executableComputedFocusRecipeOfRootBalance,executableComputedFocusRecipe]

/-- Strict progress for the proof-only balance dispatcher, on its actual target. -/
theorem computedLocalProgressOfRootBalance {current : LTerm} {redex : RedexOcc current.erase}
    (access : ActualRedexAccess g root redex) (matching : Matches g root current.erase)
    (closed : Closed current.erase) (inputs : RootInputs g root)
    (balanced : ∃ depths : B → Int, depths root=0 ∧ Nonempty (IndexedLevelBalance g depths))
    {directions : B → Bool}
    (flow : Nonempty (FlowBalance g directions)) (positive : directions root=true)
    (oldT : Transparency g root)
    (appStamp lamStamp : Lambda.Labelled.Label) (body arg : LTerm)
    (lookup : current.subterm redex.val=some (.app appStamp (.lam lamStamp body) arg))
    (focus : PhysicalControlFocus g)
    (chosen : selectPhysicalControlFocus g access.connection.edges=some focus)
    (data : FocusCorridorData g)
    (computed : computeFocusCorridorData access.connection focus=some data) :
    ∃ schema, ∃ (recipe : Readback.ExplicitRewriteRecipe (Readback.ExecutableNet.ofNet g) schema),
      executableComputedFocusRecipeOfRootBalance access inputs balanced flow focus chosen data computed=
        some ⟨schema,recipe⟩ ∧
      ∃ target : ActualRedexAccess recipe.target.graph.net root redex,
        ControlWordDecrease (controlWord recipe.target.graph.net target.connection.edges)
          (controlWord g access.connection.edges) := by
  obtain ⟨depths,rootDepth,⟨balance⟩⟩ := balanced
  rw [executableComputedFocusRecipeOfRootBalance_eq access inputs
    ⟨depths,rootDepth,⟨balance⟩⟩ balance rootDepth flow focus chosen data computed]
  exact computedLocalProgress access matching closed inputs balance rootDepth flow positive oldT
    appStamp lamStamp body arg lookup focus chosen data computed
end
end Lamping.AG.ExposureScheduling
