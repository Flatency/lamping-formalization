import Lamping.Lamping.ComputedInitialReaderSchema
import Lamping.Lamping.ComputedTerminalWriterSchema
import Lamping.Lamping.ComputedInternalPeakSchema
import Lamping.Lamping.ComputedFocusCorridorPrincipals
import Lamping.Lamping.ExecutableOrientedSchemaRecipe

namespace Lamping.AG.ExposureScheduling
open Graph Lambda
section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable {g : Net signature N B W} {root : B} {depths : B → Int}

/-- Read only the actual endpoint labels and apply the finite schema table. -/
def computeFocusSchema (data : FocusCorridorData g) : Option (Schema × Bool) :=
  match (g.label data.first.1).sort, (g.label data.last.1).sort with
  | .op left, .op right =>
    computeControlPairSchema left right (g.label data.first.1).index (g.label data.last.1).index
  | _, _ => none

theorem computeFocusSchema_correct {t : Term} {redex : RedexOcc t}
    (access : ActualRedexAccess g root redex) (inputs : RootInputs g root)
    (balance : IndexedLevelBalance g depths) (rootDepth : depths root=0)
    (focus : PhysicalControlFocus g)
    (chosen : selectPhysicalControlFocus g access.connection.edges=some focus)
    (data : FocusCorridorData g)
    (computed : computeFocusCorridorData access.connection focus=some data) :
    ∃ left right selected,
      (g.label data.first.1).sort=.op left ∧
      (g.label data.last.1).sort=.op right ∧
      computeFocusSchema data=some selected ∧
      OrientedControlSchemaFits selected left right
        (g.label data.first.1).index (g.label data.last.1).index := by
  cases focus with
  | initialReader reader =>
    obtain ⟨right,schema,ls,rs,result,fit⟩ :=
      computedInitialReaderSchema access inputs balance rootDepth reader chosen data computed
    exact ⟨.app,right,(schema,true),ls,rs,by simpa only [computeFocusSchema,ls,rs] using result,fit⟩
  | terminalWriter writer =>
    obtain ⟨left,schema,ls,rs,result,fit⟩ :=
      computedTerminalWriterSchema access.connection balance rootDepth writer chosen data computed
    exact ⟨left,.lam,(schema,false),ls,rs,by simpa only [computeFocusSchema,ls,rs] using result,fit⟩
  | internalPeak index writer reader =>
    obtain ⟨left,right,selected,ls,rs,result,fit⟩ :=
      computedInternalPeakSchema access.connection index writer reader chosen data computed
    exact ⟨left,right,selected,ls,rs,by simpa only [computeFocusSchema,ls,rs] using result,fit⟩

/-- The recipe payload follows the actual kind and table cases. Semantic
certificates justify the selected branch solely in the proof of fit. -/
def executableComputedFocusRecipe [DecidableEq N] [DecidableEq W]
    {boundary : B → Bool} {t : Term} {redex : RedexOcc t}
    (access : ActualRedexAccess g root redex) (inputs : RootInputs g root)
    (balance : IndexedLevelBalance g depths) (rootDepth : depths root=0)
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
        have fit : OrientedControlSchemaFits selected left right
            (g.label data.first.1).index (g.label data.last.1).index := by
          obtain ⟨actualLeft,actualRight,actual,al,ar,chosenSchema,actualFit⟩ :=
            computeFocusSchema_correct access inputs balance rootDepth focus chosen data computed
          have eqLeft := Kind.op.inj (al.symm.trans ls)
          have eqRight := Kind.op.inj (ar.symm.trans rs)
          have eqSelected := Option.some.inj (chosenSchema.symm.trans result)
          cases eqLeft
          cases eqRight
          cases eqSelected
          exact actualFit
        have ports := computeFocusCorridorData_principals access.connection focus chosen data computed
        exact some ⟨selected.1,executableOrientedSchemaRecipe route selected flow left right
          ls rs ports.1 ports.2 fit⟩
end
end Lamping.AG.ExposureScheduling
