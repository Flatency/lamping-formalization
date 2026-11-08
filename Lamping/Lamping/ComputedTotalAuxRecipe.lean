import Lamping.Lamping.ComputedFocusProofOnlyBalance

namespace Lamping.AG.ExposureScheduling
open Graph Lambda Lambda.Labelled

private theorem lowerTable_not_beta (left right : Op) (i j beta : Nat) (flip d : Bool) :
    ((if lower : i<j then
      match left with
      | .fan => some (Schema.fanAction right i j lower)
      | .cro => some (Schema.croAction right i j lower)
      | .bra => some (Schema.braAction right i j lower)
      | _ => none
    else none).map (fun schema => (schema,flip))) ≠ some (.beta beta,d) := by
  intro picked
  split at picked
  · cases left <;> simp at picked
  · simp at picked

private theorem controlTable_not_beta (left right : Op) (i j beta : Nat) (d : Bool) :
    computeControlPairSchema left right i j ≠ some (.beta beta,d) := by
  intro picked
  unfold computeControlPairSchema at picked
  split at picked
  · cases left <;> cases right <;> simp at picked
  · split at picked
    · exact lowerTable_not_beta left right i j beta false d picked
    · exact lowerTable_not_beta right left j i beta true d picked

section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable [DecidableEq N] [DecidableEq W]
variable {g : Net signature N B W} {root : B} {directions : B → Bool}
variable {t : Term} {redex : RedexOcc t}

/-- A computed auxiliary recipe records the actual three successful matches.
The equality fields are propositions and do not choose payload data. -/
structure ComputedAuxRecipe (access : ActualRedexAccess g root redex) (inputs : RootInputs g root)
    (balanced : ∃ depths : B → Int, depths root=0 ∧ Nonempty (IndexedLevelBalance g depths))
    (flow : Nonempty (FlowBalance g directions)) where
  focus : PhysicalControlFocus g
  chosen : selectPhysicalControlFocus g access.connection.edges=some focus
  data : FocusCorridorData g
  computed : computeFocusCorridorData access.connection focus=some data
  schema : Schema
  recipe : Readback.ExplicitRewriteRecipe (Readback.ExecutableNet.ofNet g) schema
  run : executableComputedFocusRecipeOfRootBalance access inputs balanced flow focus chosen data computed=
    some ⟨schema,recipe⟩

/-- Follow the actual computations, eliminating impossible empty cases in Prop. -/
def selectComputedAuxRecipe
    (access : ActualRedexAccess g root redex) (inputs : RootInputs g root)
    (balanced : ∃ depths : B → Int, depths root=0 ∧ Nonempty (IndexedLevelBalance g depths))
    (flow : Nonempty (FlowBalance g directions))
    (nonempty : controlWord g access.connection.edges≠[]) :
    ComputedAuxRecipe access inputs balanced flow := by
  cases chosen : selectPhysicalControlFocus g access.connection.edges with
  | none =>
    exact False.elim (by
      obtain ⟨focus,hit⟩ := selectPhysicalControlFocus_total g access.connection.edges nonempty
      rw [chosen] at hit
      cases hit)
  | some focus =>
    cases computed : computeFocusCorridorData access.connection focus with
    | none => exact False.elim (computeFocusCorridorData_ne_none access.connection focus chosen computed)
    | some data =>
      cases run : executableComputedFocusRecipeOfRootBalance access inputs balanced flow focus
          chosen data computed with
      | none =>
        exact False.elim (by
          obtain ⟨depths,rootDepth,⟨balance⟩⟩ := balanced
          have oldRun := run
          rw [executableComputedFocusRecipeOfRootBalance_eq access inputs
            ⟨depths,rootDepth,⟨balance⟩⟩ balance rootDepth flow focus chosen data computed] at oldRun
          obtain ⟨entry,recipe,_table,hit,_left,_right⟩ :=
            executableComputedFocusRecipe_result access inputs balance rootDepth flow focus chosen data computed
          rw [oldRun] at hit
          cases hit)
      | some payload =>
        exact ⟨focus,chosen,data,computed,payload.1,payload.2,run⟩

/-- The certified recipe is auxiliary. Its exact dispatcher equation
identifies it with the recipe for the actual non-beta table entry. -/
theorem ComputedAuxRecipe.not_beta
    {access : ActualRedexAccess g root redex} {inputs : RootInputs g root}
    {balanced : ∃ depths : B → Int, depths root=0 ∧ Nonempty (IndexedLevelBalance g depths)}
    {flow : Nonempty (FlowBalance g directions)}
    (step : ComputedAuxRecipe access inputs balanced flow) (i : Nat) :
    step.schema ≠ .beta i := by
  obtain ⟨depths,rootDepth,⟨balance⟩⟩ := balanced
  obtain ⟨entry,recipe,table,run,_left,_right⟩ :=
    executableComputedFocusRecipe_result access inputs balance rootDepth flow
      step.focus step.chosen step.data step.computed
  have oldRun := step.run
  rw [executableComputedFocusRecipeOfRootBalance_eq access inputs
    ⟨depths,rootDepth,⟨balance⟩⟩ balance rootDepth flow step.focus step.chosen step.data step.computed] at oldRun
  have eqSchema : entry.1=step.schema :=
    congrArg Sigma.fst (Option.some.inj (run.symm.trans oldRun))
  obtain ⟨left,right,actual,ls,rs,computedEntry,_fit⟩ :=
    computeFocusSchema_correct access inputs balance rootDepth step.focus step.chosen step.data step.computed
  have eqEntry := Option.some.inj (computedEntry.symm.trans table)
  subst actual
  have picked : computeControlPairSchema left right (g.label step.data.first.1).index
      (g.label step.data.last.1).index=some entry := by
    simpa only [computeFocusSchema,ls,rs] using table
  intro beta
  have schemaBeta := eqSchema.trans beta
  obtain ⟨schema,flip⟩ := entry
  change schema=.beta i at schemaBeta
  subst schema
  exact controlTable_not_beta left right _ _ i flip picked

/-- The decrease is measured on any fixed matched target access for the same
occurrence, including one supplied by executable readback. -/
theorem ComputedAuxRecipe.fixed_target_decrease
    {current : LTerm} {occ : RedexOcc current.erase}
    {access : ActualRedexAccess g root occ} {inputs : RootInputs g root}
    {balanced : ∃ depths : B → Int, depths root=0 ∧ Nonempty (IndexedLevelBalance g depths)}
    {flow : Nonempty (FlowBalance g directions)}
    (step : ComputedAuxRecipe access inputs balanced flow)
    (matching : Matches g root current.erase) (closed : Closed current.erase)
    (positive : directions root=true) (oldT : Transparency g root)
    (appStamp lamStamp : Lambda.Labelled.Label) (body arg : LTerm)
    (lookup : current.subterm occ.val=some (.app appStamp (.lam lamStamp body) arg))
    (targetMatches : Matches step.recipe.target.graph.net root current.erase)
    (fixed : ActualRedexAccess step.recipe.target.graph.net root occ) :
    ControlWordDecrease (controlWord step.recipe.target.graph.net fixed.connection.edges)
      (controlWord g access.connection.edges) := by
  obtain ⟨schema,recipe,run,witness,strict⟩ := computedLocalProgressOfRootBalance access matching closed
    inputs balanced flow positive oldT appStamp lamStamp body arg lookup step.focus step.chosen
    step.data step.computed
  have same := Option.some.inj (run.symm.trans step.run)
  have sameSchema : schema=step.schema := congrArg Sigma.fst same
  subst schema
  have sameRecipe : recipe=step.recipe := eq_of_heq (Sigma.mk.inj same).2
  subst recipe
  exact controlWordDecrease_of_same_target step.recipe.target.graph targetMatches fixed witness _ strict
end
end Lamping.AG.ExposureScheduling
