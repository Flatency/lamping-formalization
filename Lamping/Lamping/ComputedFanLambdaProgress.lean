import Lamping.Lamping.ComputedFocusRecipeResult
import Lamping.Lamping.RecipeSiteOriginalWordProgress
import Lamping.Lamping.FanLambdaTerminalConnectionProgress

namespace Lamping.AG.ExposureScheduling
open Graph Lambda Lambda.Labelled
section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable [DecidableEq N] [DecidableEq W]
variable {g : Net signature N B W} {root : B} {depths : B → Int}
variable {directions : B → Bool}

/-- The computed terminal Fan/λ case decreases the original control count at
the actual executable recipe target for this same redex. -/
theorem computedFanLambdaProgress {current : LTerm} {redex : RedexOcc current.erase}
    (access : ActualRedexAccess g root redex) (matching : Matches g root current.erase)
    (inputs : RootInputs g root)
    (balance : IndexedLevelBalance g depths) (rootDepth : depths root=0)
    (flow : Nonempty (FlowBalance g directions)) (positive : directions root=true)
    (oldT : Transparency g root)
    (writer : ControlOccurrence g)
    (chosen : selectPhysicalControlFocus g access.connection.edges=some (.terminalWriter writer))
    (data : FocusCorridorData g)
    (computed : computeFocusCorridorData access.connection (.terminalWriter writer)=some data)
    {i j : Nat} (lt : i<j)
    (table : computeFocusSchema data=some (.fanAction .lam i j lt,false)) :
    ∃ recipe : Readback.ExplicitRewriteRecipe (Readback.ExecutableNet.ofNet g) (.fanAction .lam i j lt),
      executableComputedFocusRecipe access inputs balance rootDepth flow (.terminalWriter writer)
        chosen data computed=some ⟨.fanAction .lam i j lt,recipe⟩ ∧
      ∃ target : ActualRedexAccess recipe.target.graph.net root redex,
        (controlWord recipe.target.graph.net target.connection.edges).length <
          (controlWord g access.connection.edges).length := by
  have shape := computed
  simp only [computeFocusCorridorData,Option.some.injEq] at shape
  subst data
  obtain ⟨entry,recipe,actual,result,_left,right⟩ :=
    executableComputedFocusRecipe_result access inputs balance rootDepth flow
      (.terminalWriter writer) chosen _ computed
  have same := Option.some.inj (actual.symm.trans table)
  subst entry
  refine ⟨recipe,result,?_⟩
  let iso := recipe.sourceIso
  let mapped := iso.actualRedexAccess access
  have terminalPort : iso.ports ⟨access.connection.lam,access.connection.lamPort⟩ =
      ⟨.inr (.inr ()),.inl ()⟩ := by
    simpa [orientSchemaCorridor, FocusCorridorData.toTransparentCorridor] using right
  have oldFinish : access.child.val.getLast?=
      some (g.wire (Sum.inl ⟨access.connection.lam,access.connection.lamPort⟩)) := by
    rw [access.split,List.getLast?_append,access.connection.finish]
    rfl
  have finish : mapped.child.val.getLast?=
      some (recipe.site.net.wire (.inl ⟨.inr (.inr ()),.inl ()⟩)) := by
    change (access.child.val.map iso.ends).getLast?=_
    rw [List.getLast?_map,oldFinish,Option.map_some]
    exact (congrArg some
      (iso.wiring (Sum.inl (Sigma.mk access.connection.lam access.connection.lamPort)))).trans
      (by rw [iso.node_end,terminalPort])
  obtain ⟨a,b,labels⟩ := access.child.property.1.1
  obtain ⟨flow⟩ := flow
  obtain ⟨_q,target,_middle,_child,_turn,_word,_count,strict⟩ :=
    mapped.fan_lam_control_count_progress recipe.site (iso.matches matching)
      (iso.rootInputs inputs) (iso.flowBalance flow) positive (iso.indexed_balance balance)
      rootDepth (iso.transparency oldT) finish (iso.labelling labels)
  change (controlWord recipe.target.graph.net target.connection.edges).length <
    (controlWord recipe.site.net (iso.actualRedexAccess access).connection.edges).length at strict
  rw [recipe.mappedRedexAccess_controlWord access] at strict
  exact ⟨target,strict⟩
end
end Lamping.AG.ExposureScheduling
