import Lamping.Lamping.ComputedFocusRecipeResult
import Lamping.Lamping.RecipeSiteOriginalWordProgress
import Lamping.Lamping.CroAppControlCountProgress

namespace Lamping.AG.ExposureScheduling
open Graph Lambda Lambda.Labelled
section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable [DecidableEq N] [DecidableEq W]
variable {g : Net signature N B W} {root : B} {depths : B → Int}
variable {directions : B → Bool}

private theorem keptLambdaPort {K U V : Type} [FiniteNames K] [FiniteNames U] [FiniteNames V]
    {kept : K → Graph.Label signature} {i j : Nat} {lt : i<j}
    (site : PathSite (.croAction .app i j lt) kept (B:=B) (W:=U) (V:=V))
    (port : NodePort signature (K ⊕ (Unit ⊕ Unit)) site.net.label)
    (index : Nat) (tag : site.net.label port.1=label .lam index) :
    ∃ k, ∃ (p : Port (kept k).sort), port=⟨.inl k,p⟩ := by
  rcases port with ⟨node,p⟩
  rcases node with k | (active | passive)
  · exact ⟨k,p,rfl⟩
  · cases active
    have impossible : Op.cro=Op.lam := Kind.op.inj (congrArg Graph.Label.sort tag)
    cases impossible
  · cases passive
    have impossible : Op.app=Op.lam := Kind.op.inj (congrArg Graph.Label.sort tag)
    cases impossible

/-- The computed reverse Cro/APP branch drops one control letter at its own
executable recipe target, for the same original redex. -/
theorem computedCroAppProgress {current : LTerm} {redex : RedexOcc current.erase}
    (access : ActualRedexAccess g root redex) (matching : Matches g root current.erase)
    (inputs : RootInputs g root)
    (balance : IndexedLevelBalance g depths) (rootDepth : depths root=0)
    (flow : Nonempty (FlowBalance g directions)) (positive : directions root=true)
    (oldT : Transparency g root)
    (reader : ControlOccurrence g)
    (chosen : selectPhysicalControlFocus g access.connection.edges=some (.initialReader reader))
    (data : FocusCorridorData g)
    (computed : computeFocusCorridorData access.connection (.initialReader reader)=some data)
    {i j : Nat} (lt : i<j)
    (table : computeFocusSchema data=some (.croAction .app i j lt,true)) :
    ∃ recipe : Readback.ExplicitRewriteRecipe (Readback.ExecutableNet.ofNet g) (.croAction .app i j lt),
      executableComputedFocusRecipe access inputs balance rootDepth flow (.initialReader reader)
        chosen data computed=some ⟨.croAction .app i j lt,recipe⟩ ∧
      ∃ target : ActualRedexAccess recipe.target.graph.net root redex,
        (controlWord recipe.target.graph.net target.connection.edges).length <
          (controlWord g access.connection.edges).length := by
  have firstPort : data.first=⟨access.connection.app,access.connection.appPort⟩ := by
    cases read : nodePortOfEndpoint g (g.wire reader.entry) with
    | none => simp [computeFocusCorridorData,read] at computed
    | some port =>
      simp only [computeFocusCorridorData,read,Option.map_some,Option.some.injEq] at computed
      subst data
      rfl
  obtain ⟨entry,recipe,actual,result,_left,right⟩ :=
    executableComputedFocusRecipe_result access inputs balance rootDepth flow
      (.initialReader reader) chosen data computed
  have same := Option.some.inj (actual.symm.trans table)
  subst entry
  refine ⟨recipe,result,?_⟩
  let iso := recipe.sourceIso
  let mapped := iso.actualRedexAccess access
  have passivePort : iso.ports ⟨access.connection.app,access.connection.appPort⟩ =
      ⟨.inr (.inr ()),.inl ()⟩ := by
    simpa [orientSchemaCorridor, TransparentCorridor.reverse,
      FocusCorridorData.toTransparentCorridor, firstPort] using right
  have appNode : mapped.connection.app=.inr (.inr ()) := by
    change iso.nodes access.connection.app=_
    exact (iso.port_node ⟨access.connection.app,access.connection.appPort⟩).symm.trans
      (congrArg Sigma.fst passivePort)
  have ctxPort :
      (⟨mapped.connection.app,mapped.ctx⟩ : NodePort signature _ recipe.site.net.label) =
        ⟨.inr (.inr ()),appCtx⟩ :=
    Sigma.ext appNode mapped.contextPrincipal
  have appFinish : mapped.parent.val.getLast?=
      some (recipe.site.net.wire (.inl ⟨.inr (.inr ()),appCtx⟩)) := by
    rw [←ctxPort]
    exact mapped.parentFinish
  obtain ⟨lamNode,lamPort,lamEnd⟩ := keptLambdaPort recipe.site
    ⟨mapped.connection.lam,mapped.connection.lamPort⟩ mapped.connection.lamIndex
    mapped.connection.lamLabel
  have lamFinish : mapped.child.val.getLast?=
      some (recipe.site.net.wire (.inl ⟨.inl lamNode,lamPort⟩)) := by
    rw [←lamEnd,mapped.split,List.getLast?_append,mapped.connection.finish]
    rfl
  obtain ⟨a,b,labels⟩ := access.child.property.1.1
  obtain ⟨flow⟩ := flow
  obtain ⟨target,_child,_word,_count,strict⟩ :=
    mapped.cro_app_control_count_progress recipe.site (iso.matches matching)
      (iso.rootInputs inputs) (iso.flowBalance flow) positive (iso.indexed_balance balance)
      rootDepth (iso.transparency oldT) appFinish lamNode lamPort lamFinish (iso.labelling labels)
  change (controlWord recipe.target.graph.net target.connection.edges).length <
    (controlWord recipe.site.net (iso.actualRedexAccess access).connection.edges).length at strict
  rw [recipe.mappedRedexAccess_controlWord access] at strict
  exact ⟨target,strict⟩
end
end Lamping.AG.ExposureScheduling
