import Lamping.Lamping.ComputedFocusRecipeResult
import Lamping.Lamping.ActionCanonicalRoutes
import Lamping.Lamping.CorridorTransport

namespace Lamping.AG.ExposureScheduling
open Graph Lambda
section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable [DecidableEq N] [DecidableEq W]
variable {g : Net signature N B W} {root : B} {depths : B → Int}
variable {boundary : B → Bool}

/-- The site's principal witness is the complete ordered image of the
oriented physical corridor under the returned recipe's source isomorphism. -/
theorem executableComputedFocusRecipe_mapped_principal {t : Term} {redex : RedexOcc t}
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
      ∃ principal : SiteActionPrincipal recipe.site,
        principal.edges = (orientSchemaCorridor route selected.2).edges.map recipe.sourceIso.ends ∧
        access.connection.edges.map recipe.sourceIso.ends =
          ((focus.beforeCorridor access.connection.edges).map recipe.sourceIso.ends ++
            data.edges.map recipe.sourceIso.ends) ++
            (focus.afterCorridor access.connection.edges).map recipe.sourceIso.ends := by
  let route := FocusCorridorData.toTransparentCorridor access.connection focus chosen data computed
  obtain ⟨selected,recipe,table,result,left,right⟩ :=
    executableComputedFocusRecipe_result access inputs balance rootDepth flow focus chosen data computed
  let oriented := orientSchemaCorridor route selected.2
  let mapped := oriented.map recipe.sourceIso
  have start : mapped.edges.head?=some (.inl ⟨.inr (.inl ()),.inl ()⟩) := by
    have head := mapped.start
    change mapped.edges.head?=some (Sum.inl (recipe.sourceIso.ports oriented.first)) at head
    exact head.trans (congrArg (fun p => some (Sum.inl p : Endpoint recipe.site.net)) left)
  have finish : mapped.edges.getLast?=
      some (recipe.site.net.wire (.inl ⟨.inr (.inr ()),.inl ()⟩)) := by
    have last := mapped.finish
    change mapped.edges.getLast?=
      some (recipe.site.net.wire (Sum.inl (recipe.sourceIso.ports oriented.last))) at last
    exact last.trans (congrArg (fun p => some (recipe.site.net.wire (Sum.inl p))) right)
  let principal : SiteActionPrincipal recipe.site := ⟨mapped.edges,start,finish,mapped.transparent⟩
  refine ⟨selected,recipe,table,result,principal,rfl,?_⟩
  have split := computeFocusCorridorData_partition access.connection focus chosen data computed
  simpa only [List.map_append] using congrArg (List.map recipe.sourceIso.ends.toFun) split
end
end Lamping.AG.ExposureScheduling
