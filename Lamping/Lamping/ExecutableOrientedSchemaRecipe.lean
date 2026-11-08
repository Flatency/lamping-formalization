import Lamping.Lamping.ExecutableCorridorPresentation
import Lamping.Lamping.ComputedControlSchemaTable
import Lamping.Lamping.CorridorFlow
import Lamping.Lamping.CorridorReverse
import Lamping.Lamping.PrincipalCorridorExtraction

namespace Lamping.AG.ExposureScheduling
open Graph
section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable {g : Net signature N B W} {boundary : B → Bool}

/-- The direction bit acts on the same physical route. -/
def orientSchemaCorridor (route : TransparentCorridor g) (reverse : Bool) :
    TransparentCorridor g :=
  if reverse then route.reverse else route

private theorem endpointFits (port : NodePort signature N g.label) (op : Op) (index : Nat)
    (sort : (g.label port.1).sort=.op op) (level : (g.label port.1).index=index)
    (principal : IsPrincipal (g:=g) port) :
    g.label port.1=label op index ∧ HEq port.2 (Sum.inl () : Port (.op op)) := by
  obtain ⟨actual,actualSort,actualPrincipal⟩ := principal
  have same : actual=op := Kind.op.inj (actualSort.symm.trans sort)
  subst actual
  refine ⟨?_,actualPrincipal⟩
  generalize h : g.label port.1 = tag at sort level ⊢
  cases tag
  cases sort
  cases level
  rfl

private theorem orientedEndpoints (route : TransparentCorridor g) (selected : Schema × Bool)
    (left right : Op)
    (leftSort : (g.label route.first.1).sort=.op left)
    (rightSort : (g.label route.last.1).sort=.op right)
    (leftPrincipal : IsPrincipal (g:=g) route.first)
    (rightPrincipal : IsPrincipal (g:=g) route.last)
    (fit : OrientedControlSchemaFits selected left right
      (g.label route.first.1).index (g.label route.last.1).index) :
    let oriented := orientSchemaCorridor route selected.2
    (g.label oriented.first.1=label selected.1.active selected.1.low ∧
      HEq oriented.first.2 (Sum.inl () : Port (.op selected.1.active))) ∧
    (g.label oriented.last.1=label selected.1.passive selected.1.high ∧
      HEq oriented.last.2 (Sum.inl () : Port (.op selected.1.passive))) := by
  obtain ⟨schema,direction⟩ := selected
  cases direction with
  | false =>
    obtain ⟨active,passive,low,high⟩ := fit
    exact ⟨endpointFits route.first _ _ (leftSort.trans (congrArg Kind.op active.symm))
      low.symm leftPrincipal, endpointFits route.last _ _
      (rightSort.trans (congrArg Kind.op passive.symm)) high.symm rightPrincipal⟩
  | true =>
    obtain ⟨active,passive,low,high⟩ := fit
    exact ⟨endpointFits route.last _ _ (rightSort.trans (congrArg Kind.op active.symm))
      low.symm rightPrincipal, endpointFits route.first _ _
      (leftSort.trans (congrArg Kind.op passive.symm)) high.symm leftPrincipal⟩

/-- Build the recipe directly from the route and the computed table entry.
All carrier data come from that route and the supplied equality algorithms. -/
def executableOrientedSchemaRecipe [DecidableEq N] [DecidableEq W]
    (route : TransparentCorridor g) (selected : Schema × Bool) (flow : Nonempty (FlowBalance g boundary))
    (left right : Op)
    (leftSort : (g.label route.first.1).sort=.op left)
    (rightSort : (g.label route.last.1).sort=.op right)
    (leftPrincipal : IsPrincipal (g:=g) route.first)
    (rightPrincipal : IsPrincipal (g:=g) route.last)
    (fit : OrientedControlSchemaFits selected left right
      (g.label route.first.1).index (g.label route.last.1).index) :
    Readback.ExplicitRewriteRecipe (Readback.ExecutableNet.ofNet g) selected.1 := by
  let oriented := orientSchemaCorridor route selected.2
  have ends := orientedEndpoints route selected left right leftSort rightSort
    leftPrincipal rightPrincipal fit
  have distinct : oriented.first.1 ≠ oriented.last.1 := by
    obtain ⟨witness⟩ := flow
    exact oriented.principal_nodes_distinct witness selected.1
      oriented.first.1 oriented.last.1 ends.1.1 ends.2.1
      oriented.first.2 oriented.last.2 ends.1.2 ends.2.2 rfl rfl
  exact Readback.explicitRecipeOfPresentation
    (PhysicalCorridorPresentation.executableOfCorridor g selected.1 oriented
      oriented.first.1 oriented.last.1 distinct ends.1.1 ends.2.1
      oriented.first.2 oriented.last.2 ends.1.2 ends.2.2 rfl rfl)
end
end Lamping.AG.ExposureScheduling
