import Lamping.Lamping.FirstNodeDecomposition
import Lamping.Lamping.PhysicalInteractionExistence
import Lamping.Lamping.BalancedPrincipalRoutes
namespace Lamping.AG
open Graph
section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable {g : Net signature N B W} {depths : B → Int} {directions : B → Bool}

/-- The all-transparent case of a genuine syntax-redex connection is a real
graph beta step. Its index equality is derived from actual geometric balance.
No arbitrary proper-path input, Matches preservation or NF premise is used. -/
theorem RedexConnection.transparent_graph_step (connection : RedexConnection g)
    (balance : LevelBalance g depths) (flow : FlowBalance g directions)
    (transparent : TransparentTurns (g:=g) connection.edges) :
    ∃ target,GraphStep (.beta connection.appIndex) (ActualNet.ofNet g) target := by
  have equal := balance.proper_principal_route_indices connection.edges connection.app connection.lam
    connection.appPort connection.lamPort .app .lam connection.appIndex connection.lamIndex
    connection.appLabel connection.lamLabel (Or.inl rfl) (Or.inr rfl)
    connection.appPrincipal connection.lamPrincipal connection.start connection.finish transparent
  let route : TransparentCorridor g := {
    first := ⟨connection.app,connection.appPort⟩,
    last := ⟨connection.lam,connection.lamPort⟩,
    edges := connection.edges,start := connection.start,finish := connection.finish,
    transparent := transparent }
  exact beta_corridor_graph_step flow route connection.app connection.lam connection.appLabel
    (by rw [equal]; exact connection.lamLabel) connection.appPort connection.lamPort
    connection.appPrincipal connection.lamPrincipal rfl rfl
end
end Lamping.AG
