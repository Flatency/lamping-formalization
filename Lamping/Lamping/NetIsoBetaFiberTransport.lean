import Lamping.Lamping.NetIsoPathTransport
import Lamping.Lamping.MatchingBetaFiber
import Lamping.Lamping.PhysicalCorridorPresentation
namespace Lamping.Graph
open AG Lambda
section
variable {N M B W V : Type} [FiniteNames N] [FiniteNames M] [FiniteNames B]
  [FiniteNames W] [FiniteNames V]
variable {g : Net signature N B W} {h : Net signature M B V} (iso : NetIso g h)

/-- Rename the supplied actual connection, retaining every literal segment,
its source/passive indices, and its zero syntax suffix word. -/
def NetIso.redexConnection (connection : RedexConnection g) : RedexConnection h where
  app := iso.nodes connection.app
  lam := iso.nodes connection.lam
  appPort := iso.imagePort _ connection.appPort
  lamPort := iso.imagePort _ connection.lamPort
  appIndex := connection.appIndex
  lamIndex := connection.lamIndex
  appLabel := (iso.labels _).trans connection.appLabel
  lamLabel := (iso.labels _).trans connection.lamLabel
  appPrincipal := (iso.imagePort_heq _ _).trans connection.appPrincipal
  lamPrincipal := (iso.imagePort_heq _ _).trans connection.lamPrincipal
  edges := connection.edges.map iso.ends
  proper := iso.forwardProper connection.proper
  start := by
    rw [List.head?_map,connection.start]
    simp only [Option.map_some,iso.node_end_image]
  finish := by
    rw [List.getLast?_map,connection.finish]
    simp only [Option.map_some,iso.wiring,iso.node_end_image]
  emptyWord := (iso.accessWord _).trans connection.emptyWord

/-- The SAME syntax redex retains its actual parent/child accesses and split.
No Matches or selected endpoints are supplied as map correctness fields. -/
def NetIso.actualRedexAccess {root : B} {t : Term} {redex : RedexOcc t}
    (source : ActualRedexAccess g root redex) : ActualRedexAccess h root redex where
  connection := iso.redexConnection source.connection
  parent := iso.rootAccessBij root source.parent
  child := iso.rootAccessBij root source.child
  ctx := iso.imagePort source.connection.app source.ctx
  contextPrincipal := (iso.imagePort_heq _ _).trans source.contextPrincipal
  parentWord := (iso.accessWord _).trans source.parentWord
  childWord := (iso.accessWord _).trans source.childWord
  parentFinish := by
    change (source.parent.val.map iso.ends).getLast?=_
    rw [List.getLast?_map,source.parentFinish]
    simp only [Option.map_some,iso.wiring,iso.node_end_image,NetIso.redexConnection]
  split := by
    change source.child.val.map iso.ends=source.parent.val.map iso.ends++source.connection.edges.map iso.ends
    rw [source.split,List.map_append]

/-- Boundary-fixing renaming preserves actual source occurrence membership
at the SAME physical pair, without a semantic matching hypothesis. -/
theorem NetIso.atPhysicalBeta_iff (root : B) (t : Term) (app lam : N) (p : Path) :
    AtPhysicalBeta h root t (iso.nodes app) (iso.nodes lam) p ↔AtPhysicalBeta g root t app lam p := by
  constructor
  · rintro ⟨redex,source,path,atApp,atLam⟩
    refine ⟨redex,iso.symm.actualRedexAccess source,path,?_,?_⟩
    · change iso.nodes.invFun source.connection.app=app
      rw [atApp,iso.nodes.left_inv]
    · change iso.nodes.invFun source.connection.lam=lam
      rw [atLam,iso.nodes.left_inv]
  · rintro ⟨redex,source,path,atApp,atLam⟩
    exact ⟨redex,iso.actualRedexAccess source,path,congrArg iso.nodes atApp,congrArg iso.nodes atLam⟩

/-- The literal finite filter, including its order, is unchanged. Thus old
names, selected marks and actual schedules are shared across reindexing. -/
theorem NetIso.physicalBetaFiberPaths_eq (root : B) (t : Term) (app lam : N) :
    physicalBetaFiberPaths h root t (iso.nodes app) (iso.nodes lam)=physicalBetaFiberPaths g root t app lam := by
  classical
  have tests : physicalBetaTest h root t (iso.nodes app) (iso.nodes lam)=physicalBetaTest g root t app lam := by
    funext p
    simp only [physicalBetaTest,iso.atPhysicalBeta_iff]
  simp only [physicalBetaFiberPaths,tests]
end
end Lamping.Graph

namespace Lamping.AG
open Graph Lambda
section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable {g : Net signature N B W} {app lam : N} {i : Nat}
variable {p : Port (g.label app).sort} {q : Port (g.label lam).sort}

/-- Exact principal-port provenance makes the canonical site's finite syntax
fiber the original selected physical pair's SAME ordered source fiber. -/
theorem PhysicalCorridorPresentation.betaSyntaxFiber_eq
    (presentation : PhysicalCorridorPresentation g (.beta i) app lam p q)
    (root : B) (t : Term) :
    presentation.site.betaSyntaxFiber root t=physicalBetaFiberPaths g root t app lam := by
  have activeNode : presentation.sourceIso.nodes app=.inr (.inl ()) :=
    (presentation.sourceIso.port_node ⟨app,p⟩).symm.trans
      (congrArg Sigma.fst presentation.active_port)
  have passiveNode : presentation.sourceIso.nodes lam=.inr (.inr ()) :=
    (presentation.sourceIso.port_node ⟨lam,q⟩).symm.trans
      (congrArg Sigma.fst presentation.passive_port)
  unfold PathSite.betaSyntaxFiber
  rw [←activeNode,←passiveNode]
  exact presentation.sourceIso.physicalBetaFiberPaths_eq root t app lam
end
end Lamping.AG
