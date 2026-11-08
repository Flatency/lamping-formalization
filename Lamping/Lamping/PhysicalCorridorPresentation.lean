import Lamping.Lamping.PrincipalCorridorReach
import Lamping.Lamping.CorridorTransport
import Lamping.Graph.FinitePartition
import Lamping.Graph.SelectedNodes
import Lamping.Graph.CarrierRenaming
namespace Lamping.AG
open Graph
section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]

/-- A real corridor presentation retains the exact two selected physical
principal ports through its boundary-fixing source isomorphism. Finite
carriers and the PathSite are constructed, not assumed rewrite witnesses. -/
structure PhysicalCorridorPresentation (g : Net signature N B W) (schema : Schema)
    (active passive : N) (p : Port (g.label active).sort) (q : Port (g.label passive).sort) where
  Kept : Type
  Outside : Type
  Inside : Type
  [keptFinite : FiniteNames Kept]
  [outsideFinite : FiniteNames Outside]
  [insideFinite : FiniteNames Inside]
  kept : Kept → Label signature
  site : PathSite schema kept (B:=B) (W:=Outside) (V:=Inside)
  sourceIso : NetIso g site.net
  active_port : sourceIso.ports ⟨active,p⟩=⟨.inr (.inl ()),.inl ()⟩
  passive_port : sourceIso.ports ⟨passive,q⟩=⟨.inr (.inr ()),.inl ()⟩
attribute [instance] PhysicalCorridorPresentation.keptFinite
  PhysicalCorridorPresentation.outsideFinite PhysicalCorridorPresentation.insideFinite

/-- Forgetting the retained port equations recovers the original actual
schema step on the same constructed PathSite. -/
theorem PhysicalCorridorPresentation.graph_step
    {g : Net signature N B W} {schema : Schema} {active passive : N}
    {p : Port (g.label active).sort} {q : Port (g.label passive).sort}
    (presentation : PhysicalCorridorPresentation g schema active passive p q) :
    GraphStep schema (ActualNet.ofNet g) (ActualNet.ofNet presentation.site.reduce) :=
  .atSite presentation.kept presentation.site presentation.sourceIso (.refl _)

/-- The existing selected-node/selected-vertex reindex construction, with
its two actual principal-port equations retained rather than erased. -/
noncomputable def PhysicalCorridorPresentation.of_corridor (g : Net signature N B W) (schema : Schema)
    (route : TransparentCorridor g) (active passive : N) (different : active≠passive)
    (activeLabel : g.label active=label schema.active schema.low)
    (passiveLabel : g.label passive=label schema.passive schema.high)
    (p : Port (g.label active).sort) (q : Port (g.label passive).sort)
    (activePrincipal : HEq p (Sum.inl () : Port (.op schema.active)))
    (passivePrincipal : HEq q (Sum.inl () : Port (.op schema.passive)))
    (first : route.first=⟨active,p⟩) (last : route.last=⟨passive,q⟩) :
    PhysicalCorridorPresentation g schema active passive p q := by
  let K := RemainingNodes active passive
  let Outside := {w : W // ¬route.vertex w}
  let Inside := {w : W // route.vertex w}
  letI : FiniteNames K := remainingNodesFinite active passive
  letI : FiniteNames Outside := Graph.finiteSubtype (fun w => ¬route.vertex w)
  letI : FiniteNames Inside := Graph.finiteSubtype route.vertex
  let kept : K → Label signature := fun n => g.label n.val
  let nodes := splitSelectedNodes active passive different
  let vertices := partitionNames route.vertex
  have compatible : ∀ n,g.label (nodes n)=ambientLabel schema kept n := by
    rintro (n | (tag | tag))
    · rfl
    · cases tag; exact activeLabel
    · cases tag; exact passiveLabel
  let fresh := g.reindex (ambientLabel schema kept) nodes vertices compatible
  let iso := g.reindexIso (ambientLabel schema kept) nodes vertices compatible
  let mapped := route.map iso.symm
  let left : NodePort signature (K ⊕ (Unit ⊕ Unit)) (ambientLabel schema kept) :=
    ⟨.inr (.inl ()),.inl ()⟩
  let right : NodePort signature (K ⊕ (Unit ⊕ Unit)) (ambientLabel schema kept) :=
    ⟨.inr (.inr ()),.inl ()⟩
  have leftPort : iso.ports left=⟨active,p⟩ := by
    apply Sigma.ext (iso.port_node left)
    exact (iso.port_role left).trans activePrincipal.symm
  have rightPort : iso.ports right=⟨passive,q⟩ := by
    apply Sigma.ext (iso.port_node right)
    exact (iso.port_role right).trans passivePrincipal.symm
  have firstMap : mapped.first=left := by
    change iso.ports.invFun route.first=left
    rw [first,←leftPort,iso.ports.left_inv]
  have lastMap : mapped.last=right := by
    change iso.ports.invFun route.last=right
    rw [last,←rightPort,iso.ports.left_inv]
  have selected : ∀ w,mapped.vertex w ↔∃ v,w=.inr v := by
    intro w
    rw [TransparentCorridor.map_vertex_iff]
    change route.vertex (vertices w) ↔∃ v,w=.inr v
    cases w with
    | inl w =>
      constructor
      · intro occurs; exact False.elim (w.property occurs)
      · rintro ⟨v,impossible⟩; cases impossible
    | inr v =>
      constructor
      · intro _; exact ⟨v,rfl⟩
      · intro _; exact v.property
  let actual : SelectedCorridor schema kept (B:=B) (W:=Outside) (V:=Inside) := {
    wire := fresh.wire
    edges := mapped.edges
    start := by simpa only [firstMap] using mapped.start
    finish := by simpa only [lastMap] using mapped.finish
    transparent := mapped.transparent
    selectedVertices := selected }
  refine {
    Kept := K
    Outside := Outside
    Inside := Inside
    kept := kept
    site := actual.pathSite
    sourceIso := iso.symm
    active_port := ?_
    passive_port := ?_ }
  · change iso.ports.invFun ⟨active,p⟩=left
    rw [←leftPort,iso.ports.left_inv]
  · change iso.ports.invFun ⟨passive,q⟩=right
    rw [←rightPort,iso.ports.left_inv]


/-- The original existence interface, forgetting only the constructed record. -/
theorem physical_corridor_presentation (g : Net signature N B W) (schema : Schema)
    (route : TransparentCorridor g) (active passive : N) (different : active≠passive)
    (activeLabel : g.label active=label schema.active schema.low)
    (passiveLabel : g.label passive=label schema.passive schema.high)
    (p : Port (g.label active).sort) (q : Port (g.label passive).sort)
    (activePrincipal : HEq p (Sum.inl () : Port (.op schema.active)))
    (passivePrincipal : HEq q (Sum.inl () : Port (.op schema.passive)))
    (first : route.first=⟨active,p⟩) (last : route.last=⟨passive,q⟩) :
    Nonempty (PhysicalCorridorPresentation g schema active passive p q) :=
  ⟨PhysicalCorridorPresentation.of_corridor g schema route active passive different
    activeLabel passiveLabel p q activePrincipal passivePrincipal first last⟩

end
end Lamping.AG



