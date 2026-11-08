import Lamping.Lamping.PhysicalCorridorPresentation
import Lamping.Lamping.ExecutableNetTransport
import Lamping.Graph.ExecutableCarrierRenaming
import Lamping.Graph.ExecutableFinitePartition

namespace Lamping.AG
open Graph
section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable {g : Net signature N B W}

private def wireHit (w : W) : Endpoint g → Prop
  | .inr (.inr (v, _)) => w = v
  | _ => False

private def wireHitDecidable [DecidableEq W] (w : W) (e : Endpoint g) :
    Decidable (wireHit w e) := by
  cases e with
  | inl p => exact .isFalse (fun h => h)
  | inr e =>
    cases e with
    | inl b => exact .isFalse (fun h => h)
    | inr wd => exact inferInstanceAs (Decidable (w = wd.1))

private theorem wireHit_iff (w : W) (e : Endpoint g) :
    wireHit w e ↔ ∃ d, e = .inr (.inr (w,d)) := by
  cases e with
  | inl p => simp [wireHit]
  | inr e =>
    cases e with
    | inl b => simp [wireHit]
    | inr wd =>
      rcases wd with ⟨v,d⟩
      constructor
      · intro same
        change w = v at same
        subst v
        exact ⟨d,rfl⟩
      · rintro ⟨b,same⟩
        exact (congrArg Prod.fst (Sum.inr.inj (Sum.inr.inj same))).symm

/-- Scan the actual route using wire equality, without endpoint or boundary equality. -/
def TransparentCorridor.vertexDecidable [DecidableEq W]
    (route : TransparentCorridor g) : DecidablePred route.vertex := fun w => by
  letI : DecidablePred (wireHit (g:=g) w) := wireHitDecidable w
  let scan : Decidable (∃ e ∈ route.edges, wireHit (g:=g) w e) := inferInstance
  have equivalent : (∃ e ∈ route.edges, wireHit (g:=g) w e) ↔ route.vertex w := by
    constructor
    · rintro ⟨e,member,hit⟩
      obtain ⟨d,same⟩ := (wireHit_iff w e).mp hit
      subst e
      exact ⟨d,member⟩
    · rintro ⟨d,member⟩
      exact ⟨.inr (.inr (w,d)),member,(wireHit_iff w _).mpr ⟨d,rfl⟩⟩
  cases scan with
  | isTrue found => exact .isTrue (equivalent.mp found)
  | isFalse absent => exact .isFalse (fun found => absent (equivalent.mpr found))
end

section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable [DecidableEq N] [DecidableEq W]

def PhysicalCorridorPresentation.executableOfCorridor (g : Net signature N B W) (schema : Schema)
    (route : TransparentCorridor g) (active passive : N) (different : active≠passive)
    (activeLabel : g.label active=label schema.active schema.low)
    (passiveLabel : g.label passive=label schema.passive schema.high)
    (p : Port (g.label active).sort) (q : Port (g.label passive).sort)
    (activePrincipal : HEq p (Sum.inl () : Port (.op schema.active)))
    (passivePrincipal : HEq q (Sum.inl () : Port (.op schema.passive)))
    (first : route.first=⟨active,p⟩) (last : route.last=⟨passive,q⟩) :
    PhysicalCorridorPresentation g schema active passive p q := by
  letI : DecidablePred route.vertex := route.vertexDecidable
  let K := RemainingNodes active passive
  let Outside := {w : W // ¬route.vertex w}
  let Inside := {w : W // route.vertex w}
  letI : FiniteNames K := Executable.remainingNodesFinite active passive
  letI : FiniteNames Outside := Executable.finiteSubtype (fun w => ¬route.vertex w)
  letI : FiniteNames Inside := Executable.finiteSubtype route.vertex
  let kept : K → Label signature := fun n => g.label n.val
  let nodes := Executable.splitSelectedNodes active passive different
  let vertices := Executable.partitionNames route.vertex
  have compatible : ∀ n,g.label (nodes n)=ambientLabel schema kept n := by
    rintro (n | (tag | tag))
    · rfl
    · cases tag; exact activeLabel
    · cases tag; exact passiveLabel
  let fresh := Executable.reindex g (ambientLabel schema kept) nodes vertices compatible
  let iso := Executable.reindexIso g (ambientLabel schema kept) nodes vertices compatible
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
end

namespace Readback
section
variable {B : Type} [FiniteNames B] {source : ExecutableNet B} {schema : Schema}
variable {active passive : source.graph.Node}
variable {p : Port (source.graph.net.label active).sort}
variable {q : Port (source.graph.net.label passive).sort}

/-- Direct record assembly from the same actual presentation. -/
def explicitRecipeOfPresentation
    (presentation : PhysicalCorridorPresentation source.graph.net schema active passive p q) :
    ExplicitRewriteRecipe source schema where
  Kept := presentation.Kept
  OutsideWire := presentation.Outside
  InternalWire := presentation.Inside
  keptFinite := presentation.keptFinite
  outsideFinite := presentation.outsideFinite
  internalFinite := presentation.insideFinite
  kept := presentation.kept
  site := presentation.site
  sourceIso := presentation.sourceIso

theorem explicitRecipeOfPresentation_ports
    (presentation : PhysicalCorridorPresentation source.graph.net schema active passive p q) :
    (explicitRecipeOfPresentation presentation).sourceIso.ports ⟨active,p⟩ = ⟨.inr (.inl ()),.inl ()⟩ ∧
    (explicitRecipeOfPresentation presentation).sourceIso.ports ⟨passive,q⟩ = ⟨.inr (.inr ()),.inl ()⟩ :=
  ⟨presentation.active_port,presentation.passive_port⟩
end
end Readback
end Lamping.AG

