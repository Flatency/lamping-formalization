import Lamping.Lamping.BetaDetourReflection
import Lamping.Lamping.BetaDetourCoherence
import Lamping.Lamping.TypedDetourRelabelling
namespace Lamping.AG
open Graph
section
variable {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K → Label signature} {i : Nat}
variable (site : PathSite (.beta i) kept (B:=B) (W:=W) (V:=V))

/-- Every given assignment on an actual reduced rooted path has a coherently
generated old ancestor. This transports genuine source I/Transparency through
the finite paired-block construction; neither generation nor a shell-transfer
certificate is assumed of the target path. -/
theorem PathSite.beta_root_coherent_ancestor {boundary : B → Bool}
    (flow : FlowBalance site.net boundary) (root : B) (rootPolarity : boundary root=true)
    (independence : Independence site.net root) (transparency : Transparency site.net root)
    {es : List (Endpoint site.reduce)} {input output : Context}
    (labels : Labelling site.reduce es input output) (rooted : es.head?=some (.inr (.inl root)))
    (last : Endpoint (cutFragment site.net (pathPartition (.beta i) V) site.closed))
    (finish : es.getLast?=some (AG.plugLeft _ _ last)) :
    ∃ (edge : BetaEdge site.net) (old : List (Endpoint site.net)),
      SiteBetaGeometry site edge ∧
      BetaPathResidual site edge (es.map (plugEnd _ _).invFun) old ∧
      CoherentExpandedCore site.net root old input output ∧
      old.head?=some (.inr (.inl root)) ∧ old.getLast?=some (site.outsideEnd last) := by
  obtain ⟨edge,old,geometry,relation,oldLabels,first,endAt⟩ :=
    site.beta_root_ancestor flow root rootPolarity labels rooted last finish
  obtain ⟨count,stream⟩ := relation.detour_blocks site geometry (labels.plug_decomposition _ _)
  exact ⟨edge,old,geometry,relation,stream.coherent flow rootPolarity independence transparency first,first,endAt⟩

/-- Select the actual literal ancestor once, preserving its given assignment,
then reconstruct coherent labels on that SAME ancestor for every root input.
The terminal role is checked at the actual old outside endpoint; converting
a reduced typed endpoint to this role is a separate geometric transport. -/
theorem PathSite.beta_root_typed_uniform_ancestor {boundary : B → Bool}
    (flow : FlowBalance site.net boundary) (root : B) (rootPolarity : boundary root=true)
    (invariants : OrdinaryPathInvariants site.net root)
    {es : List (Endpoint site.reduce)} {input output : Context}
    (labels : Labelling site.reduce es input output) (rooted : es.head?=some (.inr (.inl root)))
    (last : Endpoint (cutFragment site.net (pathPartition (.beta i) V) site.closed))
    (finish : es.getLast?=some (AG.plugLeft _ _ last))
    (role : ProperRole) (level : Nat)
    (atTerminal : AtProperRole site.net root (site.net.wire (site.outsideEnd last)) role level)
    (incoming : role.incoming) :
    ∃ (edge : BetaEdge site.net) (old : List (Endpoint site.net)),
      SiteBetaGeometry site edge ∧
      BetaPathResidual site edge (es.map (plugEnd _ _).invFun) old ∧
      CoherentExpandedCore site.net root old input output ∧
      old.head?=some (.inr (.inl root)) ∧ old.getLast?=some (site.outsideEnd last) ∧
      ∀ requested : Context, ∃ result,CoherentExpandedCore site.net root old requested result := by
  obtain ⟨edge,old,geometry,relation,oldLabels,first,endAt⟩ :=
    site.beta_root_ancestor flow root rootPolarity labels rooted last finish
  obtain ⟨count,stream⟩ := relation.detour_blocks site geometry (labels.plug_decomposition _ _)
  refine ⟨edge,old,geometry,relation,
    stream.coherent flow rootPolarity invariants.independence invariants.transparency first,
    first,endAt,?_⟩
  exact stream.typed_root_inputs flow rootPolarity invariants first
    (site.net.wire (site.outsideEnd last)) role level
    (by simpa only [Pairing.involutive] using endAt) atTerminal incoming
end
end Lamping.AG
