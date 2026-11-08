import Lamping.Lamping.CancellationFrontGeometry
import Lamping.Lamping.BetaPrincipalInternal
import Lamping.Lamping.BetaResidualOccurrences
namespace Lamping.AG
open Graph
section
variable {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K → Label signature} {i : Nat}
variable (site : PathSite (.beta i) kept (B:=B) (W:=W) (V:=V))
local notation "cut" => cutFragment site.net (pathPartition (Schema.beta i) V) site.closed

/-- Reuse the general fixed-front wire relation for this actual beta.
The front geometry lemmas are schema-parametric despite their historical
cancellation names; no cancellation-only token or untypedness lemma is used. -/
theorem BetaPathResidual.canonical {edge : BetaEdge site.net}
    (geometry : SiteBetaGeometry site edge) {raw old}
    (relation : BetaPathResidual site edge raw old) :
    CanonicalWireResidual cut (Schema.beta i).right.net site.net site.outsideEnd
      (site.cancellation_canonical_fronts edge.principal) raw old := by
  induction relation with
  | single e => exact .single e
  | outside rest ih => exact .outside ih
  | @context e tail oldTail arrival rest ih =>
    have literal := cancellation_fronts_literal site (geometry.principal_presentation site) (Sum.inl false)
    have entrance : (cut).wire (.inr (.inl (.inr (Sum.inl false))))=e := by
      rw [←arrival,Pairing.involutive]
    have frontEq : site.cancellation_canonical_fronts edge.principal (Sum.inl false)=
        site.outsideEnd e::edge.principal := by
      simpa only [entrance,cancellationFrontRoute,SiteBetaGeometry.principal_presentation] using literal
    have actual := CanonicalWireResidual.through
      (c:=cut) (r:=(Schema.beta i).right.net) (g:=site.net) (embed:=site.outsideEnd)
      (fronts:=site.cancellation_canonical_fronts edge.principal) (f:=Sum.inl false)
      (by rw [frontEq];rfl) ih
    simpa only [frontEq,List.cons_append] using actual
  | @binding e tail oldTail arrival rest ih =>
    have literal := cancellation_fronts_literal site (geometry.principal_presentation site) (Sum.inr false)
    have entrance : (cut).wire (.inr (.inl (.inr (Sum.inr false))))=e := by
      rw [←arrival,Pairing.involutive]
    have frontEq : site.cancellation_canonical_fronts edge.principal (Sum.inr false)=
        site.outsideEnd e::edge.reverseRoute := by
      simpa only [entrance,cancellationFrontRoute,SiteBetaGeometry.principal_presentation,
        BetaEdge.reverseRoute,reverseEdges] using literal
    have actual := CanonicalWireResidual.through
      (c:=cut) (r:=(Schema.beta i).right.net) (g:=site.net) (embed:=site.outsideEnd)
      (fronts:=site.cancellation_canonical_fronts edge.principal) (f:=Sum.inr false)
      (by rw [frontEq];rfl) ih
    simpa only [frontEq,List.cons_append] using actual

/-- The actual internal principal/reverse routes delimit the fixed fronts. -/
theorem BetaPathResidual.target_unique {edge : BetaEdge site.net}
    (geometry : SiteBetaGeometry site edge) {left right oldLeft oldRight}
    (first : BetaPathResidual site edge left oldLeft)
    (second : BetaPathResidual site edge right oldRight) (same : oldLeft=oldRight) : left=right := by
  let principal := geometry.principal_presentation site
  exact CanonicalWireResidual.target_unique cut (Schema.beta i).right.net site.net site.outsideEnd
    (site.cancellation_canonical_fronts edge.principal) site.outsideEnd_injective
    (fun f=>by
      obtain ⟨inside,tail,equal,disjoint⟩ := cancellation_front_internal_delimiter site principal f
      exact ⟨_,inside,tail,equal,disjoint⟩)
    (fun f h same=>cancellation_front_heads_injective site principal same)
    (first.canonical site geometry) (second.canonical site geometry) same

/-- The same literal reduced residual has one literal old ancestor. -/
theorem BetaPathResidual.source_unique {edge : BetaEdge site.net}
    (geometry : SiteBetaGeometry site edge) {raw left right}
    (first : BetaPathResidual site edge raw left)
    (second : BetaPathResidual site edge raw right) : left=right :=
  CanonicalWireResidual.source_unique cut (Schema.beta i).right.net site.net site.outsideEnd
    (site.cancellation_canonical_fronts edge.principal)
    (first.canonical site geometry) (second.canonical site geometry)

/-- Every outside pivot is disjoint from both actual inserted internal
routes. The specified old ordinal is preserved, including repeated pivots. -/
theorem BetaPathResidual.split_outside {edge : BetaEdge site.net}
    (geometry : SiteBetaGeometry site edge) {raw old}
    (relation : BetaPathResidual site edge raw old)
    (pivot : Endpoint cut) (before after : List (Endpoint site.net))
    (split : old=before++site.outsideEnd pivot::after) :
    ∃ cutAt : BetaResidualOccurrence site edge raw old pivot before.length,
      cutAt.oldBefore=before ∧cutAt.oldAfter=after := by
  apply relation.split_decomposition site
  · intro member
    obtain ⟨index,inside⟩ := geometry.principal_internal site _ member
    exact site.internal_outside_ne index pivot inside.symm
  · intro member
    obtain ⟨index,inside⟩ := geometry.reverse_internal site _ member
    exact site.internal_outside_ne index pivot inside.symm
  · exact split

/-- A supplied actual parent residual and the two literal prefix equations
force the specified new piece, rather than merely giving some outside cut.
Constructing these parent/whole residuals for a syntax selector is separate. -/
theorem BetaPathResidual.cut_at_actual_prefix {edge : BetaEdge site.net}
    (geometry : SiteBetaGeometry site edge) {raw old parentRaw parentOld newPiece oldPiece : List _}
    (whole : BetaPathResidual site edge raw old)
    (parent : BetaPathResidual site edge parentRaw parentOld)
    (oldSplit : old=parentOld++oldPiece) (rawSplit : raw=parentRaw++newPiece)
    (pivot : Endpoint cut) (parentLast : parentOld.getLast?=some (site.outsideEnd pivot)) :
    BetaPathResidual site edge (Sum.inl pivot::newPiece) (site.outsideEnd pivot::oldPiece) := by
  obtain ⟨before,parentSplit⟩ := List.getLast?_eq_some_iff.mp parentLast
  have oldCut : old=before++site.outsideEnd pivot::oldPiece := by
    rw [oldSplit,parentSplit,List.append_assoc];rfl
  obtain ⟨cutAt,beforeEq,afterEq⟩ := whole.split_outside site geometry pivot before oldPiece oldCut
  have prefixRelation := cutAt.prefixResidual
  have suffix := cutAt.suffixResidual
  rw [beforeEq] at prefixRelation
  rw [afterEq] at suffix
  have prefixEq := prefixRelation.target_unique site geometry parent parentSplit.symm
  have reassembled : raw=parentRaw++cutAt.after := by
    calc
      raw=cutAt.before++Sum.inl pivot::cutAt.after := cutAt.raw_eq
      _=(cutAt.before++[Sum.inl pivot])++cutAt.after := by rw [List.append_assoc];rfl
      _=parentRaw++cutAt.after := congrArg (·++cutAt.after) prefixEq
  have tailEq : newPiece=cutAt.after := List.append_cancel_left (rawSplit.symm.trans reassembled)
  simpa only [←tailEq] using suffix

/-- At a real retained-node arrival the leading overlap cannot be a beta
reconnection. Inverting that ordinary outside step gives the exact piece
residual. A nonempty old piece excludes the singleton/empty-suffix case. -/
theorem BetaPathResidual.cut_at_kept_prefix {edge : BetaEdge site.net}
    (geometry : SiteBetaGeometry site edge) {raw old parentRaw parentOld newPiece oldPiece : List _}
    (whole : BetaPathResidual site edge raw old)
    (parent : BetaPathResidual site edge parentRaw parentOld)
    (oldSplit : old=parentOld++oldPiece) (rawSplit : raw=parentRaw++newPiece)
    (node : K) (port : Port (kept node).sort)
    (parentLast : parentOld.getLast?=some (site.net.wire (.inl ⟨.inl node,port⟩)))
    (nonempty : oldPiece≠[]) : BetaPathResidual site edge newPiece oldPiece := by
  let pivot : Endpoint cut := (cut).wire (.inl ⟨node,port⟩)
  have outside : site.outsideEnd pivot=site.net.wire (.inl ⟨.inl node,port⟩) :=
    (site.outsideEnd_wire (.inl ⟨node,port⟩)).symm
  have overlap := whole.cut_at_actual_prefix site geometry parent oldSplit rawSplit pivot
    (parentLast.trans (congrArg some outside.symm))
  cases overlap with
  | single e => exact False.elim (nonempty rfl)
  | outside rest => exact rest
  | context arrival rest =>
    change (cut).wire ((cut).wire (.inl ⟨node,port⟩))=_ at arrival
    rw [Pairing.involutive] at arrival
    cases arrival
  | binding arrival rest =>
    change (cut).wire ((cut).wire (.inl ⟨node,port⟩))=_ at arrival
    rw [Pairing.involutive] at arrival
    cases arrival
end
end Lamping.AG
