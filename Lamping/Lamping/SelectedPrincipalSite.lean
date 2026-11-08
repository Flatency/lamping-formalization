import Lamping.Lamping.PrincipalSiteRealization
import Lamping.Graph.CarrierRenaming
namespace Lamping.AG
open Graph

private def emptyExtension (W : Type) : Bij (W ⊕ Empty) W where
  toFun := fun x => match x with | .inl w => w | .inr v => nomatch v
  invFun := Sum.inl
  left_inv := by rintro (w | v); rfl; exact nomatch v
  right_inv _ := rfl

section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]

/-- A genuine schema-labelled direct principal connection in any finite net
produces an actual GraphStep. Neither a special ambient carrier nor a Site
witness nor graph correctness is assumed by the caller. -/
theorem selected_principal_graph_step (g : Net signature N B W) (schema : Schema)
    (active passive : N) (different : active≠passive)
    (activeLabel : g.label active=label schema.active schema.low)
    (passiveLabel : g.label passive=label schema.passive schema.high)
    (p : Port (g.label active).sort) (q : Port (g.label passive).sort)
    (activePrincipal : HEq p (Sum.inl () : Port (.op schema.active)))
    (passivePrincipal : HEq q (Sum.inl () : Port (.op schema.passive)))
    (connection : g.wire (.inl ⟨active,p⟩)=.inl ⟨passive,q⟩) :
    ∃ target : ActualNet B,GraphStep schema (ActualNet.ofNet g) target := by
  let K := RemainingNodes active passive
  letI : FiniteNames K := remainingNodesFinite active passive
  let kept : K → Label signature := fun n => g.label n.val
  let nodes := splitSelectedNodes active passive different
  let vertices := emptyExtension W
  have compatible : ∀ n,g.label (nodes n)=ambientLabel schema kept n := by
    rintro (n | (tag | tag))
    · rfl
    · cases tag; exact activeLabel
    · cases tag; exact passiveLabel
  let fresh := g.reindex (ambientLabel schema kept) nodes vertices compatible
  let iso := g.reindexIso (ambientLabel schema kept) nodes vertices compatible
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
  have leftEnd : iso.ends (.inl left)=.inl ⟨active,p⟩ :=
    (iso.node_end left).trans (congrArg Sum.inl leftPort)
  have rightEnd : iso.ends (.inl right)=.inl ⟨passive,q⟩ :=
    (iso.node_end right).trans (congrArg Sum.inl rightPort)
  have actual : fresh.wire (.inl left)=.inl right := by
    apply iso.ends.injective
    rw [iso.wiring,leftEnd,connection,rightEnd]
  let site : Site schema kept (B:=B) (W:=W) := {
    wire := fresh.wire
    principal := actual }
  exact ⟨ActualNet.ofNet site.pathSite.reduce,site.graph_step.iso_source iso.symm⟩

/-- GraphNormal excludes every such actual direct schema interaction. -/
theorem GraphNormal.no_selected_principal {g : ActualNet B} (normal : GraphNormal g)
    (schema : Schema) (active passive : g.Node) (different : active≠passive)
    (activeLabel : g.net.label active=label schema.active schema.low)
    (passiveLabel : g.net.label passive=label schema.passive schema.high)
    (p : Port (g.net.label active).sort) (q : Port (g.net.label passive).sort)
    (activePrincipal : HEq p (Sum.inl () : Port (.op schema.active)))
    (passivePrincipal : HEq q (Sum.inl () : Port (.op schema.passive)))
    (connection : g.net.wire (.inl ⟨active,p⟩)=.inl ⟨passive,q⟩) : False := by
  obtain ⟨target,step⟩ := selected_principal_graph_step g.net schema active passive different
    activeLabel passiveLabel p q activePrincipal passivePrincipal connection
  exact normal schema target step
end
end Lamping.AG
