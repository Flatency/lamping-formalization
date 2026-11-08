-- CP84 SOURCE ONLY. No proof has been compiled; no axiom is declared here.
import Lamping.Checks.WrappedLambdaParent
import Lamping.Lamping.BetaCanonicalComparison
import Lamping.Lamping.BetaDetourReflection
import Lamping.Lamping.BetaDetourCoherence
import Lamping.Lamping.NetIsoInvariantTransport
import Lamping.Lamping.GraphFlowPreservation
import Lamping.Lamping.InitialFullIndependence
import Lamping.Lamping.InitialTransparency

namespace Lamping.Checks.ReturnedIdentityCopyResidual
noncomputable section
open AG Graph Lambda
open FunctionWrappedReachable WrappedLambdaParent

noncomputable abbrev cut := actualCut
noncomputable abbrev right := (Schema.beta 0).right.net

def rootCut : Endpoint cut := .inr (.inl (.inl (.inl ())))
def outerFunction : Endpoint cut := .inl ⟨outerKept, .inl ()⟩
def outerEnd : Endpoint cut := .inr (.inr (outerOutside, true))
def bodyFront : Endpoint cut := .inr (.inl (.inr (.inr true)))
def bodyEnd : Endpoint cut := .inr (.inr (oldBodyOutside, true))
def variablePrincipal : Endpoint cut := .inl ⟨croKept, .inl ()⟩
def bindingEnd : Endpoint cut := .inr (.inr (bindingOutside, false))
def argumentFront : Endpoint cut := .inr (.inl (.inr (.inl true)))
def argumentEnd : Endpoint cut := .inr (.inr (argumentOutside, true))

def rawQ : List (PlugSegment cut right) :=
  [.inl rootCut, .inl outerFunction, .inl outerEnd,
   .inr (.inr (.inl (.inl false))),
   .inl bodyFront, .inl bodyEnd, .inl variablePrincipal, .inl bindingEnd,
   .inr (.inr (.inl (.inr false))),
   .inl argumentFront, .inl argumentEnd]

def actualQ : List (Endpoint concrete.site.reduce) :=
  rawQ.map (plugEnd cut.label right.label)

def siteWord (edge : BetaEdge concrete.site.net) : List (Endpoint concrete.site.net) :=
  [concrete.site.outsideEnd rootCut,
   concrete.site.outsideEnd outerFunction,
   concrete.site.outsideEnd outerEnd] ++ edge.principal ++
  [concrete.site.outsideEnd bodyFront,
   concrete.site.outsideEnd bodyEnd,
   concrete.site.outsideEnd variablePrincipal,
   concrete.site.outsideEnd bindingEnd] ++ edge.reverseRoute ++
  [concrete.site.outsideEnd argumentFront,
   concrete.site.outsideEnd argumentEnd]

def identityLoop : List (Endpoint net) :=
  [.inl ⟨lam, lamBody⟩, .inr (.inr (oldBodyWire, true)),
   .inl ⟨oldCro, .inl ()⟩, .inr (.inr (bindingWire, false))]

def originalWord : List (Endpoint net) :=
  parentEdges ++ corridor.edges ++ identityLoop ++
    reverseEdges (g := net) corridor.edges ++
    [.inl ⟨app, appArg⟩, .inr (.inr (argumentWire, true))]

-- The edge, geometry, Q assignment, old assignment and path identity are OUTPUTS.
-- No caller-supplied old labels, old path equality, residual, geometry or IH.
private noncomputable def mapped := corridor.map concrete.sourceIso

private noncomputable def actualEdge : BetaEdge concrete.site.net where
  app := .inr (.inl ())
  lam := .inr (.inr ())
  index := 0
  appLabel := rfl
  lamLabel := rfl
  appFun := .inl ()
  appCtx := .inr false
  appArg := .inr true
  lamCtx := .inl ()
  lamBody := .inr true
  lamBind := .inr false
  appFun_role := HEq.rfl
  appCtx_role := HEq.rfl
  appArg_role := HEq.rfl
  lamCtx_role := HEq.rfl
  lamBody_role := HEq.rfl
  lamBind_role := HEq.rfl
  principal := mapped.edges
  principalStart := by
    have h := mapped.start
    change mapped.edges.head? = some (.inl (concrete.sourceIso.ports ⟨app,.inl ()⟩)) at h
    rw [concrete.active_port] at h
    exact h
  principalEnd := by
    have h := mapped.finish
    change mapped.edges.getLast? = some (concrete.site.net.wire (.inl (concrete.sourceIso.ports ⟨lam,.inl ()⟩))) at h
    rw [concrete.passive_port] at h
    exact h
  transparent := mapped.transparent

private theorem geometry : SiteBetaGeometry concrete.site actualEdge := ⟨rfl,rfl,rfl,rfl⟩

private theorem cut_root : cut.wire rootCut = .inl ⟨outerKept,appCtx⟩ := by
  apply concrete.site.outsideEnd_injective
  apply concrete.sourceIso.symm.ends.injective
  rw [←concrete.site.outsideEnd_wire,concrete.sourceIso.symm.wiring]
  rfl

private theorem cut_outer : cut.wire outerFunction = .inr (.inr (outerOutside,false)) := by
  apply concrete.site.outsideEnd_injective
  apply concrete.sourceIso.symm.ends.injective
  rw [←concrete.site.outsideEnd_wire,concrete.sourceIso.symm.wiring]
  rfl

private theorem cut_context : cut.wire outerEnd = .inr (.inl (.inr (.inl false))) := by
  apply concrete.site.outsideEnd_injective
  apply concrete.sourceIso.symm.ends.injective
  rw [←concrete.site.outsideEnd_wire,concrete.sourceIso.symm.wiring]
  rfl

private theorem cut_body : cut.wire bodyFront = .inr (.inr (oldBodyOutside,false)) := by
  apply concrete.site.outsideEnd_injective
  apply concrete.sourceIso.symm.ends.injective
  rw [←concrete.site.outsideEnd_wire,concrete.sourceIso.symm.wiring]
  rfl

private theorem cut_body_end : cut.wire bodyEnd = .inl ⟨croKept,.inr ()⟩ := by
  apply concrete.site.outsideEnd_injective
  apply concrete.sourceIso.symm.ends.injective
  rw [←concrete.site.outsideEnd_wire,concrete.sourceIso.symm.wiring]
  rfl

private theorem excursions (a : Context) : WireExcursions cut right rawQ a (InitialOffsets.croAt 0 a) := by
  apply WireExcursions.outside (b:=a)
  · rw [cut_root]
    exact LabelledTurn.node (g:=cut) outerKept appCtx (.inl ()) (.direct (.appFun a))
  apply WireExcursions.outside (b:=a)
  · rw [cut_outer]
    exact LabelledTurn.transparent (g:=cut) outerOutside false a
  apply WireExcursions.through cut_context
  change WireExcursions cut right (.inl bodyFront::_) a _
  apply WireExcursions.outside (b:=a)
  · rw [cut_body]
    exact LabelledTurn.transparent (g:=cut) oldBodyOutside false a
  apply WireExcursions.outside (b:=InitialOffsets.croAt 0 a)
  · rw [cut_body_end]
    exact LabelledTurn.node (g:=cut) croKept (.inr ()) (.inl ()) (.direct (InitialOffsets.Event.apply_rel (.cro 0) a))
  apply WireExcursions.outside (b:=InitialOffsets.croAt 0 a)
  · change LabelledTurn cut (cut.wire (.inl ⟨croKept,.inl ()⟩)) bindingEnd _ _
    rw [cut_cro_wire]
    exact LabelledTurn.transparent (g:=cut) bindingOutside true _
  apply WireExcursions.through cut_binding_wire
  change WireExcursions cut right (.inl argumentFront::_) _ _
  apply WireExcursions.outside (b:=InitialOffsets.croAt 0 a)
  · change LabelledTurn cut (cut.wire (.inr (.inl (.inr (.inl true))))) argumentEnd _ _
    rw [cut_argument_wire]
    exact LabelledTurn.transparent (g:=cut) argumentOutside false _
  exact .single argumentEnd _

private theorem directions : BetaEntriesForward concrete.site rawQ := by
  intro f h
  simpa [rawQ] using h

private theorem explicit_residual : BetaPathResidual concrete.site actualEdge rawQ (siteWord actualEdge) := by
  apply BetaPathResidual.outside
  apply BetaPathResidual.outside
  apply BetaPathResidual.context cut_context
  apply BetaPathResidual.outside
  apply BetaPathResidual.outside
  apply BetaPathResidual.outside
  apply BetaPathResidual.binding cut_binding_wire
  apply BetaPathResidual.outside
  exact .single argumentEnd

private theorem principal_inverse : actualEdge.principal.map concrete.sourceIso.symm.ends = corridor.edges :=
  concrete.sourceIso.symm.path_roundtrip corridor.edges

private theorem reverse_inverse : actualEdge.reverseRoute.map concrete.sourceIso.symm.ends = reverseEdges (g:=net) corridor.edges := by
  change (actualEdge.principal.reverse.map concrete.site.net.wire).map concrete.sourceIso.symm.ends = _
  rw [←principal_inverse]
  simp only [reverseEdges,List.map_reverse,List.map_map]
  apply congrArg List.reverse
  apply List.map_congr_left
  intro e _
  exact concrete.sourceIso.symm.wiring e

private theorem inverse_word : (siteWord actualEdge).map concrete.sourceIso.symm.ends = originalWord := by
  simp only [siteWord,List.map_append]
  rw [principal_inverse,reverse_inverse]
  rfl

private theorem coherent {old : List (Endpoint concrete.site.net)} {a : Context}
    (relation : BetaPathResidual concrete.site actualEdge rawQ old) :
    CoherentExpandedCore concrete.site.net (.inl ()) old a (InitialOffsets.croAt 0 a) := by
  obtain ⟨count,stream⟩ := relation.detour_blocks concrete.site geometry ((excursions a).labelling cut right)
  obtain ⟨flow⟩ := encode_flowBalance term 0
  apply stream.coherent (concrete.sourceIso.flowBalance flow) (by rfl)
    (concrete.sourceIso.independence (encode_closed_independence term closed 0))
    (concrete.sourceIso.transparency (encode_closed_transparency term closed 0))
  exact relation.head concrete.site rfl

theorem actual_returned_identity_copy_residual :
 ∃ edge : BetaEdge concrete.site.net,
   SiteBetaGeometry concrete.site edge ∧
   edge.principal = corridor.edges.map concrete.sourceIso.ends ∧
   ∀ a : Context,
     WireExcursions cut right rawQ a (InitialOffsets.croAt 0 a) ∧
     Labelling concrete.site.reduce actualQ a (InitialOffsets.croAt 0 a) ∧
     ∃ old : List (Endpoint concrete.site.net),
       BetaPathResidual concrete.site edge rawQ old ∧
       CoherentExpandedCore concrete.site.net (.inl ()) old a (InitialOffsets.croAt 0 a) ∧
       old = siteWord edge ∧
       old.map concrete.sourceIso.symm.ends = originalWord ∧
       (∀ alternative : List (Endpoint concrete.site.net),
         BetaPathResidual concrete.site edge rawQ alternative → alternative = old) := by
  refine ⟨actualEdge,geometry,rfl,?_⟩
  intro a
  have path := excursions a
  obtain ⟨old,relation,_⟩ := path.beta_lift concrete.site geometry directions
  have same := relation.source_unique concrete.site geometry explicit_residual
  exact ⟨path,path.labelling.actual cut right,old,relation,coherent relation,same,
    same ▸ inverse_word,fun alternative alt => alt.source_unique concrete.site geometry relation⟩

theorem no_direct_original_second_beta_edge :
 ¬ ∃ edge : BetaEdge net, edge.app = outerApp ∧ edge.lam = oldArgLam := by
  rintro ⟨edge,ha,hl⟩
  have ap := congrArg Label.index edge.appLabel
  have la := congrArg Label.index edge.lamLabel
  rw [ha] at ap
  rw [hl] at la
  change 0=edge.index at ap
  change 1=edge.index at la
  omega

#print axioms actual_returned_identity_copy_residual
#print axioms no_direct_original_second_beta_edge
end
end Lamping.Checks.ReturnedIdentityCopyResidual
