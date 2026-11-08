import Lamping.Lamping.NetIsoPathTransport
import Lamping.Lamping.NetIsoInvariantTransport
import Lamping.Lamping.InitialFullIndependence
import Lamping.Lamping.GlobalGraphSteps
import Lamping.Lamping.Encoding
import Lamping.Lamping.Fixtures
namespace Lamping.Checks.Phase5Bridges
open Graph AG Lambda
example {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
    (g : Net signature N B W) : GraphTrace (ActualNet.ofNet g) (ActualNet.ofNet g) [] :=
  GraphTrace.refl _
example (t : Term) : GraphTrace (ActualNet.initial t) (ActualNet.initial t) [] := .refl _
example : GraphStep (.beta 0) (ActualNet.ofNet actualBetaSite.net)
    (ActualNet.ofNet actualBetaReduced) := GraphStep.site betaKeptLabels actualBetaSite
example : GraphTrace (ActualNet.ofNet actualBetaSite.net)
    (ActualNet.ofNet actualBetaReduced) [.beta 0] :=
  .single (GraphStep.site betaKeptLabels actualBetaSite)
example {B : Type} [FiniteNames B] {g h k : ActualNet B} {ss tt : List Schema}
    (first : GraphTrace g h ss) (second : GraphTrace h k tt) : GraphTrace g k (ss++tt) :=
  first.trans second
example {B : Type} [FiniteNames B] {g h : ActualNet B} (iso : NetIso g.net h.net) :
    GraphTrace g h [] := .iso iso
example {B : Type} [FiniteNames B] {g h : ActualNet B} {s : Schema}
    (normal : GraphNormal g) (step : GraphStep s g h) : False := normal s h step
#print axioms GraphStep.site
#print axioms GraphTrace.trans
#print axioms GraphReachable.trans
end Lamping.Checks.Phase5Bridges

namespace Lamping.Checks.Phase5Bridges
open Graph AG Lambda
private abbrev croNet := leftNet .cro .cro 0 0
private def swappedNodes : Bij (Unit⊕Unit) (Unit⊕Unit) where
  toFun | .inl _ => .inr () | .inr _ => .inl ()
  invFun | .inl _ => .inr () | .inr _ => .inl ()
  left_inv := by rintro (u|u) <;> cases u <;> rfl
  right_inv := by rintro (u|u) <;> cases u <;> rfl
private def swappedPorts : Bij (NodePort signature (Unit⊕Unit) croNet.label)
    (NodePort signature (Unit⊕Unit) croNet.label) where
  toFun | ⟨.inl _,p⟩ => ⟨.inr (),p⟩ | ⟨.inr _,p⟩ => ⟨.inl (),p⟩
  invFun | ⟨.inl _,p⟩ => ⟨.inr (),p⟩ | ⟨.inr _,p⟩ => ⟨.inl (),p⟩
  left_inv := by rintro ⟨u|u,p⟩ <;> cases u <;> rfl
  right_inv := by rintro ⟨u|u,p⟩ <;> cases u <;> rfl
private def swappedEnds : Bij (Endpoint croNet) (Endpoint croNet) where
  toFun | .inl p => .inl (swappedPorts p) | .inr b => .inr b
  invFun | .inl p => .inl (swappedPorts.invFun p) | .inr b => .inr b
  left_inv := by rintro (p|b); exact congrArg Sum.inl (swappedPorts.left_inv p); rfl
  right_inv := by rintro (p|b); exact congrArg Sum.inl (swappedPorts.right_inv p); rfl
private def renamedCro : Net signature (Unit⊕Unit) (Unit⊕Unit) Empty :=
  ⟨croNet.label,croNet.wire.rename swappedEnds⟩
private def croIso : NetIso croNet renamedCro where
  nodes := swappedNodes
  vertices := Bij.refl _
  labels := by rintro (u|u) <;> rfl
  ports := swappedPorts
  port_node := by rintro ⟨u|u,p⟩ <;> rfl
  port_role := by rintro ⟨u|u,p⟩ <;> rfl
  ends := swappedEnds
  node_end _ := rfl
  boundary_end _ := rfl
  vertex_end w _ := nomatch w
  wiring e := (Pairing.rename_apply croNet.wire swappedEnds e).symm
private def crossing : List (Endpoint croNet) :=
  [.inr (.inl (.inl ())),.inl ⟨.inl (),.inl ()⟩,.inl ⟨.inr (),.inr ()⟩]
private theorem crossing_labels : Labelling croNet crossing Context.empty Context.empty := by
  have cro : Passage 0 (.op .cro) (.inr ()) (.inl ()) Context.empty Context.empty := by
    simpa only [Context.replace_zero,Context.cons_empty] using
      Passage.cro (i:=0) Context.empty Context.empty
  exact .cons (.node (Sum.inl () : Unit⊕Unit) _ _ (.direct cro))
    (.cons (.node (Sum.inr () : Unit⊕Unit) _ _ (.inverse cro)) (.single _ _))
example : Labelling renamedCro (crossing.map croIso.ends) Context.empty Context.empty :=
  croIso.labelling crossing_labels
example : AG.accessWord renamedCro (crossing.map croIso.ends)=AG.accessWord croNet crossing :=
  croIso.accessWord crossing
example (root : Unit⊕Unit) (t : Term) : Matches croNet root t ↔ Matches renamedCro root t :=
  croIso.matches_iff
#print axioms NetIso.matches
#print axioms NetIso.bindingSuffix_iff
example (root : Unit⊕Unit) (old : OrdinaryPathInvariants croNet root) :
    OrdinaryPathInvariants renamedCro root := croIso.ordinaryInvariants old
example : ∃ cs,ContextTrace renamedCro (crossing.map croIso.ends) cs ∧
    cs.head?=some Context.empty ∧cs.getLast?=some Context.empty := by
  obtain ⟨cs,trace,first,last⟩ := crossing_labels.contextTrace croNet
  exact ⟨cs,croIso.contextTrace trace,first,last⟩
example {M V : Type} [FiniteNames M] [FiniteNames V] (t : Term) (closed : Closed t)
    (target : Net signature M (Boundary t) V) (iso : NetIso (encode 7 t).net target) :
    OrdinaryPathInvariants target (.inl ()) :=
  iso.ordinaryInvariants (encode_closed_ordinary_invariants t closed 7)
#print axioms NetIso.independence
#print axioms NetIso.nesting
#print axioms NetIso.transparency
end Lamping.Checks.Phase5Bridges
