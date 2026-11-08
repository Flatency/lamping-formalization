import Lamping.Graph.Rewrite
namespace Lamping.Graph

private def portCast {S : Signature} {x y : Label S} (same : x=y) (p : S.Port x.sort) :
    S.Port y.sort := same ▸ p
private theorem portCast_heq {S : Signature} {x y : Label S} (same : x=y) (p : S.Port x.sort) :
    HEq (portCast same p) p := by cases same; rfl

private noncomputable def bijOfBijective (f : A → B) (inj : Function.Injective f)
    (surj : ∀ y,∃ x,f x=y) : Bij A B where
  toFun := f
  invFun y := Classical.choose (surj y)
  left_inv x := inj (Classical.choose_spec (surj (f x)))
  right_inv y := Classical.choose_spec (surj y)

/-- The actual node bijection and label compatibility induce all port names,
including their dependent sorts. No wiring assumption is part of this map. -/
noncomputable def carrierPorts {S : Signature} {N M : Type}
    (old : N → Label S) (fresh : M → Label S) (nodes : Bij M N)
    (compatible : ∀ m,old (nodes m)=fresh m) :
    Bij (NodePort S M fresh) (NodePort S N old) := by
  let image : NodePort S M fresh → NodePort S N old :=
    fun p => ⟨nodes p.1,portCast (compatible p.1).symm p.2⟩
  apply bijOfBijective image
  · rintro ⟨m,p⟩ ⟨n,q⟩ same
    have names : m=n := nodes.injective (congrArg Sigma.fst same)
    subst n
    have roles := sigma_snd_heq same
    have samePort : HEq p q := (portCast_heq (compatible m).symm p).symm.trans
      (roles.trans (portCast_heq (compatible m).symm q))
    have equal := eq_of_heq samePort
    subst q
    rfl
  · rintro ⟨n,p⟩
    let m := nodes.invFun n
    have name : nodes m=n := nodes.right_inv n
    have labels : old n=fresh m := (congrArg old name).symm.trans (compatible m)
    refine ⟨⟨m,portCast labels p⟩,?_⟩
    apply Sigma.ext name
    exact (portCast_heq (compatible m).symm (portCast labels p)).trans (portCast_heq labels p)

section
variable {S : Signature} {N M B W V : Type}
variable [FiniteNames N] [FiniteNames M] [FiniteNames B] [FiniteNames W] [FiniteNames V]

private def vertexEnds (vertices : Bij V W) : Bij (V × Bool) (W × Bool) where
  toFun x := (vertices x.1,x.2)
  invFun x := (vertices.invFun x.1,x.2)
  left_inv := by intro x; simp only [vertices.left_inv]
  right_inv := by intro x; simp only [vertices.right_inv]

noncomputable def carrierEnds (g : Net S N B W) (fresh : M → Label S)
    (nodes : Bij M N) (vertices : Bij V W) (compatible : ∀ m,g.label (nodes m)=fresh m) :
    Bij (End S M B V fresh) (End S N B W g.label) :=
  (carrierPorts g.label fresh nodes compatible).sum ((Bij.refl B).sum (vertexEnds vertices))

/-- Reindex all actual graph carriers by the supplied bijections; the entire
pairing, boundary and transparent vertices are retained. -/
noncomputable def Net.reindex (g : Net S N B W) (fresh : M → Label S)
    (nodes : Bij M N) (vertices : Bij V W) (compatible : ∀ m,g.label (nodes m)=fresh m) : Net S M B V :=
  ⟨fresh,g.wire.rename (carrierEnds g fresh nodes vertices compatible).symm⟩

noncomputable def Net.reindexIso (g : Net S N B W) (fresh : M → Label S)
    (nodes : Bij M N) (vertices : Bij V W) (compatible : ∀ m,g.label (nodes m)=fresh m) :
    NetIso (g.reindex fresh nodes vertices compatible) g where
  nodes := nodes
  vertices := vertices
  labels := compatible
  ports := carrierPorts g.label fresh nodes compatible
  port_node _ := rfl
  port_role p := portCast_heq (compatible p.1).symm p.2
  ends := carrierEnds g fresh nodes vertices compatible
  node_end _ := rfl
  boundary_end _ := rfl
  vertex_end _ _ := rfl
  wiring e := by
    change (carrierEnds g fresh nodes vertices compatible)
      ((carrierEnds g fresh nodes vertices compatible).invFun
        (g.wire ((carrierEnds g fresh nodes vertices compatible) e)))=_
    exact (carrierEnds g fresh nodes vertices compatible).right_inv _
end
end Lamping.Graph
