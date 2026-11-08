import Lamping.Lamping.MatchingDefinitions
namespace Lamping.Graph
open Lamping.AG Lamping.Lambda
private def castPort {x y : Label signature} (eq : x=y) (p : Port x.sort) : Port y.sort := eq ▸ p
private theorem castPort_heq {x y : Label signature} (eq : x=y) (p : Port x.sort) :
    HEq (castPort eq p) p := by cases eq; rfl
private theorem castPort_injective {x y : Label signature} (eq : x=y) :
    Function.Injective (castPort eq) := by cases eq; exact fun _ _ h => h
private theorem traversal_cast {x y : Label signature} (eq : x=y) {p q : Port x.sort}
    (ht : Traversal x.index x.sort p q a b) :
    Traversal y.index y.sort (castPort eq p) (castPort eq q) a b := by cases eq; exact ht
private theorem forward_cast {x y : Label signature} (eq : x=y) {p q : Port x.sort}
    (ht : ForwardPorts x.sort p q) : ForwardPorts y.sort (castPort eq p) (castPort eq q) := by
  cases eq; exact ht
section
variable {N M B W V : Type} [FiniteNames N] [FiniteNames M] [FiniteNames B]
  [FiniteNames W] [FiniteNames V]
variable {g : Net signature N B W} {h : Net signature M B V} (iso : NetIso g h)

def NetIso.imagePort (n : N) (p : Port (g.label n).sort) : Port (h.label (iso.nodes n)).sort :=
  castPort (iso.labels n).symm p

theorem NetIso.imagePort_heq (n : N) (p : Port (g.label n).sort) : HEq (iso.imagePort n p) p :=
  castPort_heq _ _

theorem NetIso.node_end_image (n : N) (p : Port (g.label n).sort) :
    iso.ends (.inl ⟨n,p⟩)=.inl ⟨iso.nodes n,iso.imagePort n p⟩ := by
  rw [iso.node_end]
  apply congrArg Sum.inl
  exact Sigma.ext (iso.port_node ⟨n,p⟩)
    ((iso.port_role ⟨n,p⟩).trans (iso.imagePort_heq n p).symm)

theorem NetIso.turn {x y : Endpoint g} (ht : Turn g x y) : Turn h (iso.ends x) (iso.ends y) := by
  cases ht with
  | node n p q different =>
    rw [iso.node_end_image,iso.node_end_image]
    exact .node _ _ _ (fun eq => different (castPort_injective (iso.labels n).symm eq))
  | transparent w d =>
    rw [iso.vertex_end,iso.vertex_end]
    exact .transparent _ _

theorem NetIso.labelledTurn {x y : Endpoint g} (ht : LabelledTurn g x y a b) :
    LabelledTurn h (iso.ends x) (iso.ends y) a b := by
  cases ht with
  | node n p q rule =>
    rw [iso.node_end_image,iso.node_end_image]
    exact .node _ _ _ (traversal_cast (iso.labels n).symm rule)
  | transparent w d a =>
    rw [iso.vertex_end,iso.vertex_end]
    exact .transparent _ _ _

theorem NetIso.walk {es : List (Endpoint g)} (walk : Walk g es) : Walk h (es.map iso.ends) := by
  induction walk with
  | single => exact .single _
  | cons ht rest ih =>
    apply Walk.cons
    · rw [←iso.wiring]
      exact iso.turn ht
    · exact ih

theorem NetIso.labelling {es : List (Endpoint g)} (labels : Labelling g es a b) :
    Labelling h (es.map iso.ends) a b := by
  induction labels with
  | single => exact .single _ _
  | cons ht rest ih =>
    apply Labelling.cons
    · rw [←iso.wiring]
      exact iso.labelledTurn ht
    · exact ih

theorem NetIso.forward {es : List (Endpoint g)} (path : Forward g es) : Forward h (es.map iso.ends) := by
  induction path with
  | single => exact .single _
  | @node e f es n p q arrives leaves direction rest ih =>
    refine Forward.node (iso.nodes n) (iso.imagePort n p) (iso.imagePort n q) ?_ ?_
      (forward_cast (iso.labels n).symm direction) ih
    · rw [←iso.wiring,arrives,iso.node_end_image]
    · rw [leaves,iso.node_end_image]
  | @transparent e f es w d arrives leaves rest ih =>
    refine Forward.transparent (iso.vertices w) d ?_ ?_ ih
    · rw [←iso.wiring,arrives,iso.vertex_end]
    · rw [leaves,iso.vertex_end]

theorem NetIso.proper {es : List (Endpoint g)} (path : ProperPath g es) :
    ProperPath h (es.map iso.ends) := by
  obtain ⟨a,b,path⟩ := path
  exact ⟨a,b,iso.labelling path⟩

theorem NetIso.forwardProper {es : List (Endpoint g)} (path : ForwardProperPath g es) :
    ForwardProperPath h (es.map iso.ends) := ⟨iso.proper path.1,iso.forward path.2⟩
end
end Lamping.Graph

namespace Lamping.Graph
open Lamping.AG Lamping.Lambda
private def observedWord (l : Label signature) (p : Port l.sort) : Path :=
  match l.sort,p with
  | .op .app,.inl () => [.fn]
  | .op .app,.inr true => [.arg]
  | .op .lam,.inr true => [.body]
  | _,_ => []
private theorem observedWord_cast {x y : Label signature} (eq : x=y) (p : Port x.sort) :
    observedWord y (castPort eq p)=observedWord x p := by cases eq; rfl
private theorem portKind_cast {x y : Label signature} (eq : x=y) (p : Port x.sort) :
    portKind y.sort (castPort eq p)=portKind x.sort p := by cases eq; rfl
section
variable {N M B W V : Type} [FiniteNames N] [FiniteNames M] [FiniteNames B]
  [FiniteNames W] [FiniteNames V]
variable {g : Net signature N B W} {h : Net signature M B V} (iso : NetIso g h)

theorem NetIso.arrivalWord (e : Endpoint g) : AG.arrivalWord h (iso.ends e)=AG.arrivalWord g e := by
  rcases e with ⟨n,p⟩ | (b | ⟨w,d⟩)
  · rw [iso.node_end_image]
    exact observedWord_cast (iso.labels n).symm p
  · rw [iso.boundary_end]; rfl
  · rw [iso.vertex_end]; rfl

theorem NetIso.accessWord (es : List (Endpoint g)) : AG.accessWord h (es.map iso.ends)=AG.accessWord g es := by
  cases es with
  | nil => rfl
  | cons e es =>
    change (es.map iso.ends).flatMap (AG.arrivalWord h)=es.flatMap (AG.arrivalWord g)
    rw [List.flatMap_map]
    have same : (AG.arrivalWord h ∘ iso.ends)=AG.arrivalWord g := funext (iso.arrivalWord)
    exact congrArg (fun f => es.flatMap f) same

private theorem terminalKind_map (e : Endpoint g) :
    (match h.wire (iso.ends e) with
      | .inl ⟨n,p⟩ => portKind (h.label n).sort p
      | _ => none) =
    (match g.wire e with
      | .inl ⟨n,p⟩ => portKind (g.label n).sort p
      | _ => none) := by
  rw [←iso.wiring]
  generalize g.wire e = terminal
  rcases terminal with ⟨n,p⟩ | (b | ⟨w,d⟩)
  · rw [iso.node_end_image]
    exact portKind_cast (iso.labels n).symm p
  · rw [iso.boundary_end]
  · rw [iso.vertex_end]

theorem NetIso.accessKind (es : List (Endpoint g)) : AG.accessKind h (es.map iso.ends)=AG.accessKind g es := by
  unfold AG.accessKind
  rw [List.getLast?_map]
  cases last : es.getLast? with
  | none => rfl
  | some e => exact terminalKind_map iso e

def NetIso.bindingLoop {es : List (Endpoint g)} (loop : BindingLoop g es a b) :
    BindingLoop h (es.map iso.ends) a b where
  binder := iso.nodes loop.binder
  isLam := by rw [iso.labels]; exact loop.isLam
  body := iso.imagePort loop.binder loop.body
  bind := iso.imagePort loop.binder loop.bind
  body_role := (iso.imagePort_heq _ _).trans loop.body_role
  bind_role := (iso.imagePort_heq _ _).trans loop.bind_role
  start := by
    rw [List.head?_map,loop.start]
    simp only [Option.map_some,iso.node_end_image]
  finish := by
    rw [List.getLast?_map,loop.finish]
    simp only [Option.map_some,iso.wiring,iso.node_end_image]
  proper := iso.labelling loop.proper
  forward := iso.forward loop.forward
  shell := by rw [iso.labels]; exact loop.shell

theorem NetIso.bindingSuffix {es : List (Endpoint g)} (bound : BindingSuffix g es k) :
    BindingSuffix h (es.map iso.ends) k := by
  obtain ⟨pre,loop,a,b,c,binding,ctx,same,role,finish,labels,index⟩ := bound
  let next := iso.bindingLoop binding
  refine ⟨pre.map iso.ends,loop.map iso.ends,a,b,c,next,iso.imagePort binding.binder ctx,?_,
    (iso.imagePort_heq _ _).trans role,?_,iso.labelling labels,?_⟩
  · rw [same,List.map_append]
  · rw [List.getLast?_map,finish]
    simp only [Option.map_some,iso.wiring,iso.node_end_image, next, NetIso.bindingLoop]
  · rw [iso.accessWord]
    exact index

private theorem map_inverse (es : List (Endpoint g)) : (es.map iso.ends).map iso.symm.ends=es := by
  simp only [List.map_map]
  have same : (iso.symm.ends ∘ iso.ends)=id := funext iso.ends.left_inv
  rw [same,List.map_id]

theorem NetIso.bindingSuffix_iff (es : List (Endpoint g)) :
    BindingSuffix h (es.map iso.ends) k ↔ BindingSuffix g es k := by
  constructor
  · intro bound
    simpa only [map_inverse] using iso.symm.bindingSuffix bound
  · exact iso.bindingSuffix

theorem NetIso.observes {es : List (Endpoint g)} (observation : Observes g es shape) :
    Observes h (es.map iso.ends) shape := by
  refine ⟨(iso.accessKind es).trans observation.1,?_⟩
  cases shape with
  | app => trivial
  | lam => trivial
  | var k =>
    exact ⟨iso.bindingSuffix observation.2.1,fun j bound =>
      observation.2.2 j ((iso.bindingSuffix_iff es).mp bound)⟩

theorem NetIso.rootAccess {root : B} {es : List (Endpoint g)} (access : IsRootAccess g root es) :
    IsRootAccess h root (es.map iso.ends) := by
  refine ⟨iso.forwardProper access.1,?_,?_⟩
  · rw [List.head?_map,access.2.1]
    simp only [Option.map_some,iso.boundary_end]
  · obtain ⟨k,hk⟩ := access.2.2
    exact ⟨k,(iso.accessKind es).trans hk⟩
end
end Lamping.Graph

namespace Lamping.Graph
open Lamping.AG Lamping.Lambda
section
variable {N M B W V : Type} [FiniteNames N] [FiniteNames M] [FiniteNames B]
  [FiniteNames W] [FiniteNames V]
variable {g : Net signature N B W} {h : Net signature M B V} (iso : NetIso g h)

def NetIso.rootAccessBij (root : B) : Bij (RootAccess g root) (RootAccess h root) where
  toFun access := ⟨access.val.map iso.ends,iso.rootAccess access.property⟩
  invFun access := ⟨access.val.map iso.symm.ends,iso.symm.rootAccess access.property⟩
  left_inv access := Subtype.ext (map_inverse iso access.val)
  right_inv access := Subtype.ext (map_inverse iso.symm access.val)

theorem NetIso.corresponds {es : List (Endpoint g)} {t : Term} {p : Position t}
    (correspondence : Corresponds g es t p) : Corresponds h (es.map iso.ends) t p := by
  obtain ⟨word,u,term,observed⟩ := correspondence
  exact ⟨(iso.accessWord es).trans word,u,term,iso.observes observed⟩

include iso

theorem NetIso.matches {root : B} {t : Term} (matched : Matches g root t) : Matches h root t := by
  obtain ⟨f,correspondence,prefixes⟩ := matched
  let paths := iso.rootAccessBij root
  refine ⟨paths.symm.trans f,?_,?_⟩
  · intro access
    change Corresponds h access.val t (f (paths.invFun access))
    have same : (paths.invFun access).val.map iso.ends=access.val :=
      congrArg Subtype.val (paths.right_inv access)
    simpa only [same] using iso.corresponds (correspondence (paths.invFun access))
  · intro es fs suffix
    obtain ⟨tail,same⟩ := suffix
    apply prefixes (paths.invFun es) (paths.invFun fs)
    refine ⟨tail.map iso.symm.ends,?_⟩
    change fs.val.map iso.symm.ends=es.val.map iso.symm.ends++tail.map iso.symm.ends
    rw [same,List.map_append]

theorem NetIso.matches_iff {root : B} {t : Term} : Matches g root t ↔ Matches h root t :=
  ⟨iso.matches,iso.symm.matches⟩
end
end Lamping.Graph
