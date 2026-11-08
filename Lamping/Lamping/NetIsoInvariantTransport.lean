import Lamping.Lamping.NetIsoPathTransport
import Lamping.Lamping.GlobalPathInvariants
namespace Lamping.Graph
open Lamping.AG Lamping.Lambda
section
variable {N M B W V : Type} [FiniteNames N] [FiniteNames M] [FiniteNames B]
  [FiniteNames W] [FiniteNames V]
variable {g : Net signature N B W} {h : Net signature M B V} (iso : NetIso g h)

theorem NetIso.path_roundtrip (es : List (Endpoint h)) :
    (es.map iso.symm.ends).map iso.ends=es := by
  simp only [List.map_map]
  have same : (iso.ends ∘ iso.symm.ends)=id := funext iso.ends.right_inv
  rw [same,List.map_id]

theorem NetIso.properRole {root : B} {e : Endpoint g} {role : ProperRole} {index : Nat}
    (atPort : AtProperRole g root e role index) : AtProperRole h root (iso.ends e) role index := by
  cases atPort with
  | root => rw [iso.boundary_end]; exact .root
  | appCtx node p i lab port =>
    rw [iso.node_end_image]
    exact .appCtx _ _ index ((iso.labels node).trans lab) ((iso.imagePort_heq _ _).trans port)
  | appFun node p i lab port =>
    rw [iso.node_end_image]
    exact .appFun _ _ index ((iso.labels node).trans lab) ((iso.imagePort_heq _ _).trans port)
  | appArg node p i lab port =>
    rw [iso.node_end_image]
    exact .appArg _ _ index ((iso.labels node).trans lab) ((iso.imagePort_heq _ _).trans port)
  | lamCtx node p i lab port =>
    rw [iso.node_end_image]
    exact .lamCtx _ _ index ((iso.labels node).trans lab) ((iso.imagePort_heq _ _).trans port)
  | lamBody node p i lab port =>
    rw [iso.node_end_image]
    exact .lamBody _ _ index ((iso.labels node).trans lab) ((iso.imagePort_heq _ _).trans port)
  | lamBind node p i lab port =>
    rw [iso.node_end_image]
    exact .lamBind _ _ index ((iso.labels node).trans lab) ((iso.imagePort_heq _ _).trans port)

theorem NetIso.contextTrace {es cs} (trace : ContextTrace g es cs) :
    ContextTrace h (es.map iso.ends) cs := by
  induction trace with
  | single e a => exact .single _ _
  | cons turn tail ih =>
    apply ContextTrace.cons
    · rw [←iso.wiring]
      exact iso.labelledTurn turn
    · exact ih

include iso

theorem NetIso.independence {root : B} (old : Independence g root) : Independence h root := by
  intro es e f sr tr m n a b head last source outgoing target incoming fw labels
  have oldHead : (es.map iso.symm.ends).head?=some (iso.symm.ends e) := by rw [List.head?_map,head]; rfl
  have oldLast : (es.map iso.symm.ends).getLast?=some (g.wire (iso.symm.ends f)) := by
    rw [List.getLast?_map,last]
    exact congrArg some (iso.symm.wiring f)
  obtain ⟨arbitrary,width,lower,strict,tail,sync⟩ := old _ _ _ sr tr m n a b oldHead oldLast
    (iso.symm.properRole source) outgoing (iso.symm.properRole target) incoming
    (iso.symm.forward fw) (iso.symm.labelling labels)
  refine ⟨?_,width,lower,strict,tail,?_⟩
  · intro x
    obtain ⟨output,changed⟩ := arbitrary x
    exact ⟨output,by simpa only [iso.path_roundtrip] using iso.labelling changed⟩
  · intro y
    simpa only [iso.path_roundtrip] using iso.labelling (sync y)

theorem NetIso.nesting {root : B} (old : Nesting g root) : Nesting h root := by
  intro es cs trace rooted fw i j e a b n role before atI atJ atA atB context target shell
  have oldRoot : (es.map iso.symm.ends).head?=some (.inr (.inl root)) := by
    rw [List.head?_map,rooted]
    exact congrArg some (iso.symm.boundary_end root)
  have oldI : (es.map iso.symm.ends)[i]?=some (iso.symm.ends e) := by rw [List.getElem?_map,atI]; rfl
  have oldJ : (es.map iso.symm.ends)[j]?=some (iso.symm.ends e) := by rw [List.getElem?_map,atJ]; rfl
  have oldTarget := iso.symm.properRole target
  rw [iso.symm.wiring] at oldTarget
  exact old _ _ (iso.symm.contextTrace trace) oldRoot (iso.symm.forward fw)
    i j _ a b n role before oldI oldJ atA atB context oldTarget shell

theorem NetIso.transparency {root : B} (old : Transparency g root) : Transparency h root := by
  intro es a b node ctx body bind isLam ctxRole bodyRole bindRole rooted finish fw labels
  let oldNode := iso.symm.nodes node
  let oldCtx := iso.symm.imagePort node ctx
  let oldBody := iso.symm.imagePort node body
  let oldBind := iso.symm.imagePort node bind
  have oldLam : (g.label oldNode).sort=.op .lam := by
    rw [iso.symm.labels]
    exact isLam
  have oldRoot : (es.map iso.symm.ends).head?=some (.inr (.inl root)) := by
    rw [List.head?_map,rooted]
    exact congrArg some (iso.symm.boundary_end root)
  have oldFinish : (es.map iso.symm.ends).getLast?=some (g.wire (.inl ⟨oldNode,oldBind⟩)) := by
    rw [List.getLast?_map,finish]
    simp only [Option.map_some,iso.symm.wiring,iso.symm.node_end_image,oldNode,oldBind]
  obtain ⟨pre,loop,middle,binding,split,binderEq,preLast,preLabels⟩ :=
    old _ a b oldNode oldCtx oldBody oldBind oldLam
      ((iso.symm.imagePort_heq _ _).trans ctxRole)
      ((iso.symm.imagePort_heq _ _).trans bodyRole)
      ((iso.symm.imagePort_heq _ _).trans bindRole)
      oldRoot oldFinish (iso.symm.forward fw) (iso.symm.labelling labels)
  refine ⟨pre.map iso.ends,loop.map iso.ends,middle,iso.bindingLoop binding,?_,?_,?_,iso.labelling preLabels⟩
  · have mapped := congrArg (List.map iso.ends) split
    rw [iso.path_roundtrip,List.map_append] at mapped
    exact mapped
  · change iso.nodes binding.binder=node
    rw [binderEq]
    exact iso.nodes.right_inv node
  · rw [List.getLast?_map,preLast]
    change some (iso.ends (g.wire (.inl ⟨oldNode,oldCtx⟩)))=some (h.wire (.inl ⟨node,ctx⟩))
    have endEq : (.inl ⟨oldNode,oldCtx⟩ : Endpoint g)=iso.symm.ends (.inl ⟨node,ctx⟩) :=
      (iso.symm.node_end_image node ctx).symm
    rw [endEq,iso.wiring]
    have inverse : iso.ends (iso.symm.ends (.inl ⟨node,ctx⟩))=(.inl ⟨node,ctx⟩ : Endpoint h) :=
      iso.ends.right_inv _
    rw [inverse]

theorem NetIso.ordinaryInvariants {root : B} (old : OrdinaryPathInvariants g root) :
    OrdinaryPathInvariants h root :=
  ⟨iso.independence old.independence,iso.nesting old.nesting,iso.transparency old.transparency⟩
end
end Lamping.Graph
