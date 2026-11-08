import Lamping.Lamping.MatchedControlInputs
import Lamping.Lamping.HighTailTransport
import Lamping.Lamping.NetIsoInvariantTransport
namespace Lamping.AG
open Graph
section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable (g : Net signature N B W) (root : B)

/-- Arbitrary input exists on each already labelled, forward, typed ROOT path.
This has no quantifier over non-root proper sources and asserts no extension
of a partial control path. The trace-preservation proof is separate. -/
def RootInputs : Prop :=
  ∀ (es : List (Endpoint g)) (a b : Context) (terminal : Endpoint g)
    (role : ProperRole) (level : Nat),
    Labelling g es a b → Forward g es → es.head?=some (.inr (.inl root)) →
    es.getLast?=some (g.wire terminal) → AtProperRole g root terminal role level → role.incoming →
    ∀ requested : Context, ∃ output, Labelling g es requested output
end
section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable {g : Net signature N B W} {root : B}

/-- Full ordinary Independence implies its root-input component. The converse
is neither used nor asserted. -/
theorem Independence.rootInputs (indep : Independence g root) : RootInputs g root := by
  intro es a b terminal role level labels forward rooted finish atTerminal incoming requested
  obtain ⟨total,_⟩ := indep es (.inr (.inl root)) terminal .root role 0 level a b rooted finish
    (.root) trivial atTerminal incoming forward labels
  obtain ⟨output,changed⟩ := total requested
  exact ⟨output,by simpa only [Context.replace_zero] using changed⟩

/-- Existing observable root accesses need only root input existence, with
actual terminal metadata recovered from their observation. -/
theorem RootInputs.access (inputs : RootInputs g root) (path : RootAccess g root)
    (requested : Context) : ∃ output, Labelling g path.val requested output := by
  obtain ⟨input,output,labels⟩ := path.property.1.1
  obtain ⟨terminal,role,level,finish,atTerminal,incoming⟩ := path.incoming_endpoint
  exact inputs path.val input output terminal role level labels path.property.1.2
    path.property.2.1 finish atTerminal incoming requested

/-- Reset the terminal tail of an existing rooted application prefix from
structural indexed balance alone. No arbitrary-input existence is invoked. -/
theorem IndexedLevelBalance.relabel_app_prefix {boundary : B → Int}
    (balance : IndexedLevelBalance g boundary) (rootDepth : boundary root=0) (edge : BetaEdge g)
    {pre : List (Endpoint g)} {input seam target : Context}
    (labels : Labelling g pre input seam) (forward : Forward g pre)
    (rooted : pre.head?=some (.inr (.inl root)))
    (finish : pre.getLast?=some (g.wire (.inl ⟨edge.app,edge.appCtx⟩)))
    (shell : Context.SameShell edge.index seam target) :
    ∃ newInput, Labelling g pre newInput target := by
  obtain ⟨width,_,_,_,sync⟩ := balance.independence_tail root rootDepth pre (.inr (.inl root))
    (.inl ⟨edge.app,edge.appCtx⟩) .root .appCtx 0 edge.index input seam rooted finish
    (.root) trivial (.appCtx edge.app edge.appCtx edge.index edge.appLabel edge.appCtx_role)
    trivial forward labels
  refine ⟨input.replace width (target.tail edge.index),?_⟩
  have changed := sync (target.tail edge.index)
  change Labelling g pre (input.replace width (target.tail edge.index))
    (seam.replace edge.index (target.tail edge.index)) at changed
  rw [Context.replace_of_sameShell seam target edge.index shell] at changed
  exact changed
end
end Lamping.AG

namespace Lamping.Graph
open Lamping.AG
section
variable {N M B W V : Type} [FiniteNames N] [FiniteNames M] [FiniteNames B]
  [FiniteNames W] [FiniteNames V]
variable {g : Net signature N B W} {h : Net signature M B V} (iso : NetIso g h)

include iso

/-- Boundary-fixed physical isomorphism transports this root-only property. -/
theorem NetIso.rootInputs {root : B} (inputs : RootInputs g root) : RootInputs h root := by
  intro es a b terminal role level labels forward rooted finish atTerminal incoming requested
  have oldHead : (es.map iso.symm.ends).head?=some (.inr (.inl root)) := by
    rw [List.head?_map,rooted]
    exact congrArg some (iso.symm.boundary_end root)
  have oldFinish : (es.map iso.symm.ends).getLast?=some (g.wire (iso.symm.ends terminal)) := by
    rw [List.getLast?_map,finish]
    exact congrArg some (iso.symm.wiring terminal)
  obtain ⟨output,changed⟩ := inputs (es.map iso.symm.ends) a b (iso.symm.ends terminal) role level
    (iso.symm.labelling labels) (iso.symm.forward forward) oldHead oldFinish
    (iso.symm.properRole atTerminal) incoming requested
  exact ⟨output,by simpa only [iso.path_roundtrip] using iso.labelling changed⟩
end
end Lamping.Graph


