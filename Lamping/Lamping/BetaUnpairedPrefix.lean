import Lamping.Lamping.BetaProperAncestors
import Lamping.Lamping.BetaDetourReflection
namespace Lamping.AG
open Graph
section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable {g : Net signature N B W} {root : B}

/-- The positive-count check is valid at any outgoing proper source, including
components with no root access. -/
theorem BetaDetourBlocks.proper_positive_count {es a b count}
    (path : BetaDetourBlocks g es a b count) {boundary : B → Bool}
    (flow : FlowBalance g boundary) (rootPositive : boundary root=true)
    {first role level} (head : es.head?=some first)
    (source : AtProperRole g root first role level) (outgoing : role.outgoing)
    (edge : BetaEdge g) (occurs : edge.ctxEnd ∈ es) : 0<count := by
  by_cases zero : count=0
  · subst count
    have positive := (path.zero_ordinary g).positive_departures flow (by
      intro e atHead
      rw [head] at atHead
      cases Option.some.inj atHead
      exact source.outgoing_flow outgoing flow.nodes boundary flow.vertices rootPositive) _ occurs
    rw [edge.ctx_polarity] at positive
    cases positive
  · omega

/-- Split the first reversed beta block without choosing a root prefix. The
actual ordinary head starts at the original proper port. Its totality below
is ONLY totality of this head; its changed output is not identified with an
admissible argument-suffix input. -/
theorem BetaDetourBlocks.first_backward_proper_inputs {es a b count}
    (path : BetaDetourBlocks g es a b count) (positive : 0<count)
    {boundary : B → Bool} (flow : FlowBalance g boundary) (rootPositive : boundary root=true)
    (independence : Independence g root) {first role level}
    (head : es.head?=some first) (source : AtProperRole g root first role level)
    (outgoing : role.outgoing) :
    ∃ (edge : BetaEdge g) (pre tail : List (Endpoint g)) (seam : Context) (remaining : Nat),
      count=remaining+1 ∧ es=pre++edge.reverseRoute++tail ∧
      pre.head?=some first ∧ Forward g pre ∧ Labelling g pre a seam ∧
      pre.getLast?=some (g.wire (.inl ⟨edge.lam,edge.lamBind⟩)) ∧
      tail.head?=some edge.argEnd ∧ BetaDetourBlocks g tail seam b remaining ∧
      ∀ x, ∃ changedSeam, Labelling g pre (a.replace level x) changedSeam := by
  obtain ⟨edge,pre,tail,seam,remaining,countEq,split,labels,finish,tailHead,rest⟩ :=
    path.first_backward g positive
  have preHead : pre.head?=some first := by
    cases pre with
    | nil => exact False.elim (labels.nonempty rfl)
    | cons e pre =>
      rw [split] at head
      exact head
  have forward := labels.forward_of_flow flow (by
    intro e atHead
    rw [preHead] at atHead
    cases Option.some.inj atHead
    exact source.outgoing_flow outgoing flow.nodes boundary flow.vertices rootPositive)
  have total := (independence pre first (.inl ⟨edge.lam,edge.lamBind⟩) role .lamBind level edge.index
    a seam preHead finish source outgoing
    (.lamBind edge.lam edge.lamBind edge.index edge.lamLabel edge.lamBind_role) trivial forward labels).1
  exact ⟨edge,pre,tail,seam,remaining,countEq,split,preHead,forward,labels,finish,tailHead,rest,total⟩
end
end Lamping.AG

