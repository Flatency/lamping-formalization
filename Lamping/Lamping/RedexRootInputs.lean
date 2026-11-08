import Lamping.Lamping.MatchingRedexEndpointUniqueness
import Lamping.Lamping.RootPathInputs
import Lamping.Lamping.ExpandedIndependence
import Lamping.Lamping.PathLabelDeterminism
namespace Lamping.AG
open Graph Lambda

private theorem app_identity (actual : Label signature) (i : Nat) (lab : actual=label .app i)
    {p q : Port actual.sort} {a b : Context}
    (rule : Traversal actual.index actual.sort p q a b) : a=b := by
  subst actual
  cases rule with
  | direct rule => cases rule <;> rfl
  | inverse rule => cases rule <;> rfl

section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable {g : Net signature N B W} {depths : B → Int} {root : B}

/-- Arbitrary high tails on this actual redex connection, with the low shell
of its real parent assignment. The same child access supplies the entire
continuation; no arbitrary proper-path extension or full I is used. -/
theorem ActualRedexAccess.connection_tail_inputs {t : Term} {redex : RedexOcc t}
    (access : ActualRedexAccess g root redex) (inputs : RootInputs g root)
    (balance : IndexedLevelBalance g depths) (rootDepth : depths root=0)
    {input seam : Context} (parentLabels : Labelling g access.parent.val input seam)
    (requested : Context) :
    ∃ output,Labelling g access.connection.edges
      (seam.replace access.connection.appIndex requested) output := by
  obtain ⟨width,_lower,_strict,_fixed,sync⟩ := balance.independence_tail root rootDepth
    access.parent.val (.inr (.inl root)) (.inl ⟨access.connection.app,access.ctx⟩)
    .root .appCtx 0 access.connection.appIndex input seam
    access.parent.property.2.1 access.parentFinish (.root) trivial
    (.appCtx access.connection.app access.ctx access.connection.appIndex
      access.connection.appLabel access.contextPrincipal) trivial access.parent.property.1.2 parentLabels
  let newInput := input.replace width requested
  have changedParent : Labelling g access.parent.val newInput
      (seam.replace access.connection.appIndex requested) := sync requested
  obtain ⟨output,changedChild⟩ := inputs.access access.child newInput
  obtain ⟨initial,parentSplit⟩ := List.getLast?_eq_some_iff.mp access.parentFinish
  obtain ⟨tail,connectionSplit⟩ := List.head?_eq_some_iff.mp access.connection.start
  have childSplit : access.child.val=initial++
      (g.wire (.inl ⟨access.connection.app,access.ctx⟩))::
      (.inl ⟨access.connection.app,access.connection.appPort⟩)::tail := by
    simpa only [parentSplit,connectionSplit,List.append_assoc,List.singleton_append] using access.split
  rw [childSplit] at changedChild
  obtain ⟨middle,pref,suff⟩ := changedChild.split_segment
  have actualParent : Labelling g access.parent.val newInput middle := by
    simpa only [parentSplit] using pref
  have same := actualParent.output_unique changedParent
  subst middle
  cases suff with
  | cons turn rest =>
    rw [Pairing.involutive] at turn
    cases turn with
    | node node p q rule =>
      have equal := app_identity _ access.connection.appIndex access.connection.appLabel rule
      cases equal
      exact ⟨output,by simpa only [connectionSplit] using rest⟩
end
end Lamping.AG
