import Lamping.Lamping.CancellationFragmentTransport
import Lamping.Lamping.FamilyRepresentation
namespace Lamping.AG
open Graph Lambda Lambda.Labelled
private theorem map_comparison {A B X Y : Type}
    (f : A → X) (g : B → X) (h : A → Y) (k : B → Y)
    (compare : ∀ a b,f a=g b ↔h a=k b) (xs : List A) (ys : List B) :
    xs.map f=ys.map g ↔xs.map h=ys.map k := by
  induction xs generalizing ys with
  | nil => cases ys <;> simp
  | cons a xs ih =>
    cases ys with
    | nil => simp
    | cons b ys =>
      simp only [List.map_cons,List.cons.injEq]
      exact and_congr (compare a b) (ih ys)
section
variable {s : Schema} {K B W V : Type} [FiniteNames K] [FiniteNames B]
  [FiniteNames W] [FiniteNames V] {kept : K → Label signature}
variable (site : PathSite s kept (B:=B) (W:=W) (V:=V))

theorem PathSite.cancellation_chain_representation
    (cancel : IsCancellation s) {boundary : B → Bool}
    (flow : FlowBalance site.net boundary) (root : B) (positive : boundary root=true)
    {current : LTerm} (sourceMatches : Matches site.net root current.erase)
    (targetMatches : Matches site.reduce root current.erase)
    (source : OccurrenceFragmentSelection current site.net root)
    (target : OccurrenceFragmentSelection current site.reduce root)
    (first : PrerequisiteChain current p left) (second : PrerequisiteChain current q right) :
    SameChainRepresentation target first second ↔SameChainRepresentation source first second := by
  unfold SameChainRepresentation canonicalChainImage
  apply map_comparison
  intro a b
  exact site.cancellation_occurrence_equality cancel flow root positive sourceMatches targetMatches
    (source _) (target _) (source _) (target _)

theorem PathSite.cancellation_joint_representation
    (cancel : IsCancellation s) {boundary : B → Bool}
    (flow : FlowBalance site.net boundary) (root : B) (positive : boundary root=true)
    {current : LTerm} (closed : Closed current.erase)
    (sourceMatches : Matches site.net root current.erase)
    (targetMatches : Matches site.reduce root current.erase)
    (source : OccurrenceFragmentSelection current site.net root)
    (target : OccurrenceFragmentSelection current site.reduce root) :
    JointRepresentation closed target ↔JointRepresentation closed source := by
  have pieces (a b : SyntaxIncidence.Edge current) :
      (target a).fragment.segments=(target b).fragment.segments ↔
        (source a).fragment.segments=(source b).fragment.segments :=
    site.cancellation_occurrence_equality cancel flow root positive sourceMatches targetMatches
      (source a) (target a) (source b) (target b)
  have chains : ChainRepresentationInvariant closed target ↔ChainRepresentationInvariant closed source := by
    constructor
    · intro invariant p q left right first second
      exact (site.cancellation_chain_representation cancel flow root positive sourceMatches targetMatches
        source target first second).symm.trans (invariant first second)
    · intro invariant p q left right first second
      exact (site.cancellation_chain_representation cancel flow root positive sourceMatches targetMatches
        source target first second).trans (invariant first second)
  have auxiliary : AuxiliarySeparation closed target ↔AuxiliarySeparation closed source := by
    constructor
    · intro invariant a b first second label distinct
      exact invariant a b first second label (fun equal=>distinct ((pieces a b).mp equal))
    · intro invariant a b first second label distinct
      exact invariant a b first second label (fun equal=>distinct ((pieces a b).mpr equal))
  exact and_congr chains auxiliary
end
end Lamping.AG
