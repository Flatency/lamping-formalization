import Lamping.Lamping.FanLambdaChainPassages
namespace Lamping.AG
open Graph Lambda Lambda.Labelled
section
variable {n : Nat}
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable {current : LTerm} {g : Net signature N B W} {root : B}

/-- An actual edge slot supplies its own bound and its exact physical block. -/
theorem canonical_chain_slot (selection : OccurrenceFragmentSelection current g root)
    (chain : PrerequisiteChain current start edges) (position : Position current.erase)
    (slot : edges[n]?=some position.val) :
    (canonicalChainImage selection chain)[n]?=some (selection position).fragment.segments := by
  obtain ⟨bound,atSlot⟩ := List.getElem?_eq_some_iff.mp slot
  have imageBound : n<(canonicalChainImage selection chain).length := by
    rw [canonicalChainImage_length];exact bound
  rw [List.getElem?_eq_getElem imageBound]
  simp only [canonicalChainImage,List.getElem_map]
  apply congrArg (fun pos : Position current.erase=>some (selection pos).fragment.segments)
  apply Subtype.ext
  simpa only [List.getElem_attach] using atSlot

/-- Piece equality at corresponding actual ordinals is a consequence of
whole canonical image equality, not a caller-supplied transport certificate. -/
theorem same_chain_representation_slot
    (selection : OccurrenceFragmentSelection current g root)
    (first : PrerequisiteChain current p left) (second : PrerequisiteChain current q right)
    (physical : SameChainRepresentation selection first second)
    (leftPosition rightPosition : Position current.erase)
    (leftSlot : left[n]?=some leftPosition.val)
    (rightSlot : right[n]?=some rightPosition.val) :
    (selection leftPosition).fragment.segments=(selection rightPosition).fragment.segments := by
  have same := congrArg (fun blocks=>blocks[n]?) physical
  change (canonicalChainImage selection first)[n]?=(canonicalChainImage selection second)[n]? at same
  rw [canonical_chain_slot selection first leftPosition leftSlot,
    canonical_chain_slot selection second rightPosition rightSlot] at same
  exact Option.some.inj same
end
section
variable {n : Nat}
variable {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K→Label signature} {i j : Nat} {lt : i<j}
variable (site : PathSite (.fanAction .lam i j lt) kept (B:=B) (W:=W) (V:=V))

/-- The corresponding slots of two actual whole-chain images synchronize
copied-lambda fan branches. Source Joint truth is not a hidden premise. -/
theorem PathSite.fan_lambda_same_slot_branches
    {current : LTerm} {root : B} {boundary : B→Bool}
    (matching : Matches site.net root current.erase)
    (flow : FlowBalance site.net boundary) (positive : boundary root=true)
    (principal : SiteActionPrincipal site)
    (selection : OccurrenceFragmentSelection current site.net root)
    (first : PrerequisiteChain current p left) (second : PrerequisiteChain current q right)
    (physical : SameChainRepresentation selection first second)
    (leftPosition rightPosition : Position current.erase)
    (leftSlot : left[n]?=some leftPosition.val) (rightSlot : right[n]?=some rightPosition.val)
    (leftTarget rightTarget : RootAccess site.reduce root)
    (leftWord : accessWord site.reduce leftTarget.val=leftPosition.val)
    (rightWord : accessWord site.reduce rightTarget.val=rightPosition.val)
    (leftBranch rightBranch : Bool)
    (leftFinish : leftTarget.val.getLast?=some (site.reduce.wire (.inl ⟨.inr (.inl leftBranch),.inl ()⟩)))
    (rightFinish : rightTarget.val.getLast?=some (site.reduce.wire (.inl ⟨.inr (.inl rightBranch),.inl ()⟩))) :
    leftBranch=rightBranch := by
  have same := same_chain_representation_slot selection first second physical
    leftPosition rightPosition leftSlot rightSlot
  obtain ⟨leftPre,leftSplit,leftLast⟩ := (selection leftPosition).fragment.target_lambda_writer
    site matching flow positive principal leftTarget leftWord.symm leftBranch leftFinish
  obtain ⟨rightPre,rightSplit,rightLast⟩ := (selection rightPosition).fragment.target_lambda_writer
    site matching flow positive principal rightTarget rightWord.symm rightBranch rightFinish
  exact site.writer_suffix_aux_unique principal (leftSplit.symm.trans (same.trans rightSplit)) leftLast rightLast

/-- A genuine source Joint induction hypothesis supplies whole-image equality
from the actual bare iso. This is conditional and does not assert that such
source Joint truth has been proved for any current graph. -/
theorem PathSite.fan_lambda_joint_same_slot_branches
    {current : LTerm} {root : B} {boundary : B→Bool}
    (matching : Matches site.net root current.erase)
    (flow : FlowBalance site.net boundary) (positive : boundary root=true)
    (principal : SiteActionPrincipal site)
    (closed : Closed current.erase) (selection : OccurrenceFragmentSelection current site.net root)
    (joint : JointRepresentation closed selection)
    (first : PrerequisiteChain current p left) (second : PrerequisiteChain current q right)
    (iso : ChainIncidenceIsomorphic (chainSyntaxIncidence current closed left)
      (chainSyntaxIncidence current closed right))
    (leftPosition rightPosition : Position current.erase)
    (leftSlot : left[n]?=some leftPosition.val) (rightSlot : right[n]?=some rightPosition.val)
    (leftTarget rightTarget : RootAccess site.reduce root)
    (leftWord : accessWord site.reduce leftTarget.val=leftPosition.val)
    (rightWord : accessWord site.reduce rightTarget.val=rightPosition.val)
    (leftBranch rightBranch : Bool)
    (leftFinish : leftTarget.val.getLast?=some (site.reduce.wire (.inl ⟨.inr (.inl leftBranch),.inl ()⟩)))
    (rightFinish : rightTarget.val.getLast?=some (site.reduce.wire (.inl ⟨.inr (.inl rightBranch),.inl ()⟩))) :
    leftBranch=rightBranch := by
  exact site.fan_lambda_same_slot_branches matching flow positive principal selection first second
    ((joint.1 first second).mpr iso) leftPosition rightPosition leftSlot rightSlot
    leftTarget rightTarget leftWord rightWord leftBranch rightBranch leftFinish rightFinish
end
end Lamping.AG
#print axioms Lamping.AG.canonical_chain_slot
#print axioms Lamping.AG.same_chain_representation_slot
#print axioms Lamping.AG.PathSite.fan_lambda_same_slot_branches
#print axioms Lamping.AG.PathSite.fan_lambda_joint_same_slot_branches