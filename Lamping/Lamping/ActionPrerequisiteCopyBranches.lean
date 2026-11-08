import Lamping.Lamping.ActionPendingFunctionBranches
import Lamping.Lamping.FamilyRepresentation
namespace Lamping.AG
open Graph Lambda Lambda.Labelled
section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable {current : LTerm} {g : Net signature N B W} {root : B}
/-- The first actual chain edge selects its own occurrence-indexed block. -/
theorem canonical_chain_head (selection : OccurrenceFragmentSelection current g root)
    (chain : PrerequisiteChain current p edges) (position : Position current.erase)
    (head : edges.head?=some position.val) :
    (canonicalChainImage selection chain).head?=some (selection position).fragment.segments := by
  cases edges with
  | nil => cases head
  | cons first rest => have same := Option.some.inj head; subst first; rfl

/-- A real function-child coordinate fixes its source role even with repeated labels. -/
theorem selected_function_role (selection : OccurrenceFragmentSelection current g root)
    (lookup : current.subterm p=some (.app stamp fn arg)) (position : Position current.erase)
    (atPosition : position.val=p++[.fn]) :
    SourceDeparture (.app stamp fn arg) .fn
      (sourceEdge (selection position).environment (selection position).context (selection position).term).fromPort := by
  obtain ⟨env,ctx,outer⟩ := SourceSubterm.of_lookup current lookup [] .external
  have actual : SourceSubterm [] .external current position.val env (.appFn stamp) fn := by
    rw [atPosition]
    exact outer.append (.fn .nil)
  have context := ((selection position).occurrence.same_occurrence actual).2.1
  have sourceFrom : (sourceEdge (selection position).environment (selection position).context
      (selection position).term).fromPort=.appFn stamp := by
    cases (selection position).term <;> exact context
  rw [sourceFrom]
  exact .fn
end
section
variable {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K → Label signature} {i j : Nat} {lt : i<j}
variable (site : PathSite (.fanAction .app i j lt) kept (B:=B) (W:=W) (V:=V))
/-- Source REP compares two given successful prerequisite chains. At actual
copied application contexts this forces the same pending fan branch. No
chain existence is inferred for an undefined endpoint. -/
theorem PathSite.prerequisite_app_copy_branches
    {current : LTerm} {root : B} {boundary : B → Bool}
    (matching : Matches site.net root current.erase) (inputs : RootInputs site.net root)
    (flow : FlowBalance site.net boundary) (positive : boundary root=true)
    (closed : Closed current.erase) (selection : OccurrenceFragmentSelection current site.net root)
    (joint : JointRepresentation closed selection)
    (leftLookup : current.subterm p=some (.app leftStamp leftFn leftArg))
    (rightLookup : current.subterm q=some (.app rightStamp rightFn rightArg))
    (leftChain : PrerequisiteChain current p left) (rightChain : PrerequisiteChain current q right)
    (iso : ChainIncidenceIsomorphic (chainSyntaxIncidence current closed left)
      (chainSyntaxIncidence current closed right))
    (leftTarget rightTarget : RootAccess site.reduce root)
    (leftWord : accessWord site.reduce leftTarget.val=p)
    (rightWord : accessWord site.reduce rightTarget.val=q)
    (leftBranch rightBranch : Bool)
    (leftFinish : leftTarget.val.getLast?=some (site.reduce.wire (.inl ⟨.inr (.inl leftBranch),appCtx⟩)))
    (rightFinish : rightTarget.val.getLast?=some (site.reduce.wire (.inl ⟨.inr (.inl rightBranch),appCtx⟩))) :
    leftBranch=rightBranch := by
  let leftParentPosition : Position current.erase := ⟨p,by rw [←LTerm.erase_subterm,leftLookup]; rfl⟩
  let rightParentPosition : Position current.erase := ⟨q,by rw [←LTerm.erase_subterm,rightLookup]; rfl⟩
  have leftFnLookup : current.subterm (p++[.fn])=some leftFn := by
    rw [LTerm.subterm_append,leftLookup]; cases leftFn <;> rfl
  have rightFnLookup : current.subterm (q++[.fn])=some rightFn := by
    rw [LTerm.subterm_append,rightLookup]; cases rightFn <;> rfl
  let leftPosition : Position current.erase := ⟨p++[.fn],by rw [←LTerm.erase_subterm,leftFnLookup]; cases leftFn <;> rfl⟩
  let rightPosition : Position current.erase := ⟨q++[.fn],by rw [←LTerm.erase_subterm,rightFnLookup]; cases rightFn <;> rfl⟩
  obtain ⟨leftParent,leftParentWord,_⟩ := Matches.observation site.net matching leftParentPosition
  obtain ⟨rightParent,rightParentWord,_⟩ := Matches.observation site.net matching rightParentPosition
  have leftReader := (selection leftPosition).fragment.fan_target_app_function_branch site matching inputs flow positive
    (selected_function_role selection leftLookup leftPosition rfl) leftParent
    (by simp only [leftParentWord]; rfl) leftTarget (leftParentWord.trans leftWord.symm) leftBranch leftFinish
  have rightReader := (selection rightPosition).fragment.fan_target_app_function_branch site matching inputs flow positive
    (selected_function_role selection rightLookup rightPosition rfl) rightParent
    (by simp only [rightParentWord]; rfl) rightTarget (rightParentWord.trans rightWord.symm) rightBranch rightFinish
  have leftHead : left.head?=some leftPosition.val := by
    rcases leftChain.app_cases leftLookup with ⟨_,_,_,same⟩|⟨_,_,same,_⟩ <;> rw [same] <;> rfl
  have rightHead : right.head?=some rightPosition.val := by
    rcases rightChain.app_cases rightLookup with ⟨_,_,_,same⟩|⟨_,_,same,_⟩ <;> rw [same] <;> rfl
  have physical := (joint.1 leftChain rightChain).mpr iso
  have heads := congrArg List.head? physical
  rw [canonical_chain_head selection leftChain leftPosition leftHead,
    canonical_chain_head selection rightChain rightPosition rightHead] at heads
  have same := Option.some.inj heads
  apply (selection leftPosition).fragment.function_control_branch_unique site (Or.inl rfl) leftReader
  intro a b labels
  exact rightReader a b (same ▸ labels)
end
end Lamping.AG