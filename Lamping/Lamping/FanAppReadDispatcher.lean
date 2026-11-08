import Lamping.Lamping.FanAppLambdaDispatcher
import Lamping.Lamping.FanBodyLambdaDispatcher
import Lamping.Lamping.FanKeptFragmentComparison
import Lamping.Lamping.FragmentTerminalSeparation
import Lamping.Lamping.BetaOldChainImages
namespace Lamping.AG
open Graph Lambda Lambda.Labelled
section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable {g : Net signature N B W} {root : B} {current : LTerm}
/-- Actual terminal equality of literal fragments preserves the observed kind. -/
theorem SourceEdgeFragment.access_kind_eq_of_segments_eq
    (first : SourceEdgeFragment current g root leftEdge p)
    (second : SourceEdgeFragment current g root rightEdge q)
    (pieces : first.segments=second.segments) :
    accessKind g first.access.val=accessKind g second.access.val := by
  have lasts := congrArg List.getLast? pieces
  rw [first.segments_last_eq_access_last,second.segments_last_eq_access_last] at lasts
  simp only [accessKind,lasts]

/-- Metadata of THIS actual APP access, not a label-to-node identification. -/
theorem Matches.app_access_typed (matching : Matches g root current.erase)
    (lookup : current.subterm p=some (.app stamp fn arg))
    (path : RootAccess g root) (word : accessWord g path.val=p) :
    accessKind g path.val=some .app := by
  let pos : Position current.erase := ⟨p,by rw [←LTerm.erase_subterm,lookup];rfl⟩
  obtain ⟨observed,observedWord,sub,observedLookup,observes⟩ := Matches.observation g matching pos
  have erased : subtermAt current.erase p=some (.app fn.erase arg.erase) := by
    rw [←LTerm.erase_subterm,lookup];rfl
  have subEq : sub=.app fn.erase arg.erase := Option.some.inj (observedLookup.symm.trans erased)
  subst sub
  have same : path=observed := matching.accessWord_injective (word.trans observedWord.symm)
  rw [same]
  exact observes.1

/-- An actual successful APP edge is an APP function departure. Lambda-only
eligibility and root arrival are genuinely excluded, not input profiles. -/
theorem OccurrenceFragment.app_read_incoming
    (occurrence : OccurrenceFragment current g root position)
    (chain : PrerequisiteChain current start edges) (member : position∈edges)
    (lookup : current.subterm position=some (.app stamp fn arg)) :
    ∃origin,occurrence.context=.appFn origin := by
  rcases occurrence with ⟨sub,env,ctx,actual,fragment⟩
  rcases chain.eligible member with ⟨parent,origin,f,a,split,_parentLookup⟩|⟨origin,body,atLambda⟩
  · rcases actual.last_departure with ⟨empty,_external⟩|⟨other,step,term,otherSplit,_otherLookup,role⟩
    · exact False.elim (chain.reading_ne_nil member empty)
    · have steps : step=.fn := by
        have last := congrArg List.getLast? (otherSplit.symm.trans split)
        simp only [List.getLast?_append,List.getLast?_singleton,Option.some_or] at last
        exact Option.some.inj last
      subst step
      cases role with
      | fn => exact ⟨_,rfl⟩
  · have different := Option.some.inj (lookup.symm.trans atLambda)
    cases different
end
section
variable {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K→Label signature} {i j : Nat} {lt : i<j}
variable (site : PathSite (.fanAction .lam i j lt) kept (B:=B) (W:=W) (V:=V))
private theorem kept_piece_equality
    {directions : B → Bool} (flow : FlowBalance site.net directions)
    (root : B) (positive : directions root=true) {current : LTerm}
    (sourceMatches : Matches site.net root current.erase) (targetMatches : Matches site.reduce root current.erase)
    (principal : SiteActionPrincipal site) {p q : Path}
    (sourceFirst : OccurrenceFragment current site.net root p)
    (targetFirst : OccurrenceFragment current site.reduce root p)
    (sourceSecond : OccurrenceFragment current site.net root q)
    (targetSecond : OccurrenceFragment current site.reduce root q)
    {leftTerm rightTerm : LTerm} {leftStep rightStep : Step}
    (leftRole : SourceDeparture leftTerm leftStep (sourceEdge sourceFirst.environment sourceFirst.context sourceFirst.term).fromPort)
    (rightRole : SourceDeparture rightTerm rightStep (sourceEdge sourceSecond.environment sourceSecond.context sourceSecond.term).fromPort)
    (sourceLeft sourceRight : RootAccess site.net root) (targetLeft targetRight : RootAccess site.reduce root)
    (sourceLeftWord : p=accessWord site.net sourceLeft.val++[leftStep])
    (sourceRightWord : q=accessWord site.net sourceRight.val++[rightStep])
    (targetLeftWord : p=accessWord site.reduce targetLeft.val++[leftStep])
    (targetRightWord : q=accessWord site.reduce targetRight.val++[rightStep])
    (leftParent rightParent leftEnd rightEnd : NodePort signature K kept)
    (leftParentAt : targetLeft.val.getLast?=some (site.reduce.wire (.inl ⟨.inl leftParent.1,leftParent.2⟩)))
    (rightParentAt : targetRight.val.getLast?=some (site.reduce.wire (.inl ⟨.inl rightParent.1,rightParent.2⟩)))
    (leftEndAt : targetFirst.fragment.access.val.getLast?=some (site.reduce.wire (.inl ⟨.inl leftEnd.1,leftEnd.2⟩)))
    (rightEndAt : targetSecond.fragment.access.val.getLast?=some (site.reduce.wire (.inl ⟨.inl rightEnd.1,rightEnd.2⟩))) :
    targetFirst.fragment.segments=targetSecond.fragment.segments ↔sourceFirst.fragment.segments=sourceSecond.fragment.segments := by
  rcases sourceFirst with ⟨lsub,lenv,lctx,locc,lsource⟩
  rcases targetFirst with ⟨_,_,_,ltocc,ltarget⟩
  obtain ⟨rfl,rfl,rfl⟩ := locc.same_occurrence ltocc
  rcases sourceSecond with ⟨rsub,renv,rctx,rocc,rsource⟩
  rcases targetSecond with ⟨_,_,_,rtocc,rtarget⟩
  obtain ⟨rfl,rfl,rfl⟩ := rocc.same_occurrence rtocc
  exact lsource.fan_kept_piece_equality site flow root positive sourceMatches targetMatches principal
    ltarget rsource rtarget leftRole rightRole sourceLeft sourceRight targetLeft targetRight
    sourceLeftWord sourceRightWord targetLeftWord targetRightWord leftParent rightParent leftEnd rightEnd
    leftParentAt rightParentAt leftEndAt rightEndAt


theorem PathSite.fan_app_read_same_slot_forward
    {current : LTerm} {root : B} {boundary : B→Bool} {n : Nat}
    (sourceMatches : Matches site.net root current.erase) (targetMatches : Matches site.reduce root current.erase)
    (flow : FlowBalance site.net boundary) (positive : boundary root=true)
    (principal : SiteActionPrincipal site) (selection : OccurrenceFragmentSelection current site.net root)
    (first : PrerequisiteChain current p left) (second : PrerequisiteChain current q right)
    (physical : SameChainRepresentation selection first second)
    (leftPosition rightPosition : Position current.erase)
    (leftSlot : left[n]?=some leftPosition.val) (rightSlot : right[n]?=some rightPosition.val)
    (leftLookup : current.subterm leftPosition.val=some (.app leftStamp leftFn leftArg))
    (rightLookup : current.subterm rightPosition.val=some (.app rightStamp rightFn rightArg))
    (targetFirst : OccurrenceFragment current site.reduce root leftPosition.val)
    (targetSecond : OccurrenceFragment current site.reduce root rightPosition.val)
    : targetFirst.fragment.segments=targetSecond.fragment.segments := by
  have pieces := same_chain_representation_slot selection first second physical leftPosition rightPosition leftSlot rightSlot
  let sourceFirst := selection leftPosition
  let sourceSecond := selection rightPosition
  obtain ⟨leftOrigin,leftContext⟩ := sourceFirst.app_read_incoming first (List.mem_of_getElem? leftSlot) leftLookup
  obtain ⟨rightOrigin,rightContext⟩ := sourceSecond.app_read_incoming second (List.mem_of_getElem? rightSlot) rightLookup
  have sourceLeftIncoming : ∃stamp,sourceFirst.context=.appFn stamp ∨sourceFirst.context=.appArg stamp := ⟨leftOrigin,Or.inl leftContext⟩
  have sourceRightIncoming : ∃stamp,sourceSecond.context=.appFn stamp ∨sourceSecond.context=.appArg stamp := ⟨rightOrigin,Or.inl rightContext⟩
  obtain ⟨lp,lstep,la,lfn,larg,lLookup,lSplit,_lsteps,lRole⟩ := sourceFirst.app_incoming_parent sourceLeftIncoming
  obtain ⟨rp,rstep,ra,rfn,rarg,rLookup,rSplit,_rsteps,rRole⟩ := sourceSecond.app_incoming_parent sourceRightIncoming
  let leftParentPosition : Position current.erase := ⟨lp,by rw [←LTerm.erase_subterm,lLookup];rfl⟩
  let rightParentPosition : Position current.erase := ⟨rp,by rw [←LTerm.erase_subterm,rLookup];rfl⟩
  obtain ⟨sourceLeft,sourceLeftWord,_⟩ := Matches.observation site.net sourceMatches leftParentPosition
  obtain ⟨sourceRight,sourceRightWord,_⟩ := Matches.observation site.net sourceMatches rightParentPosition
  obtain ⟨targetLeft,targetLeftWord,lu,leftShape,leftObs⟩ := Matches.observation site.reduce targetMatches leftParentPosition
  obtain ⟨targetRight,targetRightWord,ru,rightShape,rightObs⟩ := Matches.observation site.reduce targetMatches rightParentPosition
  have lErased : subtermAt current.erase lp=some (.app lfn.erase larg.erase) := by
    rw [←LTerm.erase_subterm,lLookup];rfl
  have rErased : subtermAt current.erase rp=some (.app rfn.erase rarg.erase) := by
    rw [←LTerm.erase_subterm,rLookup];rfl
  have leftTerm : lu=.app lfn.erase larg.erase := Option.some.inj (leftShape.symm.trans lErased)
  have rightTerm : ru=.app rfn.erase rarg.erase := Option.some.inj (rightShape.symm.trans rErased)
  subst lu
  subst ru
  have excluded : ∀port : Port (.op .lam),portKind (.op .lam) port≠some AccessKind.app := by
    intro port wrong
    rcases port with u|aux
    · cases u;cases wrong
    · cases aux <;> cases wrong
  obtain ⟨lpPort,lpAt⟩ := site.action_access_kept_of_kind_excluded (.fan .lam i j lt) targetLeft leftObs.1 excluded
  obtain ⟨rpPort,rpAt⟩ := site.action_access_kept_of_kind_excluded (.fan .lam i j lt) targetRight rightObs.1 excluded
  have sourceLeftChildWord : leftPosition.val=accessWord site.net sourceLeft.val++[lstep] := by rw [sourceLeftWord];exact lSplit
  have sourceRightChildWord : rightPosition.val=accessWord site.net sourceRight.val++[rstep] := by rw [sourceRightWord];exact rSplit
  have targetLeftChildWord : leftPosition.val=accessWord site.reduce targetLeft.val++[lstep] := by rw [targetLeftWord];exact lSplit
  have targetRightChildWord : rightPosition.val=accessWord site.reduce targetRight.val++[rstep] := by rw [targetRightWord];exact rSplit
  have leftChildKind := targetMatches.app_access_typed leftLookup targetFirst.fragment.access targetFirst.fragment.word
  have rightChildKind := targetMatches.app_access_typed rightLookup targetSecond.fragment.access targetSecond.fragment.word
  obtain ⟨lcPort,lcAt⟩ := site.action_access_kept_of_kind_excluded (.fan .lam i j lt) targetFirst.fragment.access leftChildKind excluded
  obtain ⟨rcPort,rcAt⟩ := site.action_access_kept_of_kind_excluded (.fan .lam i j lt) targetSecond.fragment.access rightChildKind excluded
  exact (kept_piece_equality site flow root positive sourceMatches targetMatches principal
    sourceFirst targetFirst sourceSecond targetSecond lRole rRole sourceLeft sourceRight targetLeft targetRight
    sourceLeftChildWord sourceRightChildWord targetLeftChildWord targetRightChildWord lpPort rpPort lcPort rcPort
    lpAt rpAt lcAt rcAt).mpr pieces

theorem PathSite.fan_app_read_same_slot_reflect
    {current : LTerm} {root : B} {boundary : B→Bool} {n : Nat}
    (sourceMatches : Matches site.net root current.erase) (targetMatches : Matches site.reduce root current.erase)
    (flow : FlowBalance site.net boundary) (positive : boundary root=true)
    (principal : SiteActionPrincipal site) (selection : OccurrenceFragmentSelection current site.reduce root)
    (first : PrerequisiteChain current p left) (second : PrerequisiteChain current q right)
    (physical : SameChainRepresentation selection first second)
    (leftPosition rightPosition : Position current.erase)
    (leftSlot : left[n]?=some leftPosition.val) (rightSlot : right[n]?=some rightPosition.val)
    (leftLookup : current.subterm leftPosition.val=some (.app leftStamp leftFn leftArg))
    (rightLookup : current.subterm rightPosition.val=some (.app rightStamp rightFn rightArg))
    (sourceFirst : OccurrenceFragment current site.net root leftPosition.val)
    (sourceSecond : OccurrenceFragment current site.net root rightPosition.val)
    : sourceFirst.fragment.segments=sourceSecond.fragment.segments := by
  have pieces := same_chain_representation_slot selection first second physical leftPosition rightPosition leftSlot rightSlot
  let targetFirst := selection leftPosition
  let targetSecond := selection rightPosition
  obtain ⟨leftOrigin,leftContext⟩ := sourceFirst.app_read_incoming first (List.mem_of_getElem? leftSlot) leftLookup
  obtain ⟨rightOrigin,rightContext⟩ := sourceSecond.app_read_incoming second (List.mem_of_getElem? rightSlot) rightLookup
  have sourceLeftIncoming : ∃stamp,sourceFirst.context=.appFn stamp ∨sourceFirst.context=.appArg stamp := ⟨leftOrigin,Or.inl leftContext⟩
  have sourceRightIncoming : ∃stamp,sourceSecond.context=.appFn stamp ∨sourceSecond.context=.appArg stamp := ⟨rightOrigin,Or.inl rightContext⟩
  obtain ⟨lp,lstep,la,lfn,larg,lLookup,lSplit,_lsteps,lRole⟩ := sourceFirst.app_incoming_parent sourceLeftIncoming
  obtain ⟨rp,rstep,ra,rfn,rarg,rLookup,rSplit,_rsteps,rRole⟩ := sourceSecond.app_incoming_parent sourceRightIncoming
  let leftParentPosition : Position current.erase := ⟨lp,by rw [←LTerm.erase_subterm,lLookup];rfl⟩
  let rightParentPosition : Position current.erase := ⟨rp,by rw [←LTerm.erase_subterm,rLookup];rfl⟩
  obtain ⟨sourceLeft,sourceLeftWord,_⟩ := Matches.observation site.net sourceMatches leftParentPosition
  obtain ⟨sourceRight,sourceRightWord,_⟩ := Matches.observation site.net sourceMatches rightParentPosition
  obtain ⟨targetLeft,targetLeftWord,lu,leftShape,leftObs⟩ := Matches.observation site.reduce targetMatches leftParentPosition
  obtain ⟨targetRight,targetRightWord,ru,rightShape,rightObs⟩ := Matches.observation site.reduce targetMatches rightParentPosition
  have lErased : subtermAt current.erase lp=some (.app lfn.erase larg.erase) := by
    rw [←LTerm.erase_subterm,lLookup];rfl
  have rErased : subtermAt current.erase rp=some (.app rfn.erase rarg.erase) := by
    rw [←LTerm.erase_subterm,rLookup];rfl
  have leftTerm : lu=.app lfn.erase larg.erase := Option.some.inj (leftShape.symm.trans lErased)
  have rightTerm : ru=.app rfn.erase rarg.erase := Option.some.inj (rightShape.symm.trans rErased)
  subst lu
  subst ru
  have excluded : ∀port : Port (.op .lam),portKind (.op .lam) port≠some AccessKind.app := by
    intro port wrong
    rcases port with u|aux
    · cases u;cases wrong
    · cases aux <;> cases wrong
  obtain ⟨lpPort,lpAt⟩ := site.action_access_kept_of_kind_excluded (.fan .lam i j lt) targetLeft leftObs.1 excluded
  obtain ⟨rpPort,rpAt⟩ := site.action_access_kept_of_kind_excluded (.fan .lam i j lt) targetRight rightObs.1 excluded
  have sourceLeftChildWord : leftPosition.val=accessWord site.net sourceLeft.val++[lstep] := by rw [sourceLeftWord];exact lSplit
  have sourceRightChildWord : rightPosition.val=accessWord site.net sourceRight.val++[rstep] := by rw [sourceRightWord];exact rSplit
  have targetLeftChildWord : leftPosition.val=accessWord site.reduce targetLeft.val++[lstep] := by rw [targetLeftWord];exact lSplit
  have targetRightChildWord : rightPosition.val=accessWord site.reduce targetRight.val++[rstep] := by rw [targetRightWord];exact rSplit
  have leftChildKind := targetMatches.app_access_typed leftLookup targetFirst.fragment.access targetFirst.fragment.word
  have rightChildKind := targetMatches.app_access_typed rightLookup targetSecond.fragment.access targetSecond.fragment.word
  obtain ⟨lcPort,lcAt⟩ := site.action_access_kept_of_kind_excluded (.fan .lam i j lt) targetFirst.fragment.access leftChildKind excluded
  obtain ⟨rcPort,rcAt⟩ := site.action_access_kept_of_kind_excluded (.fan .lam i j lt) targetSecond.fragment.access rightChildKind excluded
  exact (kept_piece_equality site flow root positive sourceMatches targetMatches principal
    sourceFirst targetFirst sourceSecond targetSecond lRole rRole sourceLeft sourceRight targetLeft targetRight
    sourceLeftChildWord sourceRightChildWord targetLeftChildWord targetRightChildWord lpPort rpPort lcPort rcPort
    lpAt rpAt lcAt rcAt).mp pieces
end
end Lamping.AG
#print axioms Lamping.AG.SourceEdgeFragment.access_kind_eq_of_segments_eq
#print axioms Lamping.AG.Matches.app_access_typed
#print axioms Lamping.AG.OccurrenceFragment.app_read_incoming

#print axioms Lamping.AG.PathSite.fan_app_read_same_slot_forward
#print axioms Lamping.AG.PathSite.fan_app_read_same_slot_reflect
