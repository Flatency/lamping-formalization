import Lamping.Lamping.FanKeptFragmentComparison
import Lamping.Lamping.ChainRepresentation
namespace Lamping.AG
open Graph Lambda Lambda.Labelled
section
variable {op : Op} {i j : Nat} {lt : i<j}
variable {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K → Label signature}
variable (site : PathSite (Schema.fanAction op i j lt) kept (B:=B) (W:=W) (V:=V))

/-- New control nodes cannot be terminal syntax observations. -/
theorem PathSite.fan_control_access_kept
    (control : op=.fan ∨ op=.cro ∨ op=.bra) {root : B}
    (path : RootAccess site.reduce root) :
    ∃ port : NodePort signature K kept,
      path.val.getLast?=some (site.reduce.wire (.inl ⟨.inl port.1,port.2⟩)) := by
  obtain ⟨kind,typed⟩ := path.property.2.2
  cases last : path.val.getLast? with
  | none => simp only [accessKind,last,Option.bind_none] at typed; cases typed
  | some e =>
    rw [accessKind,last] at typed
    cases arrival : site.reduce.wire e with
    | inr rest => simp only [Option.bind_some,arrival] at typed; cases typed
    | inl port =>
      rcases port with ⟨node,p⟩
      simp only [Option.bind_some,arrival] at typed
      cases node with
      | inl n =>
        refine ⟨⟨n,p⟩,?_⟩
        rw [←arrival,Pairing.involutive]
      | inr fresh =>
        cases fresh with
        | inl b =>
          change portKind (.op op) p=some kind at typed
          rcases control with rfl | rfl | rfl <;> cases p <;> cases typed
        | inr a =>
          change portKind (.op .fan) p=some kind at typed
          cases p <;> cases typed

/-- Actual observations supply every kept-parent premise of the fan cut.
The two compared positions may differ and the fragment choices are arbitrary. -/
theorem PathSite.fan_control_nonroot_occurrence_equality
    (control : op=.fan ∨ op=.cro ∨ op=.bra)
    {directions : B → Bool} (flow : FlowBalance site.net directions)
    (root : B) (positive : directions root=true) {current : LTerm}
    (sourceMatches : Matches site.net root current.erase)
    (targetMatches : Matches site.reduce root current.erase)
    (principal : SiteActionPrincipal site) {p q : Path}
    (leftNonroot : p≠[]) (rightNonroot : q≠[])
    (sourceFirst : OccurrenceFragment current site.net root p)
    (targetFirst : OccurrenceFragment current site.reduce root p)
    (sourceSecond : OccurrenceFragment current site.net root q)
    (targetSecond : OccurrenceFragment current site.reduce root q) :
    targetFirst.fragment.segments=targetSecond.fragment.segments ↔
      sourceFirst.fragment.segments=sourceSecond.fragment.segments := by
  rcases sourceFirst with ⟨leftSub,leftEnv,leftCtx,leftOccurrence,sourceFirst⟩
  rcases targetFirst with ⟨_otherSub,_otherEnv,_otherCtx,otherLeftOccurrence,targetFirst⟩
  obtain ⟨rfl,rfl,rfl⟩ := leftOccurrence.same_occurrence otherLeftOccurrence
  rcases sourceSecond with ⟨rightSub,rightEnv,rightCtx,rightOccurrence,sourceSecond⟩
  rcases targetSecond with ⟨_otherSub,_otherEnv,_otherCtx,otherRightOccurrence,targetSecond⟩
  obtain ⟨rfl,rfl,rfl⟩ := rightOccurrence.same_occurrence otherRightOccurrence
  rcases leftOccurrence.last_departure with ⟨empty,_⟩ |
    ⟨leftParentPath,leftStep,leftTerm,leftSplit,leftLookup,leftRole⟩
  · exact (leftNonroot empty).elim
  rcases rightOccurrence.last_departure with ⟨empty,_⟩ |
    ⟨rightParentPath,rightStep,rightTerm,rightSplit,rightLookup,rightRole⟩
  · exact (rightNonroot empty).elim
  let leftPosition : Position current.erase := ⟨leftParentPath,by
    rw [←LTerm.erase_subterm,leftLookup];rfl⟩
  let rightPosition : Position current.erase := ⟨rightParentPath,by
    rw [←LTerm.erase_subterm,rightLookup];rfl⟩
  obtain ⟨sourceLeft,sourceLeftWord,_⟩ := Matches.observation site.net sourceMatches leftPosition
  obtain ⟨targetLeft,targetLeftWord,_⟩ := Matches.observation site.reduce targetMatches leftPosition
  obtain ⟨sourceRight,sourceRightWord,_⟩ := Matches.observation site.net sourceMatches rightPosition
  obtain ⟨targetRight,targetRightWord,_⟩ := Matches.observation site.reduce targetMatches rightPosition
  have actualLeftRole : SourceDeparture leftTerm leftStep
      (sourceEdge leftEnv leftCtx leftSub).fromPort := by
    have sourceFrom : (sourceEdge leftEnv leftCtx leftSub).fromPort=leftCtx := by cases leftSub <;> rfl
    rw [sourceFrom];exact leftRole
  have actualRightRole : SourceDeparture rightTerm rightStep
      (sourceEdge rightEnv rightCtx rightSub).fromPort := by
    have sourceFrom : (sourceEdge rightEnv rightCtx rightSub).fromPort=rightCtx := by cases rightSub <;> rfl
    rw [sourceFrom];exact rightRole
  obtain ⟨leftParent,leftParentAt⟩ := site.fan_control_access_kept control targetLeft
  obtain ⟨rightParent,rightParentAt⟩ := site.fan_control_access_kept control targetRight
  obtain ⟨leftEnd,leftEndAt⟩ := site.fan_control_access_kept control targetFirst.access
  obtain ⟨rightEnd,rightEndAt⟩ := site.fan_control_access_kept control targetSecond.access
  exact sourceFirst.fan_kept_piece_equality site flow root positive sourceMatches targetMatches principal
    targetFirst sourceSecond targetSecond actualLeftRole actualRightRole
    sourceLeft sourceRight targetLeft targetRight
    (by rw [sourceLeftWord];exact leftSplit) (by rw [sourceRightWord];exact rightSplit)
    (by rw [targetLeftWord];exact leftSplit) (by rw [targetRightWord];exact rightSplit)
    leftParent rightParent leftEnd rightEnd leftParentAt rightParentAt leftEndAt rightEndAt
end
end Lamping.AG
