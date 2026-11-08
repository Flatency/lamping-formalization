import Lamping.Lamping.DirectedMarkerSpineIncidence
import Lamping.Checks.UniformOldNodeLabelSuffix
import Lamping.Checks.PairedCurrentChainSourceLabels
namespace Lamping.Checks.DirectedMarkerSpineIncidenceChecks
open Lambda Lambda.Labelled
section Helpers
variable {source target t : LTerm}

private theorem rootvar_origin
    (origin : BetaIncomingReadingOrigin (.var stamp 0) argument site edge reader oldReader first last)
    (reading : PrerequisiteReadsDirected target reader edge forward) :
    edge=site ∧first=(if forward then site else site++[.arg]) := by
  cases origin with
  | resultFunction result fn =>
    have dir : forward=true := by
      cases forward with
      | true => rfl
      | false => have len:=congrArg List.length (reading.2.symm.trans (result.trans fn));simp at len
    simp only [dir,if_true]
    exact ⟨result,trivial⟩
  | resultLambda _ _ impossible => cases impossible
  | @copyFunction parent occurs copy read =>
    change subtermAt (.var 0) (parent++[.fn])=some (.var _) at occurs
    cases parent with
    | nil => cases occurs
    | cons s tail => cases s <;> cases occurs
  | @copyLambda q a b occurs copy read shape =>
    have empty : q=[] := by
      change subtermAt (.var 0) q=some (.var _) at occurs
      cases q with
      | nil => rfl
      | cons s tail => cases s <;> cases occurs
    have dir : forward=false := by
      cases forward with
      | false => rfl
      | true => have len:=congrArg List.length (read.trans reading.2);simp at len
    simp only [dir,Bool.false_eq_true,if_false]
    exact ⟨by simpa only [empty,List.append_nil] using copy,trivial⟩

private theorem leaf_two_cases
    (leaf : DirectedMarkerLeafOutput F source degree forward [s1,s2] word) :
    (leaf.pre=[] ∧leaf.site=s1 ∧leaf.after=[s2]) ∨
    (leaf.pre=[s1] ∧leaf.site=s2 ∧leaf.after=[]) := by
  have count:=congrArg List.length leaf.schedule
  simp only [List.length_append,List.length_cons,List.length_nil] at count
  have preSmall : leaf.pre.length≤1 := by omega
  cases preEq : leaf.pre with
  | nil =>
    have eq:=leaf.schedule
    rw [preEq,List.nil_append] at eq
    have parts:=List.cons.inj eq
    exact Or.inl ⟨rfl,parts.1.symm,parts.2.symm⟩
  | cons h tail =>
    have empty : tail=[] := by
      rw [preEq] at preSmall
      simp only [List.length_cons] at preSmall
      exact List.length_eq_zero_iff.mp (by omega)
    have eq:=leaf.schedule
    rw [preEq,empty] at eq
    have parts:=List.cons.inj eq
    have next:=List.cons.inj parts.2
    exact Or.inr ⟨by rw [empty,←parts.1],next.1.symm,next.2.symm⟩

private theorem same_redex_body
    (left : t.subterm p=some (.app beta (.lam alpha body) argument))
    (right : t.subterm p=some (.app b (.lam a other) arg)) : body=other := by
  have eq:=Option.some.inj (left.symm.trans right)
  injection eq with _ fn _
  injection fn

/-- Test-only finite schedule lemma. Every hypothesis below is an actual
lookup, step, unsafe old FIRST label, or unequal concrete word, not a
source chain/desired geometric conclusion. -/
private theorem forced_earlier_leaf
    (firstStep : StepAt s1 source middle) (_lastStep : StepAt s2 middle target)
    (firstRedex : source.subterm s1=some (.app b1 (.lam degree (.var v1 0)) arg1))
    (lastRedex : middle.subterm s2=some (.app b2 (.lam degree (.var v2 0)) arg2))
    (firstLookup : middle.subterm s1=some firstCurrent)
    (lastFirstLookup : middle.subterm (if forward then s2 else s2++[.arg])=some lastFirst)
    (lastFirstMarked : ¬lastFirst.label.OuterBarsSafe (fun x=>x≠degree))
    (different : word≠firstCurrent.label.readLetters forward)
    (leaf : DirectedMarkerLeafOutput F source degree forward [s1,s2] word) :
    leaf.continuation≠[] := by
  intro empty
  rcases leaf_two_cases leaf with ⟨preEq,siteEq,_⟩ | ⟨preEq,siteEq,_⟩
  · have middleEq : leaf.middle=source := by
      have history:=leaf.event.labels
      rw [preEq] at history
      exact history.deterministic (.nil _)
    have actualRedex : source.subterm s1=some (.app leaf.event.beta (.lam degree leaf.event.body) leaf.event.argument) :=
      (show source.subterm s1=leaf.middle.subterm leaf.site from by rw [middleEq,siteEq]).trans leaf.event.redex
    have bodyEq:=same_redex_body actualRedex firstRedex
    have origin:=leaf.origin
    rw [bodyEq] at origin
    obtain ⟨edgeEq,_⟩:=rootvar_origin origin leaf.reading
    have targetEq : leaf.target=middle := by
      have actualTurn:=leaf.event.turn
      rw [middleEq,siteEq] at actualTurn
      exact (History.cons actualTurn (History.nil _)).deterministic (.cons firstStep (.nil _))
    have actualLookup:=leaf.lookup
    rw [targetEq,edgeEq,siteEq] at actualLookup
    have nodeEq:=Option.some.inj (actualLookup.symm.trans firstLookup)
    have eq:=leaf.equation
    rw [nodeEq,empty,List.append_nil] at eq
    exact different eq
  · have middleEq : leaf.middle=middle := by
      have history:=leaf.event.labels
      rw [preEq] at history
      exact history.deterministic (.cons firstStep (.nil _))
    have actualRedex : middle.subterm s2=some (.app leaf.event.beta (.lam degree leaf.event.body) leaf.event.argument) :=
      (show middle.subterm s2=leaf.middle.subterm leaf.site from by rw [middleEq,siteEq]).trans leaf.event.redex
    have bodyEq:=same_redex_body actualRedex lastRedex
    have origin:=leaf.origin
    rw [bodyEq] at origin
    obtain ⟨_,firstEq⟩:=rootvar_origin origin leaf.reading
    have actualLookup:=leaf.firstLookup
    rw [middleEq,firstEq,siteEq] at actualLookup
    have nodeEq:=Option.some.inj (actualLookup.symm.trans lastFirstLookup)
    exact lastFirstMarked (nodeEq ▸ leaf.firstSafe)

end Helpers
namespace Nested
open UniformOldNodeLabelSuffixChecks
abbrev fresh : LTerm:=.lam (.atom 31) (.var (.atom 32) 0)
abbrev originalWrapped : LTerm:=.app (.atom 30) original fresh
abbrev sourceWrapped : LTerm:=.app (.atom 30) source fresh
abbrev middleForward : LTerm:=.app (.atom 30) middle fresh
abbrev targetForward : LTerm:=.app (.atom 30) target fresh
abbrev reverseInner : LTerm:=match source with |.app b fn arg=>.app b fn (WrappedSuccessfulChains.contractRoot arg) |t=>t
abbrev middleReverse : LTerm:=.app (.atom 30) reverseInner fresh
abbrev reverseResult : LTerm:=WrappedSuccessfulChains.contractRoot reverseInner
abbrev targetReverse : LTerm:=.app (.atom 30) reverseResult fresh
abbrev family : List Path:=[[.fn],[.fn,.arg]]

def forwardFirst : StepAt [.fn] sourceWrapped middleForward:=.fn (.root _ _ _ _)
def forwardLast : StepAt [.fn] middleForward targetForward:=.fn (.root _ _ _ _)
def reverseFirst : StepAt [.fn,.arg] sourceWrapped middleReverse:=.fn (.arg (.root _ _ _ _))
def reverseLast : StepAt [.fn] middleReverse targetReverse:=.fn (.root _ _ _ _)
def labelsForward : History [[.fn],[.fn]] sourceWrapped targetForward:=.cons forwardFirst (.cons forwardLast (.nil _))
def labelsReverse : History [[.fn,.arg],[.fn]] sourceWrapped targetReverse:=.cons reverseFirst (.cons reverseLast (.nil _))
def oldForward : Marked.RelativeOldHistory family [[.fn],[.fn]] (Marked.mark family sourceWrapped.erase)
    (.app [] (.lam (.var 0)) (.lam (.var 0))) :=
  .cons (.appL (.redRoot _ _ _)) (by decide) (.cons (.appL (.redRoot _ _ _)) (by decide) (.nil _))
def oldReverse : Marked.RelativeOldHistory family [[.fn,.arg],[.fn]] (Marked.mark family sourceWrapped.erase)
    (.app [] (.lam (.var 0)) (.lam (.var 0))) :=
  .cons (.appL (.redR (.redRoot _ _ _))) (by decide) (.cons (.appL (.redRoot _ _ _)) (by decide) (.nil _))

theorem selected (p : Path) (member : p∈family) : sourceWrapped.degreeAt p=some (.atom 10) := by
  rcases List.mem_cons.mp member with rfl | member
  · rfl
  · have eq:=List.mem_singleton.mp member;subst p;rfl

theorem sourceSafe : sourceWrapped.OuterBarsSafe (fun x=>x≠Label.atom 10) := ⟨trivial,source_safe,⟨trivial,trivial⟩⟩
theorem initial : INIT originalWrapped := by
  dsimp [originalWrapped,original,bare,caller,I,WrappedSuccessfulChains.I,initLabels,initFrom,nodeCount,fresh]
  simp [INIT,LTerm.labels,IsAtomic,Label.atom]
theorem originalClosed : Closed originalWrapped.erase := by
  change Scoped 0 (.app bare (.lam (.var 0)))
  simp [Scoped]
def globalPrefix : History [[.fn],[.fn],[.fn,.arg]] originalWrapped sourceWrapped:=
  .cons (.fn (.root _ _ _ _)) (.cons (.fn (.root _ _ _ _)) (.cons (.fn (.arg (.root _ _ _ _))) (.nil _)))
theorem sourceClosed : Closed sourceWrapped.erase:=globalPrefix.closed originalClosed

theorem forwardRead : PrerequisiteReadsDirected targetForward [] [.fn] true:=⟨Or.inl ⟨_,_,_,rfl,rfl⟩,rfl⟩
theorem reverseRead : PrerequisiteReadsDirected targetReverse [.fn] [.fn] false:=⟨Or.inr ⟨_,_,rfl,rfl⟩,rfl⟩
theorem forwardMarked : ¬target.label.OuterBarsSafe (fun x=>x≠Label.atom 10):=target_marked
theorem reverseMarked : ¬reverseResult.label.OuterBarsSafe (fun x=>x≠Label.atom 10) := by
  exact reverseLast.created_label_not_safe (by rfl) (current:=reverseResult) (by rfl) (Or.inl rfl)
def forwardSpine : DirectedMarkerSpine family sourceWrapped (.atom 10) true [[.fn],[.fn]] targetForward [] [.fn] :=
  oldForward.directed_marker_spine labelsForward selected sourceSafe .refl forwardRead rfl forwardMarked (by intro e h;cases h)
def reverseSpine : DirectedMarkerSpine family sourceWrapped (.atom 10) false [[.fn,.arg],[.fn]] targetReverse [] [.fn] :=
  oldReverse.directed_marker_spine labelsReverse selected sourceSafe .refl reverseRead rfl reverseMarked (by intro e h;cases h)

theorem reverseFirstMarked : ¬(WrappedSuccessfulChains.contractRoot (match source with |.app _ _ arg=>arg |t=>t)).label.OuterBarsSafe (fun x=>x≠Label.atom 10) := by
  exact reverseFirst.created_label_not_safe (by rfl) (current:=WrappedSuccessfulChains.contractRoot (match source with |.app _ _ arg=>arg |t=>t)) (by rfl) (Or.inl rfl)

theorem forward_nonempty : ∃leaf snapshot,
    Nonempty (SpineIncidenceProvenance family sourceWrapped (.atom 10) true forwardSpine (by rfl : targetForward.subterm [.fn]=some target) leaf snapshot) ∧leaf.continuation≠[] := by
  obtain ⟨leaf,snapshot,geometry⟩:=forwardSpine.incidence_leaf_output sourceClosed (by rfl : targetForward.subterm [.fn]=some target)
  refine ⟨leaf,snapshot,geometry,?_⟩
  exact forced_earlier_leaf (forward:=true) forwardFirst forwardLast (by rfl) (by rfl) (by rfl : middleForward.subterm [.fn]=some middle)
    (by rfl : middleForward.subterm [.fn]=some middle) unsafe_middle (by decide) leaf

theorem reverse_nonempty : ∃leaf snapshot,
    Nonempty (SpineIncidenceProvenance family sourceWrapped (.atom 10) false reverseSpine (by rfl : targetReverse.subterm [.fn]=some reverseResult) leaf snapshot) ∧leaf.continuation≠[] := by
  obtain ⟨leaf,snapshot,geometry⟩:=reverseSpine.incidence_leaf_output sourceClosed (by rfl : targetReverse.subterm [.fn]=some reverseResult)
  refine ⟨leaf,snapshot,geometry,?_⟩
  exact forced_earlier_leaf (forward:=false) reverseFirst reverseLast (by rfl) (by rfl) (by rfl : middleReverse.subterm [.fn,.arg]=some (WrappedSuccessfulChains.contractRoot (match source with |.app _ _ arg=>arg |t=>t)))
    (by rfl) reverseFirstMarked (by decide) leaf

theorem successful_readings : PrerequisiteChain targetForward [] [[.fn]] ∧PrerequisiteChain targetReverse [.fn] [[.fn]] :=
  ⟨.redex_app rfl,.redex_lam (p:=[]) rfl⟩

/-- SAME returned leaf and geometry witness: nonempty literal continuation,
actual suffix schedule, and exact projections are consumed together. -/
theorem forward_full_output : ∃leaf snapshot,
    ∃g : SpineIncidenceProvenance family sourceWrapped (.atom 10) true forwardSpine
      (by rfl : targetForward.subterm [.fn]=some target) leaf snapshot,
      leaf.continuation≠[] ∧g.continuationPieces.flatten=leaf.continuation ∧
      g.afterSites=leaf.after ∧History leaf.after leaf.target targetForward ∧
      ∃packet tail,g.creationFrames=packet::tail ∧packet.edge=leaf.edge ∧packet.first=leaf.first := by
  obtain ⟨leaf,snapshot,⟨g⟩,nonempty⟩:=forward_nonempty
  obtain ⟨packet,tail,eq,_,_,edgeEq,firstEq,_⟩:=g.base_frame_coordinates
  exact ⟨leaf,snapshot,g,nonempty,g.continuationPieces_eq,g.afterSites_eq,g.actual_suffix,packet,tail,eq,edgeEq,firstEq⟩

theorem reverse_full_output : ∃leaf snapshot,
    ∃g : SpineIncidenceProvenance family sourceWrapped (.atom 10) false reverseSpine
      (by rfl : targetReverse.subterm [.fn]=some reverseResult) leaf snapshot,
      leaf.continuation≠[] ∧g.continuationPieces.flatten=leaf.continuation ∧
      g.afterSites=leaf.after ∧History leaf.after leaf.target targetReverse ∧
      ∃packet tail,g.creationFrames=packet::tail ∧packet.edge=leaf.edge ∧packet.first=leaf.first := by
  obtain ⟨leaf,snapshot,⟨g⟩,nonempty⟩:=reverse_nonempty
  obtain ⟨packet,tail,eq,_,_,edgeEq,firstEq,_⟩:=g.base_frame_coordinates
  exact ⟨leaf,snapshot,g,nonempty,g.continuationPieces_eq,g.afterSites_eq,g.actual_suffix,packet,tail,eq,edgeEq,firstEq⟩

theorem same_original_different_schedules : INIT originalWrapped ∧Closed originalWrapped.erase ∧
    History [[.fn],[.fn],[.fn,.arg],[.fn],[.fn]] originalWrapped targetForward ∧
    History [[.fn],[.fn],[.fn,.arg],[.fn,.arg],[.fn]] originalWrapped targetReverse ∧
    ([[.fn],[.fn]] : List Path)≠[[.fn,.arg],[.fn]] :=
  ⟨initial,originalClosed,globalPrefix.append labelsForward,globalPrefix.append labelsReverse,by decide⟩
end Nested

namespace DistinctInherited
open PairedCurrentChainSourceLabelsChecks.NoninitialDistinct
abbrev markedBeforeLast : Marked:=.app [] (markedPiece [.fn,.fn,.body])
  (.red [[.arg]] (.app [[.arg,.fn,.body]] markedI (.var 0)) markedK)
abbrev markedFinal : Marked:=.app [] (markedPiece [.fn,.fn,.body]) (markedPiece [.arg,.fn,.body])
def firstLabels : History [[.fn]] source middle:=.cons firstStep (.nil _)
def firstOld : Marked.RelativeOldHistory F [[.fn]] (Marked.mark F source.erase) markedBeforeLast:=
  .cons (.appL (.redRoot _ _ _)) (by decide) (.nil _)
def lastEvent : SelectedOldTurn F source (.atom 6) [[.fn]] middle current [.arg] where
  markedBefore:=markedBeforeLast
  markedAfter:=markedFinal
  beforeOld:=firstOld
  reduction:=.appR (.redRoot _ _ _)
  member:=by decide
  labels:=firstLabels
  turn:=secondStep
  beta:=right.label
  body:=body
  argument:=argument
  redex:=rfl

theorem firstMarked : ¬newArgument.label.OuterBarsSafe (fun x=>x≠Label.atom 6) := by
  exact firstStep.created_label_not_safe (by rfl) (by rfl : middle.subterm leftStart=some newArgument) (by decide)
def earlier : DirectedMarkerSpine F source (.atom 6) false [[.fn]] middle [] leftStart :=
  firstOld.directed_marker_spine firstLabels selected sourceSafe .refl
    (show PrerequisiteReadsDirected middle leftStart leftStart false from ⟨Or.inr ⟨_,_,rfl,rfl⟩,rfl⟩)
    rfl firstMarked (by intro e h;cases h)
def inheritedSpine : DirectedMarkerSpine F source (.atom 6) false [[.fn],[.arg]] current [] leftStart :=
  .inherited lastEvent rfl rfl (.context (by rintro ⟨relative,impossible⟩;cases impossible)) (by decide) rfl earlier

theorem actual_inherited_output : ∃leaf snapshot,
    ∃g : SpineIncidenceProvenance F source (.atom 6) false inheritedSpine
      (by rfl : current.subterm leftStart=some newArgument) leaf snapshot,
      g.afterSites=leaf.after ∧g.continuationPieces.flatten=leaf.continuation ∧
      History leaf.after leaf.target current ∧
      ∃packet tail,g.creationFrames=packet::tail ∧packet.site=leaf.site ∧packet.last=leaf.last := by
  obtain ⟨leaf,snapshot,⟨g⟩⟩:=inheritedSpine.incidence_leaf_output sourceClosed (by rfl : current.subterm leftStart=some newArgument)
  obtain ⟨packet,tail,eq,_,siteEq,_,_,lastEq⟩:=g.base_frame_coordinates
  exact ⟨leaf,snapshot,g,g.afterSites_eq,g.continuationPieces_eq,g.actual_suffix,packet,tail,eq,siteEq,lastEq⟩

theorem actual_distinct_history : INIT original ∧History [[],[.fn],[.arg]] original current ∧
    PrerequisiteChain current leftStart leftEdges ∧leftStart≠rightStart ∧
    ¬middle.OuterBarsSafe (fun x=>x≠Label.atom 6) :=
  ⟨initial,prefixHistory.append labels,leftChain,by decide,unsafeMiddle⟩
end DistinctInherited

#print axioms DirectedMarkerSpine.incidence_leaf_output
#print axioms Nested.forward_nonempty
#print axioms Nested.reverse_nonempty
#print axioms Nested.initial
#print axioms Nested.successful_readings
#print axioms Nested.forward_full_output
#print axioms Nested.reverse_full_output
#print axioms Nested.same_original_different_schedules
#print axioms DistinctInherited.actual_inherited_output
#print axioms DistinctInherited.actual_distinct_history
#print axioms SpineIncidenceProvenance.base_frame_coordinates
#print axioms SpineIncidenceProvenance.actual_suffix
#print axioms SpineIncidenceProvenance.continuationPieces_eq
end Lamping.Checks.DirectedMarkerSpineIncidenceChecks
