import Lamping.Lambda.UniformOldOuterImageAlignment
import Lamping.Checks.PairedMarkerSpineReannotation
import Lamping.Checks.CrossPrefixExpandedArgumentConsumer

namespace Lamping.Checks.UniformOldOuterImageAlignmentChecks
open Lambda Lambda.Labelled AG

private def nodeAt (term : LTerm) (path : Path) : LTerm :=
  (term.subterm path).getD (.var (.atom 0) 0)

namespace CrossPrefix
open SingleUnsafeCopyFunctionAppInputsChecks
open ExpandedArgumentHistoryOriginsChecks.CrossPrefix

abbrev localSource : LTerm:=initLabels source.erase
abbrev localMiddle : LTerm:=match localSource with
  | .app stamp fn arg=>.app stamp (WrappedSuccessfulChains.contractRoot fn) arg
  | term=>term
abbrev localTarget : LTerm:=match localMiddle with
  | .app stamp fn arg=>.app stamp fn (WrappedSuccessfulChains.contractRoot arg)
  | term=>term
abbrev earlyLocal : LTerm:=nodeAt localMiddle earlyHead
abbrev lateLocal : LTerm:=nodeAt localTarget leftHead

def localBefore : History [[.fn]] localSource localMiddle:=.cons (.fn (.root _ _ _ _)) (.nil _)
def localFull : History [[.fn],[.arg]] localSource localTarget:=
  .cons (.fn (.root _ _ _ _)) (.cons (.arg (.root _ _ _ _)) (.nil _))

/-- Different actual OLD prefixes and distinct current local labels have
equal COMPLETE original-image keys. Both local histories use ONE SOURCE basis. -/
theorem actual_cross_prefix_key_alignment :
    INIT original ∧History [[.arg,.fn,.body],[]] original source ∧
    ([[.fn]] : List Path)≠[[.fn],[.arg]] ∧earlyHead≠leftHead ∧
    earlyLocal.label≠lateLocal.label ∧
    earlyLocal.label.letters.map (Letter.outerImageKey (initialRelabelling source 0))=
      lateLocal.label.letters.map (Letter.outerImageKey (initialRelabelling source 0)) := by
  have earlyAt : middle.subterm earlyHead=some copiedArgument:=rfl
  have earlyLocalAt : localMiddle.subterm earlyHead=some earlyLocal:=rfl
  have lateLocalAt : localTarget.subterm leftHead=some lateLocal:=rfl
  have equal:=event.beforeOld.local_outer_image_alignment event.final_old preHistory event.final_history
    localBefore localFull selected sourceSafe earlyAt leftLookup earlyLocalAt lateLocalAt rfl
  exact ⟨initial,prefixHistory,by decide,by decide,by decide,equal⟩
end CrossPrefix

namespace MultipleFrames
open UniformOldNodeLabelSuffixChecks
open DirectedMarkerSpineIncidenceChecks.Nested

/-- The complete parser consumes THIS returned geometry's actual local
reannotation, including its nonempty chronological continuation/tails. -/
theorem actual_forward_multiple_frame_groups :
    ∃leaf snapshot,
    ∃geometry : SpineIncidenceProvenance family sourceWrapped (.atom 10) true
      forwardSpine (by rfl : targetForward.subterm [.fn]=some target) leaf snapshot,
    ∃localTarget,∃localHistory : History [[.fn],[.fn]] (initLabels sourceWrapped.erase) localTarget,
    ∃paired : PairedSpineReannotation geometry localHistory (erase_initLabels sourceWrapped.erase).symm,
      2≤geometry.creationFrames.length ∧leaf.after≠[] ∧leaf.continuation≠[] ∧
      paired.localTailPieces≠[] ∧
      degreeGroups (.atom 10) target.label.letters=
        paired.current.label.expansionTokens (initialRelabelling sourceWrapped 0) := by
  obtain ⟨leaf,snapshot,geometry,multiple,after,continuation⟩:=
    PairedMarkerSpineReannotationChecks.Nested.forward_multiple_frames
  obtain ⟨localTarget,localHistory,_erased⟩:=
    lift_history labelsForward.betaHistory (initLabels sourceWrapped.erase) (erase_initLabels _)
  obtain ⟨paired⟩:=geometry.paired_reannotation localHistory (erase_initLabels _).symm
  have parsed:=oldForward.local_outer_image_groups labelsForward localHistory selected sourceSafe
    (by rfl : targetForward.subterm [.fn]=some target) paired.currentLookup
  exact ⟨leaf,snapshot,geometry,localTarget,localHistory,paired,multiple,after,continuation,
    paired.tails_nonempty multiple,parsed⟩

theorem actual_reverse_multiple_frame_groups :
    ∃leaf snapshot,
    ∃geometry : SpineIncidenceProvenance family sourceWrapped (.atom 10) false
      reverseSpine (by rfl : targetReverse.subterm [.fn]=some reverseResult) leaf snapshot,
    ∃localTarget,∃localHistory : History [[.fn,.arg],[.fn]] (initLabels sourceWrapped.erase) localTarget,
    ∃paired : PairedSpineReannotation geometry localHistory (erase_initLabels sourceWrapped.erase).symm,
      2≤geometry.creationFrames.length ∧leaf.after≠[] ∧leaf.continuation≠[] ∧
      paired.localTailPieces≠[] ∧
      degreeGroups (.atom 10) reverseResult.label.letters=
        paired.current.label.expansionTokens (initialRelabelling sourceWrapped 0) := by
  obtain ⟨leaf,snapshot,geometry,multiple,after,continuation⟩:=
    PairedMarkerSpineReannotationChecks.Nested.reverse_multiple_frames
  obtain ⟨localTarget,localHistory,_erased⟩:=
    lift_history labelsReverse.betaHistory (initLabels sourceWrapped.erase) (erase_initLabels _)
  obtain ⟨paired⟩:=geometry.paired_reannotation localHistory (erase_initLabels _).symm
  have parsed:=oldReverse.local_outer_image_groups labelsReverse localHistory selected sourceSafe
    (by rfl : targetReverse.subterm [.fn]=some reverseResult) paired.currentLookup
  exact ⟨leaf,snapshot,geometry,localTarget,localHistory,paired,multiple,after,continuation,
    paired.tails_nonempty multiple,parsed⟩
end MultipleFrames

namespace MarkedLast
abbrev I : Term:=.lam (.var 0)
abbrev Delta : Term:=.lam (.app (.var 0) (.var 0))
abbrev C : Term:=.lam (.app Delta (.var 0))
abbrev bare : Term:=.app (.lam (.app (.var 0) (.app (.var 0) I))) C
abbrev original : LTerm:=initLabels bare
abbrev first : LTerm:=WrappedSuccessfulChains.contractRoot original
abbrev second : LTerm:=WrappedSuccessfulChains.contractRoot first
abbrev source : LTerm:=match second with
  | .app stamp fn arg=>.app stamp fn (WrappedSuccessfulChains.contractRoot arg)
  | term=>term
abbrev middle : LTerm:=match source with
  | .app stamp fn arg=>.app stamp fn (WrappedSuccessfulChains.contractRoot arg)
  | term=>term
abbrev target : LTerm:=WrappedSuccessfulChains.contractRoot middle
abbrev F : List Path:=[[],[.arg]]
abbrev body : LTerm:=.app (.atom 11) (.var (.atom 12) 0) (.var (.atom 13) 0)
abbrev oldArgument : LTerm:=nodeAt source [.arg]
abbrev lastNode : LTerm:=nodeAt middle [.arg]
abbrev current : LTerm:=nodeAt target [.fn]
abbrev oldBeta : Label:=oldArgument.label

def globalPrefix : History [[],[],[.arg]] original source:=
  .cons (.root _ _ _ _) (.cons (.root _ _ _ _) (.cons (.arg (.root _ _ _ _)) (.nil _)))
def labels : History [[.arg],[]] source target:=
  .cons (.arg (.root _ _ _ _)) (.cons (.root _ _ _ _) (.nil _))
def markedMiddle : Marked:=.red [[]] (.app [] (.var 0) (.var 0))
  (.app [] (.lam (.var 0)) (.lam (.var 0)))
def markedTarget : Marked:=.app [] (.app [] (.lam (.var 0)) (.lam (.var 0)))
  (.app [] (.lam (.var 0)) (.lam (.var 0)))
def old : Marked.RelativeOldHistory F [[.arg],[]] (Marked.mark F source.erase) markedTarget:=
  .cons (.redR (.redRoot _ _ _)) (by decide) (.cons (.redRoot _ _ _) (by decide) (.nil _))

theorem initial : INIT original:=init_is_INIT _
theorem originalClosed : Closed original.erase:=by
  change Scoped 0 bare
  simp [Scoped]
theorem selected (p : Path) (member : p∈F) : source.degreeAt p=some (.atom 10) := by
  rcases List.mem_cons.mp member with rfl|member
  · rfl
  · have equal:=List.mem_singleton.mp member;subst p;rfl
theorem sourceSafe : source.OuterBarsSafe (fun d=>d≠Label.atom 10):=by
  dsimp [source,second,first,original,bare,C,I,Delta,WrappedSuccessfulChains.contractRoot,
    initLabels,initFrom,nodeCount,LTerm.contract,LTerm.subst,LTerm.single,LTerm.prepend,
    LTerm.rename,LTerm.lift,LTerm.label,Label.concat,Label.over,Label.under,Label.atom]
  simp only [LTerm.OuterBarsSafe,Label.OuterBarsSafe]
  decide

def readingOrigin : BetaIncomingReadingOrigin body lastNode [] [.fn] []
    [.fn,.body] [.fn,.body,.fn] [.arg] :=
  .copyFunction (parent:=[]) rfl rfl rfl
theorem reading : PrerequisiteReadsDirected target [] [.fn] true:=⟨Or.inl ⟨_,_,_,rfl,rfl⟩,rfl⟩
def chain : PrerequisiteChain target [] [[.fn],[.fn,.fn]]:=
  .app rfl (by intro stamp inner impossible;cases impossible) (.redex_app (p:=[.fn]) rfl)
theorem lastMarked : ¬lastNode.label.OuterBarsSafe (fun d=>d≠Label.atom 10):=by
  have step : StepAt [.arg] source middle:=.arg (.root _ _ _ _)
  have redex : source.subterm [.arg]=some
      (.app oldBeta (.lam (.atom 10) body) (nodeAt source [.arg,.arg])):=rfl
  exact step.created_label_not_safe redex (by rfl : middle.subterm [.arg]=some lastNode) (Or.inl rfl)
theorem firstSafe : (Label.atom 12).OuterBarsSafe (fun d=>d≠Label.atom 10):=by trivial
theorem oldBetaCompound : ¬IsAtomic oldBeta:=by
  rintro ⟨n,equal⟩
  have large : 1<oldBeta.length:=by decide
  rw [equal] at large
  simp [Label.atom,Label.length] at large

abbrev localSource : LTerm:=initLabels source.erase
abbrev localMiddle : LTerm:=match localSource with
  | .app stamp fn arg=>.app stamp fn (WrappedSuccessfulChains.contractRoot arg)
  | term=>term
abbrev localTarget : LTerm:=WrappedSuccessfulChains.contractRoot localMiddle
abbrev localCurrent : LTerm:=nodeAt localTarget [.fn]
def localLabels : History [[.arg],[]] localSource localTarget:=
  .cons (.arg (.root _ _ _ _)) (.cons (.root _ _ _ _) (.nil _))

/-- The entire five-key result retains unsafe LAST's beta image and BODY
image, rather than replacing it by its original last atom or dropping it. -/
theorem actual_marked_last_complete_keys :
    INIT original ∧Closed original.erase ∧History [[],[],[.arg]] original source ∧
    Marked.RelativeOldHistory F [[.arg],[]] (Marked.mark F source.erase) markedTarget ∧
    source.OuterBarsSafe (fun d=>d≠Label.atom 10) ∧
    middle.subterm [.arg]=some lastNode ∧
    ¬lastNode.label.OuterBarsSafe (fun d=>d≠Label.atom 10) ∧
    PrerequisiteReadsDirected target [] [.fn] true ∧
    PrerequisiteChain target [] [[.fn],[.fn,.fn]] ∧
    localCurrent.label.expansionTokens (initialRelabelling source 0)=
      [.inl (Label.atom 12).letters,.inr (.under (.atom 10)),.inl oldBeta.letters,
        .inr (.over (.atom 10)),.inl (Label.atom 11).letters] ∧
    degreeGroups (.atom 10) current.label.letters=
      localCurrent.label.expansionTokens (initialRelabelling source 0) ∧
    localCurrent.label.letters.map (Letter.outerImageKey (initialRelabelling source 0))=
      [.inl (.atom 12),.inr false,.inl oldBeta,.inr true,.inl (.atom 11)] := by
  have parsed:=old.local_outer_image_groups labels localLabels selected sourceSafe
    (by rfl : target.subterm [.fn]=some current) (by rfl : localTarget.subterm [.fn]=some localCurrent)
  exact ⟨initial,originalClosed,globalPrefix,old,sourceSafe,rfl,lastMarked,reading,chain,rfl,parsed,rfl⟩
end MarkedLast

#print axioms CrossPrefix.actual_cross_prefix_key_alignment
#print axioms MultipleFrames.actual_forward_multiple_frame_groups
#print axioms MultipleFrames.actual_reverse_multiple_frame_groups
#print axioms MarkedLast.globalPrefix
#print axioms MarkedLast.old
#print axioms MarkedLast.readingOrigin
#print axioms MarkedLast.chain
#print axioms MarkedLast.lastMarked
#print axioms MarkedLast.oldBetaCompound
#print axioms MarkedLast.actual_marked_last_complete_keys
end Lamping.Checks.UniformOldOuterImageAlignmentChecks
