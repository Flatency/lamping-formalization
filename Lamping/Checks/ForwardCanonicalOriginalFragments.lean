import Lamping.Lamping.ForwardCanonicalOriginalFragments
import Lamping.Checks.CrossPrefixExpandedArgumentConsumer

namespace Lamping.Checks.ForwardCanonicalOriginalFragmentsChecks
open Graph Lambda Lambda.Labelled AG SyntaxIncidence
open SingleUnsafeCopyFunctionAppInputsChecks
open ExpandedArgumentHistoryOriginsChecks.CrossPrefix
open CrossPrefixExpandedArgumentConsumer

private theorem unsafe_split_unique {A : Type} (P : A→Prop)
    {bs cs : List A} {x y : A} {as ds : List A}
    (same : bs++x::as=cs++y::ds)
    (leftSafe : ∀a∈bs,P a) (rightSafe : ∀a∈cs,P a)
    (leftBad : ¬P x) (rightBad : ¬P y) : bs=cs ∧x=y ∧as=ds := by
  induction bs generalizing cs with
  | nil =>
    cases cs with
    | nil => exact ⟨rfl,List.cons.inj same⟩
    | cons c rest =>
      have head : x=c := (List.cons.inj same).1
      exact False.elim (leftBad (head ▸ rightSafe c (List.mem_cons_self)))
  | cons b rest ih =>
    cases cs with
    | nil =>
      have head : b=y := (List.cons.inj same).1
      exact False.elim (rightBad (head ▸ leftSafe b (List.mem_cons_self)))
    | cons c tail =>
      have head : b=c := (List.cons.inj same).1
      have ends:=ih (List.cons.inj same).2
        (fun a member=>leftSafe a (List.mem_cons_of_mem b member))
        (fun a member=>rightSafe a (List.mem_cons_of_mem c member))
      exact ⟨by rw [head,ends.1],ends.2⟩

private theorem cut_bad
    (cut : ActualUnsafeMarkerCut f ps s t degree start edges) :
    ¬degreeReadSafe degree (t.labelAt cut.edge) := by
  intro good
  exact cut.marked (good cut.node.label (by simp only [LTerm.labelAt,cut.lookup,Option.map_some]))

private theorem cut_data
    (left right : ActualUnsafeMarkerCut f ps s t degree start edges) :
    left.before=right.before ∧left.edge=right.edge ∧left.after=right.after :=
  unsafe_split_unique (degreeReadSafe degree ∘t.labelAt) (left.split.symm.trans right.split)
    left.safeBefore right.safeBefore (cut_bad left) (cut_bad right)

private theorem app_read_true
    (read : PrerequisiteReadsDirected t reader edge forward)
    (lookup : t.subterm edge=some (.app stamp fn arg)) : forward=true := by
  cases forward with
  | true => rfl
  | false =>
    rcases read.1 with ⟨a,f,x,atApp,split⟩ | ⟨a,b,atLam,split⟩
    · have length:=congrArg List.length (split.symm.trans read.2)
      simp at length
    · have lamAt : t.subterm edge=some (.lam a b) := read.2.symm ▸ atLam
      have impossible:=Option.some.inj (lookup.symm.trans lamAt)
      cases impossible

private theorem two_schedule {pre suffix : List Path} {site : Path}
    (schedule : [[.fn],[.arg]]=(pre++[site])++suffix) :
    (pre=[] ∧site=[.fn] ∧suffix=[[.arg]]) ∨
    (pre=[[.fn]] ∧site=[.arg] ∧suffix=[]) := by
  have sizes:=congrArg List.length schedule
  simp only [List.length_append,List.length_cons,List.length_nil] at sizes
  cases pre with
  | nil =>
    simp only [List.nil_append,List.singleton_append,List.cons.injEq] at schedule
    exact Or.inl ⟨rfl,schedule.1.symm,schedule.2.symm⟩
  | cons head tail =>
    have te : tail=[]:=List.length_eq_zero_iff.mp (by simp only [List.length_cons] at sizes;omega)
    have se : suffix=[]:=List.length_eq_zero_iff.mp (by simp only [List.length_cons] at sizes;omega)
    subst tail
    rw [se] at schedule
    simp only [List.cons_append,List.nil_append,List.append_nil,List.cons.injEq] at schedule
    exact Or.inr ⟨congrArg (fun p : Path=>[p]) schedule.1.symm,schedule.2.1.symm,se⟩

private theorem origin_below {b a : LTerm} {site edge reader oldReader first last : Path}
    (origin : BetaIncomingReadingOrigin b a site edge reader oldReader first last) :
    ∃relative,edge=site++relative := by
  cases origin with
  | resultFunction eq _ => exact ⟨[],by simpa only [List.append_nil] using eq⟩
  | resultLambda eq _ _ => exact ⟨[],by simpa only [List.append_nil] using eq⟩
  | copyFunction _ eq _ => exact ⟨_,eq⟩
  | copyLambda _ eq _ _ => exact ⟨_,eq⟩

private theorem empty_coordinates {s t : LTerm} {ps : List Path}
    {labels : History ps s t}
    (trace : BetaNodeHistoryPreimage labels p old) (empty : ps=[]) : p=old := by
  subst ps
  cases trace
  rfl

private theorem one_uncreated {s t body argument : LTerm} {ps : List Path}
    {labels : History ps s t}
    (trace : UncreatedNodeHistoryPreimage labels p old) (single : ps=[site])
    (redex : s.subterm site=some (.app beta (.lam alpha body) argument)) :
    ¬BetaCreatedIncoming body site p := by
  subst ps
  cases trace with
  | one actual origin uncreated tail =>
    cases tail
    have same:=Option.some.inj (actual.symm.trans redex)
    cases same
    exact uncreated

private theorem early_signature
    {cut : ActualUnsafeMarkerCut F [[.fn],[.arg]] source target (.atom 6) earlyStart earlyEdges}
    {snapshot} {canonical : CanonicalAfterFarOutput event.final_history cut snapshot}
    (out : CanonicalRecentLastOutput event.final_history cut snapshot canonical)
    (position : cut.edge=earlyHead) :
    out.recent.packet.pre=[] ∧out.recent.packet.site=[.fn] ∧out.recent.suffixSites=[[.arg]] := by
  rcases two_schedule out.recent.schedule with good |late
  · exact good
  · obtain ⟨_pre,site,suffix⟩:=late
    have head:=empty_coordinates out.recent.uncreatedSuffix.to_node suffix
    obtain ⟨relative,inside⟩:=origin_below out.recent.packet.origin
    rw [←head,site,position] at inside
    change [.fn,.fn,.fn]=[.arg]++relative at inside
    cases inside

private theorem late_signature
    {cut : ActualUnsafeMarkerCut F [[.fn],[.arg]] source target (.atom 6) leftStart es}
    {snapshot} {canonical : CanonicalAfterFarOutput event.final_history cut snapshot}
    (out : CanonicalRecentLastOutput event.final_history cut snapshot canonical)
    (position : cut.edge=leftHead) :
    out.recent.packet.pre=[[.fn]] ∧out.recent.packet.site=[.arg] ∧out.recent.suffixSites=[] := by
  rcases two_schedule out.recent.schedule with early |good
  · obtain ⟨pre,site,suffix⟩:=early
    have history : History [[.fn]] source out.recent.packet.target := by
      have actual:=out.recent.packet.event.final_history
      exact Eq.mp (congrArg (fun sites : List Path=>History sites source out.recent.packet.target)
        (show out.recent.packet.pre++[out.recent.packet.site]=[[.fn]] from by rw [pre,site];rfl)) actual
    have targetEq:=history.deterministic preHistory
    have redex : out.recent.packet.target.subterm [.arg]=some
        (.app event.beta (.lam (.atom 6) body) argument) := by rw [targetEq];exact event.redex
    have noCreated:=one_uncreated out.recent.uncreatedSuffix suffix redex
    exact False.elim (noCreated (by rw [position];decide))
  · exact good

private theorem forward_trace
    {f ps : List Path} {s t node : LTerm} {degree : Label} {forward : Bool}
    {before : List (Option Label)} {edge : Path}
    {spine : DirectedMarkerSpine f s degree forward ps t before edge}
    {lookup : t.subterm edge=some node}
    {leaf : DirectedMarkerLeafOutput f s degree forward ps (node.label.readLetters forward)}
    {snapshot : IncomingIncidenceSnapshot t edge}
    {geometry : SpineIncidenceProvenance f s degree forward spine lookup leaf snapshot}
    (recent : RecentSpineFrame geometry) (labels : History ps s t)
    {lastNode : LTerm} {far : ProperPosition s} {farEdges : List Path}
    (out : ExpandedLastOriginalEndpoints f s recent.packet.middle degree recent.packet.event.labels
      (recent.packet.frame.edges.getLastD []) lastNode forward far farEdges)
    (positive : forward=true) : BetaNodeHistoryPreimage labels edge out.oldEdge := by
  subst forward
  exact recent.forward_expanded_last_history_preimage labels out

/-- The cuts and both geometries here come directly from the NEW natural
high producer, not from independent reruns of the earlier fixture. -/
theorem actual_distinct_prefix_canonical_comparison :
    ∃lc : ActualUnsafeMarkerCut F [[.fn],[.arg]] source target (.atom 6) earlyStart earlyEdges,
    ∃rc : ActualUnsafeMarkerCut F [[.fn],[.arg]] source target (.atom 6) leftStart es,
    ∃ls rs,
    ∃left : CanonicalAfterFarOutput event.final_history lc ls,
    ∃right : CanonicalAfterFarOutput event.final_history rc rs,
    ∃comparison : ForwardCanonicalOriginalComparison sourceClosed left right,
      lc.edge=earlyHead ∧rc.edge=leftHead ∧lc.forward=true ∧rc.forward=true ∧
      comparison.leftOutput.recent.packet.pre=[] ∧
      comparison.leftOutput.recent.packet.site=[.fn] ∧
      comparison.leftOutput.recent.suffixSites=[[.arg]] ∧
      comparison.rightOutput.recent.packet.pre=[[.fn]] ∧
      comparison.rightOutput.recent.packet.site=[.arg] ∧
      comparison.rightOutput.recent.suffixSites=[] ∧
      comparison.leftOutput.original.oldEdge=[.fn,.arg] ∧
      comparison.rightOutput.original.oldEdge=[.arg,.arg] ∧
      comparison.leftOutput.original.oldEdge≠comparison.rightOutput.original.oldEdge ∧
      comparison.leftOutput.original.original.label=comparison.rightOutput.original.original.label ∧
      SuccessfulEndpointIso source sourceClosed
        (some comparison.leftOutput.original.fromVertex) (some comparison.rightOutput.original.fromVertex) ∧
      SuccessfulEndpointIso source sourceClosed
        (some comparison.leftOutput.original.toVertex) (some comparison.rightOutput.original.toVertex) := by
  classical
  obtain ⟨iso⟩:=actual_equal_heads_and_parent_iso.2.2
  rcases actual_parent_canonical_forward_original_comparison initial prefixHistory sourceClosed
    event.final_old event.final_history selected sourceSafe earlyChain leftChain iso with safe | cuts
  · exact False.elim (copiedMarked (safe.1 earlyHead (by decide) copiedArgument.label rfl))
  · obtain ⟨lc,rc,_len,_front,_head,_back,emptyOr⟩:=cuts
    obtain ⟨_before,le,la⟩:=cut_data lc earlyCut
    obtain ⟨_rightBefore,re,ra⟩:=cut_data rc lateCut
    have leftMore : lc.after≠[] := by rw [la];decide
    have leftTrue : lc.forward=true := app_read_true lc.reading (by rw [le];rfl)
    have rightTrue : rc.forward=true := app_read_true rc.reading (by rw [re];rfl)
    rcases emptyOr with empty | more
    · exact False.elim (leftMore empty.1)
    · obtain ⟨_lm,_rm,ls,rs,left,right,_good,produce⟩:=more
      obtain ⟨comparison⟩:=produce leftTrue
      obtain ⟨ep,et,ef⟩:=early_signature comparison.leftOutput le
      obtain ⟨lp,lt,lf⟩:=late_signature comparison.rightOutput re
      have earlyTrace : BetaNodeHistoryPreimage event.final_history earlyHead comparison.leftOutput.original.oldEdge := by
        have actual:=forward_trace comparison.leftOutput.recent event.final_history comparison.leftOutput.original leftTrue
        simpa only [le] using actual
      have lateTrace : BetaNodeHistoryPreimage event.final_history leftHead comparison.rightOutput.original.oldEdge := by
        have actual:=forward_trace comparison.rightOutput.recent event.final_history comparison.rightOutput.original rightTrue
        simpa only [re] using actual
      have earlyOld:=earlyTrace.unique earlyWholeTrace
      have lateOld:=lateTrace.unique lateWholeTrace
      refine ⟨lc,rc,ls,rs,left,right,comparison,le,re,leftTrue,rightTrue,ep,et,ef,lp,lt,lf,earlyOld,lateOld,?_,
        comparison.labelEq,comparison.sourceIso,comparison.targetIso⟩
      rw [earlyOld,lateOld]
      decide

/-- The same distinct-prefix high output gives original literal pieces
under the genuine SOURCE Joint IH, which this fixture does not assume true. -/
theorem actual_distinct_prefix_original_pieces
    {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
    {g : Net signature N B W} {root : B}
    (selection : OccurrenceFragmentSelection source g root)
    (joint : JointRepresentation sourceClosed selection) :
    ∃lc : ActualUnsafeMarkerCut F [[.fn],[.arg]] source target (.atom 6) earlyStart earlyEdges,
    ∃rc : ActualUnsafeMarkerCut F [[.fn],[.arg]] source target (.atom 6) leftStart es,
    ∃ls rs,
    ∃left : CanonicalAfterFarOutput event.final_history lc ls,
    ∃right : CanonicalAfterFarOutput event.final_history rc rs,
    ∃comparison : ForwardCanonicalOriginalComparison sourceClosed left right,
      comparison.leftOutput.original.oldEdge=[.fn,.arg] ∧
      comparison.rightOutput.original.oldEdge=[.arg,.arg] ∧
      (selection comparison.leftOutput.originalEdge).fragment.segments=
        (selection comparison.rightOutput.originalEdge).fragment.segments := by
  obtain ⟨lc,rc,ls,rs,left,right,comparison,_le,_re,_lp,_rp,_ep,_et,_ef,_pp,_pt,_pf,oldL,oldR,_distinct,_labels,_si,_ti⟩:=
    actual_distinct_prefix_canonical_comparison
  exact ⟨lc,rc,ls,rs,left,right,comparison,oldL,oldR,comparison.source_fragments selection joint.2⟩

#print axioms actual_distinct_prefix_canonical_comparison
#print axioms actual_distinct_prefix_original_pieces
end Lamping.Checks.ForwardCanonicalOriginalFragmentsChecks
