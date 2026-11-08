import Lamping.Lamping.ActualCopyOverlapOperandOrigins
import Lamping.Checks.FunctionWrappedReachable
import Lamping.Checks.WrappedSuccessfulChains
import Lamping.Lamping.ActualWindowResidualOccurrence

namespace Lamping.Checks.ActualCopyOverlapOperandOrigins
open AG Graph Lambda Lambda.Labelled Lambda.Labelled.InteriorSourceBlock
open FunctionWrappedReachable WrappedSuccessfulChains

private noncomputable abbrev site := FunctionWrappedReachable.concrete.site
private abbrev original := WrappedSuccessfulChains.original
private abbrev current := WrappedSuccessfulChains.current
private def chain : PrerequisiteChain current [.fn] [[.fn]] := .redex_lam (p:=[]) rfl
private abbrev member : {p : Path //p∈WrappedSuccessfulChains.rootEdges} := ⟨[.fn],by simp [rootEdges]⟩
private noncomputable abbrev cut := cutFragment site.net (pathPartition (Schema.beta 0)
  FunctionWrappedReachable.concrete.Inside) site.closed

private theorem spine_nonempty
    (spine : DirectedMarkerSpine F source degree d ps target before edge) : ps≠[] := by
  cases spine <;> intro empty <;>
    have lengths := congrArg List.length empty <;>
    simp only [List.length_append,List.length_cons,List.length_nil] at lengths <;> omega

private theorem one_step_leaf_edge
    {spine : DirectedMarkerSpine F source degree d ps target before edge}
    {lookup : target.subterm edge=some node}
    {leaf : DirectedMarkerLeafOutput F source degree d ps (node.label.readLetters d)}
    {snapshot : IncomingIncidenceSnapshot target edge}
    (geometry : SpineIncidenceProvenance F source degree d spine lookup leaf snapshot)
    (single : ps=[p]) : leaf.edge=edge := by
  cases geometry with
  | inherited event lookup oldLookup origin uncreated same earlier earlierGeometry snap transport =>
    apply False.elim
    apply spine_nonempty earlier
    apply List.length_eq_zero_iff.mp
    have lengths := congrArg List.length single
    simp only [List.length_append,List.length_cons,List.length_nil] at lengths
    omega
  | safe => rfl
  | marked event reading lookup origin segment beforeEq beforeSafe firstLookup firstMarked lastLookup lastSourceLookup lastTrace earlier earlierGeometry marks formula equation snap fr =>
    apply False.elim
    apply spine_nonempty earlier
    apply List.length_eq_zero_iff.mp
    have lengths := congrArg List.length single
    simp only [List.length_append,List.length_cons,List.length_nil] at lengths
    omega

private theorem actual_packet :
    ∃packet : SpineCreationPacket [[.fn]] original (.atom 2) false,
      packet.pre=[] ∧packet.site=[.fn] ∧packet.edge=[.fn] := by
  have old : Marked.RelativeOldHistory [[.fn]] [[.fn]]
      (Marked.mark [[.fn]] original.erase) FunctionWrappedReachable.endpoint := by
    have value := (Marked.relativeOld_iff_relative
      (Marked.selected_mark (site.betaSyntaxFiber (.inl ()) original.erase) original.erase)).mpr
        FunctionWrappedReachable.relative
    have fiber : site.betaSyntaxFiber (.inl ()) original.erase=[[.fn]] := FunctionWrappedReachable.actual_fiber
    rw [fiber] at value
    exact value
  have selected (p : Path) (inside : p∈([[.fn]] : List Path)) : original.degreeAt p=some (.atom 2) := by
    have eq := List.mem_singleton.mp inside
    subst p
    rfl
  obtain ⟨body,lookup⟩ := WrappedSuccessfulChains.function_lambda_lookup
  have markedLabel : ¬(LTerm.lam WrappedSuccessfulChains.functionLabel body).label.OuterBarsSafe
      (fun d=>d≠Labelled.Label.atom 2) := by
    intro safe
    exact safe.1 rfl
  have reading : PrerequisiteReadsDirected current [.fn] [.fn] false := WrappedSuccessfulChains.last_read
  let spine := old.directed_marker_spine WrappedSuccessfulChains.actualHistory selected
    (WrappedSuccessfulChains.initial.outerBarsSafe _) .refl reading lookup markedLabel
    (by intro e inside;cases inside)
  obtain ⟨leaf,snapshot,⟨geometry⟩⟩ := spine.incidence_leaf_output WrappedSuccessfulChains.sourceClosed lookup
  have leafEdge := one_step_leaf_edge geometry rfl
  have lengths := congrArg List.length leaf.schedule
  simp only [List.length_append,List.length_cons,List.length_nil] at lengths
  have preNil : leaf.pre=[] := List.length_eq_zero_iff.mp (by omega)
  have afterNil : leaf.after=[] := List.length_eq_zero_iff.mp (by omega)
  have leafSite : leaf.site=[.fn] := by
    have schedule := leaf.schedule
    rw [preNil,afterNil,List.nil_append] at schedule
    exact (List.cons.inj schedule).1.symm
  obtain ⟨packet,_tail,_frames,preEq,siteEq,edgeEq,_first,_last⟩ := geometry.base_frame_coordinates
  exact ⟨packet,preEq.trans preNil,siteEq.trans leafSite,edgeEq.trans leafEdge⟩

/-- Original closed encoding, actual safe packet, nonvacuous atom3 body,
SAME producer ECR, FALSE APP/ARG complete routes and actual assignment cut. -/
theorem actual_closed_copy_overlap_operand_origins :
    Closed FunctionWrappedReachable.term ∧
    GraphStep (.beta 0) (ActualNet.initial FunctionWrappedReachable.term)
      (ActualNet.ofNet site.reduce) ∧
    ∃ (targetSelection : OccurrenceFragmentSelection current site.reduce (.inl ()))
      (localTarget : LTerm) (edge : BetaEdge site.net)
      (selection : SourceEdgeSelection (initLabels original.erase) site.net (.inl ()))
      (out : EvaluatedChainResiduals site (localTarget:=localTarget) edge selection targetSelection chain)
      (packet : SpineCreationPacket [[.fn]] original (.atom 2) false)
      (frame : PairedSpineCreationFrame packet (initLabels original.erase))
      (own : WindowOccurrences (initLabels original.erase) [[.fn]] 3 true false),
      packet.pre=[] ∧packet.site=[.fn] ∧packet.edge=[.fn] ∧frame.target=localTarget ∧
      frame.body=.var (.atom 3) 0 ∧frame.alpha=.atom 2 ∧frame.beta=.atom 1 ∧
      own.left.position=[.fn] ∧own.position=[.fn,.fn,.body] ∧own.node=.var (.atom 3) 0 ∧
      BetaNodeHistoryPreimage frame.prefixLabels packet.site own.left.position ∧
      BetaNodeHistoryPreimage frame.prefixLabels (packet.site++[.fn]) (own.left.position++[.fn]) ∧
      (∃ (ctx : SourcePort) (argId : Label),
        SelectedSourceRoute (sourceEdges [] .external (initLabels original.erase))
          (SelectedDegree (initLabels original.erase) [[.fn]]) ctx frame.beta (.appContext own.left.beta) ∧
        SelectedSourceRoute (sourceEdges [] .external (initLabels original.erase))
          (SelectedDegree (initLabels original.erase) [[.fn]])
          (.appFn own.left.beta) frame.alpha (.lamContext frame.alpha) ∧
        SelectedSourceRoute (sourceEdges [] .external (initLabels original.erase))
          (SelectedDegree (initLabels original.erase) [[.fn]])
          (.lamBody frame.alpha) (.atom 3) (.lamBind frame.alpha) ∧
        SelectedSourceRoute (sourceEdges [] .external (initLabels original.erase))
          (SelectedDegree (initLabels original.erase) [[.fn]])
          (.appArg own.left.beta) frame.argument.label (.lamContext argId)) ∧
      (sourceEdge own.env own.ctx own.node).fromPort=.lamBody (.atom 2) ∧
      (sourceEdge own.env own.ctx own.node).toPort=.lamBind (.atom 2) ∧
      frame.marker=.under (.atom 2) ∧
      frame.tail=[.under (.atom 2),.atom 3,.over (.atom 2)]++frame.beta.letters.reverse ∧
      (out.node member)=frame.current ∧
      ∃cutAt : BetaResidualOccurrence site edge
        ((targetSelection (actualChainPosition chain member)).fragment.segments.map
          (plugEnd cut.label (Schema.beta 0).right.net.label).invFun)
        (selection.evalLabel edge (out.node member).label) (.inr (.inl (.inr (.inr true))))
        ((frame.beta.letters++[Letter.over frame.alpha]).flatMap
          (Letter.sourceWord selection.atomWord edge.principal edge.reverseRoute)).length,
        cutAt.oldBefore=([Letter.atom 1,Letter.over (.atom 2)]).flatMap
          (Letter.sourceWord selection.atomWord edge.principal edge.reverseRoute) ∧
        ∃ (a b seam : Context) (lc rc : Nat),
          PlugLabelling cut (Schema.beta 0).right.net
            ((targetSelection (actualChainPosition chain member)).fragment.segments.map
              (plugEnd cut.label (Schema.beta 0).right.net.label).invFun) a b ∧
          FixedBetaDetourBlocks edge (cutAt.oldBefore++[site.outsideEnd (.inr (.inl (.inr (.inr true))))]) a seam lc ∧
          FixedBetaDetourBlocks edge (site.outsideEnd (.inr (.inl (.inr (.inr true))))::cutAt.oldAfter) seam b rc := by
  refine ⟨FunctionWrappedReachable.closed,FunctionWrappedReachable.actual_beta_step,?_⟩
  obtain ⟨targetSelection⟩ := FunctionWrappedReachable.beta_matches.occurrence_fragment_selection WrappedSuccessfulChains.targetClosed
  obtain ⟨flow⟩ := encode_flowBalance FunctionWrappedReachable.term 0
  obtain ⟨balance⟩ := encode_indexed_balance FunctionWrappedReachable.term 0
  have matching : Matches site.net (.inl ()) original.erase :=
    FunctionWrappedReachable.concrete.sourceIso.matches
      (encode_closed_matches FunctionWrappedReachable.term FunctionWrappedReachable.closed 0)
  obtain ⟨localTarget,history,_erase,_matching,edge,selection,geometry,all⟩ :=
    site.beta_evaluated_chain_residuals (source:=original) (target:=current) FunctionWrappedReachable.closed matching
      (FunctionWrappedReachable.concrete.sourceIso.rootInputs
        (encode_closed_independence FunctionWrappedReachable.term FunctionWrappedReachable.closed 0).rootInputs)
      (FunctionWrappedReachable.concrete.sourceIso.flowBalance flow) rfl
      (FunctionWrappedReachable.concrete.sourceIso.indexed_balance balance) rfl
      (FunctionWrappedReachable.concrete.sourceIso.transparency
        (encode_closed_transparency FunctionWrappedReachable.term FunctionWrappedReachable.closed 0))
      FunctionWrappedReachable.relative (by simp [FunctionWrappedReachable.endpoint,Marked.Normal])
      WrappedSuccessfulChains.actualHistory targetSelection
  obtain ⟨out⟩ := all chain
  obtain ⟨packet,packetPre,packetSite,packetEdge⟩ := actual_packet
  have packetHistory : History (packet.pre++[packet.site]) (initLabels original.erase) localTarget := by
    rw [packetPre,packetSite,List.nil_append]
    exact history
  obtain ⟨frame,frameTarget,owns⟩ := packet.actual_copy_overlap_operand_origins packetHistory (packetEdge.trans packetSite.symm)
  have nilHistory : History [] (initLabels original.erase) frame.middle := by
    simpa only [packetPre] using frame.prefixLabels
  have middleEq := nilHistory.deterministic (.nil _)
  have atSite : (initLabels original.erase).subterm packet.site=
      some (.app frame.beta (.lam frame.alpha frame.body) frame.argument) :=
    (congrArg (fun t : LTerm=>t.subterm packet.site) middleEq).symm.trans frame.redex
  have atNamed : (initLabels original.erase).subterm [.fn]=
      some (.app frame.beta (.lam frame.alpha frame.body) frame.argument) :=
    (congrArg (fun p=>(initLabels original.erase).subterm p) packetSite).symm.trans atSite
  have shapes := LTerm.app.inj (Option.some.inj atNamed)
  have lambdas := LTerm.lam.inj shapes.2.1
  have betaEq : frame.beta=.atom 1 := shapes.1.symm
  have alphaEq : frame.alpha=.atom 2 := lambdas.1.symm
  have bodyEq : frame.body=.var (.atom 3) 0 := lambdas.2.symm
  obtain ⟨own,routeCtx,argId,_leftDegree,_rightDegree,_samePos,position,node,_oldBody,
    appTrace,fnTrace,appRoute,fnRoute,bodyRoute,argRoute,_lastAtom,_argLambda,_firstNode,_lastNode,
    fromPort,toPort,marker,tail,_readingWord,word,_globalDegree⟩ := owns 3 bodyEq
  have qEq : own.left.position=[.fn] := List.mem_singleton.mp own.left.member
  have cellEq : own.position=[.fn,.fn,.body] := by simpa only [qEq] using position
  have atFrame : localTarget.subterm packet.edge=some frame.current :=
    (congrArg (fun t : LTerm=>t.subterm packet.edge) frameTarget).symm.trans frame.lookup
  have atNamedFrame : localTarget.subterm [.fn]=some frame.current :=
    (congrArg (fun p=>localTarget.subterm p) packetEdge).symm.trans atFrame
  have nodeEq : out.node member=frame.current := Option.some.inj ((out.lookup member).symm.trans atNamedFrame)
  have window : (out.node member).label.letters=
      frame.beta.letters++[InteriorSourceBlock.bar true frame.alpha,.atom 3,
        InteriorSourceBlock.bar false frame.alpha]++frame.argument.label.letters := by
    rw [nodeEq]
    exact word
  have old := (Marked.relativeOld_iff_relative
    (Marked.selected_mark (site.betaSyntaxFiber (.inl ()) original.erase) original.erase)).mpr FunctionWrappedReachable.relative
  obtain ⟨_atomTail,_atomEq,cutAt,beforeEq,_afterEq,streams⟩ :=
    out.interior_window_raw_cut site matching edge geometry selection old history targetSelection chain member window
  have before : cutAt.oldBefore=([Letter.atom 1,Letter.over (.atom 2)]).flatMap
      (Letter.sourceWord selection.atomWord edge.principal edge.reverseRoute) := by
    simpa only [betaEq,alphaEq,Label.atom,Label.letters,InteriorSourceBlock.bar,if_true,List.cons_append,List.nil_append] using beforeEq
  let fragment := (targetSelection (actualChainPosition chain member)).fragment
  obtain ⟨a,b,whole⟩ := fragment.access.property.1.1
  obtain ⟨input,_prefix,part⟩ := fragment.assignments a b whole
  have rawLabels := part.plug_decomposition cut (Schema.beta 0).right.net
  obtain ⟨seam,lc,rc,left,right⟩ := streams rawLabels
  refine ⟨targetSelection,localTarget,edge,selection,out,packet,frame,own,packetPre,packetSite,packetEdge,
    frameTarget,bodyEq,alphaEq,betaEq,qEq,cellEq,node,appTrace,fnTrace,
    ⟨routeCtx,argId,appRoute,fnRoute,bodyRoute,argRoute⟩,?_,?_,?_,?_,nodeEq,cutAt,before,input,b,seam,lc,rc,rawLabels,left,right⟩
  · simpa only [alphaEq] using fromPort
  · simpa only [alphaEq] using toPort
  · simpa only [alphaEq] using marker
  · simpa only [alphaEq] using tail

#print axioms actual_closed_copy_overlap_operand_origins
end Lamping.Checks.ActualCopyOverlapOperandOrigins
