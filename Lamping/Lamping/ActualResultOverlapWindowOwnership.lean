import Lamping.Lamping.PairedMarkerSpineReannotation
import Lamping.Lamping.InteriorSourceBlockEndpoints
import Lamping.Lamping.HistorySelectedPrincipalWord
import Lamping.Lambda.NodeLabelSuffixOrigins
import Lamping.Lambda.LabelInitialRelabelling
import Lamping.Lambda.LabelRelabelling

namespace Lamping.Lambda.Labelled
open InteriorSourceBlock

private theorem append_old {F ps qs : List Path} {m n o : Marked}
    (left : Marked.RelativeOldHistory F ps m n)
    (right : Marked.RelativeOldHistory F qs n o) :
    Marked.RelativeOldHistory F (ps++qs) m o := by
  induction left with
  | nil => exact right
  | cons reduction member _ ih => exact .cons reduction member (ih right)

private theorem nonempty_label (a : Label) : 0<a.letters.length := by
  cases a <;> simp [Label.letters]

private theorem atomic_trace {ps : List Path} {source target current : LTerm}
    {labels : History ps source target} {p q : Path} {n : Nat}
    (trace : BetaNodeHistoryPreimage labels p q)
    (lookup : target.subterm p=some current) (atomic : current.label=Label.atom n) :
    ∃old,source.subterm q=some old ∧old.label=Label.atom n := by
  induction trace generalizing current with
  | nil => exact ⟨current,lookup,atomic⟩
  | @one site ps source middle target body argument beta alpha p mid q step remaining redex origin _ ih =>
    obtain ⟨node,atNode,nodeAtom⟩ := ih lookup atomic
    obtain ⟨old,atOld,same |⟨pre,marker,_marks,word⟩⟩ :=
      step.beta_node_label_suffix redex origin atNode
    · exact ⟨old,atOld,same.symm.trans nodeAtom⟩
    · rw [nodeAtom] at word
      have lengths := congrArg List.length word
      have positive := nonempty_label old.label
      simp only [Label.atom,Label.letters,List.length_append,List.length_cons,List.length_nil] at lengths
      omega

private theorem result_coordinates
    (origin : BetaIncomingReadingOrigin body argument site edge reader oldReader first last)
    (reading : PrerequisiteReadsDirected t reader edge true) (same : edge=site) :
    first=site ∧last=site++[.fn,.body] := by
  cases origin with
  | resultFunction => exact ⟨rfl,rfl⟩
  | resultLambda result atReader _ =>
    have lengths := congrArg List.length (result.symm.trans (atReader ▸ reading.2))
    simp only [List.length_append,List.length_cons,List.length_nil] at lengths
    omega
  | copyFunction _ copy _ =>
    have lengths := congrArg List.length (same.symm.trans copy)
    simp only [List.length_append,List.length_cons,List.length_nil] at lengths
    omega
  | copyLambda _ _ atReader _ =>
    have lengths := congrArg List.length (atReader ▸ reading.2)
    simp only [List.length_append,List.length_cons,List.length_nil] at lengths
    omega

private theorem contract_atomic_var_word (beta alpha : Label) (n : Nat) (arg : LTerm) :
    (LTerm.contract beta alpha (.var (Label.atom n) 0) arg).label.letters=
      beta.letters++[.over alpha,.atom n,.under alpha]++arg.label.letters := by
  cases arg <;>
    simp only [LTerm.contract,LTerm.subst,LTerm.single,LTerm.prepend,LTerm.label,
      Label.letters_concat,Label.over,Label.under,Label.atom,Label.letters,
      List.cons_append,List.nil_append,List.append_assoc]

/-- THIS actual result-overlap packet supplies both neighboring bars and
their original selected FUNCTION ancestry. The paired frame is constructed
from the given actual schedule; a written window is never a premise. -/
theorem SpineCreationPacket.actual_result_overlap_window_ownership
    {F : List Path} {source localTarget : LTerm} {degree : Label}
    (packet : SpineCreationPacket F source degree true)
    (localHistory : History (packet.pre++[packet.site]) (initLabels source.erase) localTarget)
    (resultEdge : packet.edge=packet.site) :
    ∃ frame : PairedSpineCreationFrame packet (initLabels source.erase),
      frame.target=localTarget ∧
      ∀ n,frame.body=.var (Label.atom n) 0 →
        ∃ own : WindowOccurrences (initLabels source.erase) F n true false,
          own.left.degree=frame.alpha ∧own.right.degree=frame.alpha ∧
          own.left.position=own.right.position ∧
          own.position=(own.left.position++[.fn])++[.body] ∧
          own.node=.var (Label.atom n) 0 ∧own.left.body=.var (Label.atom n) 0 ∧
          BetaNodeHistoryPreimage frame.prefixLabels (packet.site++[.fn]) (own.left.position++[.fn]) ∧
          (sourceEdge own.env own.ctx own.node).fromPort=.lamBody frame.alpha ∧
          (sourceEdge own.env own.ctx own.node).toPort=.lamBind frame.alpha ∧
          frame.marker=.over frame.alpha ∧
          frame.tail=[.over frame.alpha,.atom n,.under frame.alpha]++frame.argument.label.letters ∧
          frame.current.label.letters=frame.beta.letters++
            [.over frame.alpha,.atom n,.under frame.alpha]++frame.argument.label.letters ∧
          frame.alpha.relabel (initialRelabelling source 0)=degree := by
  obtain ⟨frame,atTarget⟩ := paired_spine_creation_frame packet localHistory (erase_initLabels source.erase).symm
  refine ⟨frame,atTarget,?_⟩
  intro n bodyCase
  let basis := initLabels source.erase
  have initial : INIT basis := init_is_INIT _
  obtain ⟨firstPos,lastPos⟩ := result_coordinates frame.origin frame.reading resultEdge
  have atCurrent : frame.target.subterm packet.site=some frame.current :=
    (congrArg (fun p=>frame.target.subterm p) resultEdge).symm.trans frame.lookup
  have currentEq : frame.current=LTerm.contract frame.beta frame.alpha frame.body frame.argument :=
    Option.some.inj (atCurrent.symm.trans (frame.turn.contract_lookup frame.redex))
  have currentWord : frame.current.label.letters=frame.beta.letters++
      [.over frame.alpha,.atom n,.under frame.alpha]++frame.argument.label.letters := by
    rw [currentEq,bodyCase]
    exact contract_atomic_var_word _ _ _ _
  have firstLookup : frame.middle.subterm packet.site=some frame.firstNode :=
    (congrArg (fun p=>frame.middle.subterm p) firstPos).symm.trans frame.firstLookup
  have firstEq : frame.firstNode=.app frame.beta (.lam frame.alpha frame.body) frame.argument :=
    Option.some.inj (firstLookup.symm.trans frame.redex)
  have atBody : frame.middle.subterm (packet.site++[.fn,.body])=some frame.body := by
    rw [LTerm.subterm_append,frame.redex];cases frame.body <;> rfl
  have lastLookup : frame.middle.subterm (packet.site++[.fn,.body])=some frame.lastNode :=
    (congrArg (fun p=>frame.middle.subterm p) lastPos).symm.trans frame.lastLookup
  have lastEq : frame.lastNode=.var (Label.atom n) 0 :=
    (Option.some.inj (lastLookup.symm.trans atBody)).trans bodyCase
  have firstLabel : frame.firstNode.label=frame.beta := by rw [firstEq];rfl
  have lastLabel : frame.lastNode.label=Label.atom n := by rw [lastEq];rfl
  have markerEq : frame.marker=.over frame.alpha := by
    rcases frame.formula with normal |⟨_dir,mark,_arg,_lookup,_word⟩ |⟨bad,_rest⟩
    · change frame.current.label.letters=frame.firstNode.label.letters++frame.marker::frame.lastNode.label.letters at normal
      rw [currentWord,firstLabel,lastLabel] at normal
      have lengths := congrArg List.length normal
      simp only [Label.atom,Label.letters,List.length_append,List.length_cons,List.length_nil] at lengths
      omega
    · exact mark
    · cases bad
  have tailEq : frame.tail=[.over frame.alpha,.atom n,.under frame.alpha]++frame.argument.label.letters := by
    have eq := frame.tailEquation
    change frame.current.label.letters=frame.firstNode.label.letters++frame.tail at eq
    rw [currentWord,firstLabel,List.append_assoc] at eq
    exact List.append_cancel_left eq.symm
  have afterOld := append_old packet.event.beforeOld
    (Marked.RelativeOldHistory.cons packet.event.reduction packet.event.member (.nil _))
  have afterHistory : History (packet.pre++[packet.site]) basis frame.target :=
    frame.prefixLabels.append (.cons frame.turn (.nil _))
  have basisOld : Marked.RelativeOldHistory F packet.pre (Marked.mark F basis.erase) packet.event.markedBefore := by
    simpa only [basis,erase_initLabels] using packet.event.beforeOld
  have afterBasis : Marked.RelativeOldHistory F (packet.pre++[packet.site])
      (Marked.mark F basis.erase) packet.event.markedAfter := by
    simpa only [basis,erase_initLabels] using afterOld
  have relative := (Marked.relativeOld_iff_relative (Marked.selected_mark F basis.erase)).mp afterBasis
  have atDegree : frame.middle.degreeAt packet.site=some frame.alpha := by
    simp only [LTerm.degreeAt,frame.redex,Option.bind_some,LTerm.degree]
  have selected := relative_last_selected_degree initial relative frame.prefixLabels frame.turn atDegree
  obtain ⟨a,alphaAtom⟩ := selected.atomic initial
  obtain ⟨q,qMem,⟨oldBeta,oldAlpha,oldBody,oldArg,atQ⟩,_appTrace,fnTrace⟩ :=
    basisOld.selected_app_function_preimages frame.prefixLabels packet.event.member
  have atFn : frame.middle.subterm (packet.site++[.fn])=some (.lam frame.alpha frame.body) := by
    rw [LTerm.subterm_append,frame.redex];rfl
  obtain ⟨oldLambda,oldLambdaAt,oldLambdaAtom⟩ := atomic_trace fnTrace atFn alphaAtom
  have sourceFn : basis.subterm (q++[.fn])=some (.lam oldAlpha oldBody) := by
    rw [LTerm.subterm_append,atQ];rfl
  have lambdaEq := Option.some.inj (oldLambdaAt.symm.trans sourceFn)
  have oldAlphaEq : oldAlpha=frame.alpha := by
    have eq := congrArg LTerm.label lambdaEq
    exact (eq.symm.trans oldLambdaAtom).trans alphaAtom.symm
  let chosen : SelectedRedex basis F :=
    ⟨q,qMem,oldBeta,frame.alpha,oldBody,oldArg,by rw [←oldAlphaEq];exact atQ⟩
  have chosenTrace : BetaNodeHistoryPreimage frame.prefixLabels
      (packet.site++[.fn]) (chosen.position++[.fn]) := fnTrace
  obtain ⟨ctx,finish,route⟩ := actual_old_node_route afterOld afterHistory frame.lookup
  have walk := route_walk route
  rw [currentWord] at walk
  have walk' : LetterWalk (sourceEdges [] .external basis) (SelectedDegree basis F)
      ctx (frame.beta.letters++(.over frame.alpha::.atom n::.under frame.alpha::frame.argument.label.letters)) finish := by
    simpa only [List.append_assoc,List.cons_append,List.nil_append] using walk
  obtain ⟨before,_prefix,rest⟩ := walk'.split
  cases rest with
  | cons leftStep afterLeft =>
    cases afterLeft with
    | cons atomStep afterAtom =>
      cases afterAtom with
      | cons rightStep _suffix =>
        obtain ⟨left,leftDegree,_leftStart,leftFinish⟩ := marker_step_redex initial (kind:=true) leftStep
        obtain ⟨right,rightDegree,rightStart,_rightFinish⟩ := marker_step_redex initial (kind:=false) rightStep
        cases atomStep with
        | @atom cell _ member atomic =>
          have departure : cell.fromPort=chosen.afterPort true := by
            simpa only [SelectedRedex.afterPort,if_true,leftDegree] using leftFinish
          have arrival : cell.toPort=chosen.beforePort false := by
            simpa only [SelectedRedex.beforePort,Bool.false_eq_true,if_false,rightDegree] using rightStart
          obtain ⟨position,env,localCtx,node,occurrence,edgeEq⟩ := edge_occurrence member
          have fromEq : localCtx=chosen.afterPort true :=
            (source_edge_departure env localCtx node).symm.trans
              ((congrArg SourceEdge.fromPort edgeEq).trans departure)
          have toEq : (sourceEdge env localCtx node).toPort=chosen.beforePort false :=
            (congrArg SourceEdge.toPort edgeEq).trans arrival
          have nodeAtomic : node.label=Label.atom n :=
            (source_edge_label env localCtx node).symm.trans ((congrArg SourceEdge.atom edgeEq).trans atomic)
          have positionEq := occurrence_after_marker initial occurrence chosen fromEq
          have bound := occurrence_before_marker initial occurrence chosen toEq
          obtain ⟨stamp,index,rest,nodeEq,split,depth⟩ := bound
          have restNil : rest=[] := by
            have eq := List.append_cancel_left (positionEq.symm.trans split)
            exact (List.cons.inj eq).2.symm
          have stampEq : stamp=Label.atom n := by simpa only [nodeEq,LTerm.label] using nodeAtomic
          have indexEq : index=0 := by simpa only [restNil,binderDepth] using depth
          have nodeFull : node=.var (Label.atom n) 0 := by rw [nodeEq,stampEq,indexEq]
          have sourceBody : basis.subterm ((chosen.position++[.fn])++[.body])=some chosen.body := by
            rw [List.append_assoc,LTerm.subterm_append,chosen.lookup];cases chosen.body <;> rfl
          have originalBody : chosen.body=.var (Label.atom n) 0 := by
            have atSame : basis.subterm ((chosen.position++[.fn])++[.body])=some node :=
              (congrArg (fun p=>basis.subterm p) positionEq).symm.trans occurrence.lookup
            exact (Option.some.inj (sourceBody.symm.trans atSame)).trans nodeFull
          let own : WindowOccurrences basis F n true false :=
            ⟨position,env,localCtx,node,occurrence,nodeAtomic,chosen,chosen,positionEq,
              stamp,index,rest,nodeEq,split,depth⟩
          have globalHistory := frame.prefixLabels.relabel (initialRelabelling source 0)
          have factor : (initLabels source.erase).relabel (initialRelabelling source 0)=source :=
            initialRelabelling_factor source 0
          rw [factor] at globalHistory
          have middleEq := globalHistory.deterministic packet.event.labels
          have atSame := congrArg (fun t : LTerm=>t.subterm packet.site) middleEq
          change (frame.middle.relabel (initialRelabelling source 0)).subterm packet.site=
            packet.middle.subterm packet.site at atSame
          rw [LTerm.subterm_relabel,frame.redex,Option.map_some,packet.event.redex] at atSame
          have globalDegree := congrArg LTerm.degree (Option.some.inj atSame)
          have payload : frame.alpha.relabel (initialRelabelling source 0)=degree := by
            simpa only [LTerm.relabel,LTerm.degree,Option.some.injEq] using globalDegree
          refine ⟨own,rfl,rfl,rfl,positionEq,nodeFull,originalBody,chosenTrace,?_,?_,markerEq,tailEq,currentWord,payload⟩
          · exact (congrArg SourceEdge.fromPort edgeEq).trans departure
          · exact toEq

#print axioms SpineCreationPacket.actual_result_overlap_window_ownership
end Lamping.Lambda.Labelled
