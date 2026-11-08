import Lamping.Lamping.PairedMarkerSpineReannotation
import Lamping.Lamping.InteriorSourceBlockEndpoints
import Lamping.Lamping.HistorySelectedPrincipalWord
import Lamping.Lambda.NodeLabelSuffixOrigins
import Lamping.Lambda.LabelInitialRelabelling
import Lamping.Lambda.LabelRelabelling
import Lamping.Lambda.SelectedDevelopmentRoutes
import Lamping.Lambda.LabelArgumentBinderScope

namespace Lamping.Lambda.Labelled
open InteriorSourceBlock

private theorem old_snoc
    (h : Marked.RelativeOldHistory F ps m n)
    (step : Marked.ReductionAt p n o) (selected : p∈Marked.setResidualPositions F n) :
    Marked.RelativeOldHistory F (ps++[p]) m o := by
  induction h with
  | nil => exact .cons step selected (.nil _)
  | cons redex member rest ih => exact .cons redex member (ih step selected)

private theorem positive_word (x : Label) : 0<x.letters.length := by
  cases x <;> simp [Label.letters]

private theorem atomic_origin {ps : List Path} {s t node : LTerm}
    {h : History ps s t} {p q : Path} {n : Nat}
    (ancestry : BetaNodeHistoryPreimage h p q)
    (atNode : t.subterm p=some node) (atom : node.label=Label.atom n) :
    ∃old,s.subterm q=some old ∧old.label=Label.atom n := by
  induction ancestry generalizing node with
  | nil => exact ⟨node,atNode,atom⟩
  | @one site ps source middle target body argument beta alpha p mid q step remaining redex origin _ ih =>
    obtain ⟨predecessor,lookup,stamp⟩ := ih atNode atom
    obtain ⟨old,oldLookup,unchanged | ⟨stem,bar,_degree,word⟩⟩ :=
      step.beta_node_label_suffix redex origin lookup
    · exact ⟨old,oldLookup,unchanged.symm.trans stamp⟩
    · have sizes := congrArg List.length word
      rw [stamp] at sizes
      have nonempty := positive_word old.label
      simp only [Label.atom,Label.letters,List.length_append,List.length_cons,List.length_nil] at sizes
      omega

private theorem copy_coordinates
    (origin : BetaIncomingReadingOrigin body argument site edge reader oldReader first last)
    (read : PrerequisiteReadsDirected t reader edge false) (same : edge=site)
    (bodyCase : body=.var (Label.atom n) 0) :
    first=site++[.arg] ∧last=site++[.fn,.body] ∧∃stamp inner,argument=.lam stamp inner := by
  cases origin with
  | resultFunction result function =>
    have sizes := congrArg List.length (read.2.symm.trans (result.trans function))
    simp only [List.length_append,List.length_cons,List.length_nil] at sizes
    omega
  | resultLambda result atReader oldLambda =>
    rw [bodyCase] at oldLambda
    cases oldLambda
  | copyFunction occurs copy atReader =>
    have sizes := congrArg List.length (read.2.symm.trans copy)
    rw [atReader] at sizes
    simp only [List.length_append,List.length_cons,List.length_nil] at sizes
    omega
  | @copyLambda q stamp inner occurs copy atReader oldLambda =>
    have sizes := congrArg List.length (same.symm.trans copy)
    simp only [List.length_append] at sizes
    have empty : q=[] := List.length_eq_zero_iff.mp (by omega)
    subst q
    exact ⟨rfl,by simp only [List.append_nil],stamp,inner,oldLambda⟩

private theorem contract_word (b a : Label) (n : Nat) (v : LTerm) :
    (LTerm.contract b a (.var (.atom n) 0) v).label.letters=
      b.letters++[.over a,.atom n,.under a]++v.label.letters := by
  cases v <;> simp only [LTerm.contract,LTerm.subst,LTerm.single,LTerm.prepend,LTerm.label,
    Label.letters_concat,Label.over,Label.under,Label.atom,Label.letters,
    List.cons_append,List.nil_append,List.append_assoc]

theorem SpineCreationPacket.actual_copy_overlap_operand_origins
    {F : List Path} {source localTarget : LTerm} {degree : Label}
    (packet : SpineCreationPacket F source degree false)
    (localHistory : History (packet.pre++[packet.site]) (initLabels source.erase) localTarget)
    (rootCopy : packet.edge=packet.site) :
    ∃ frame : PairedSpineCreationFrame packet (initLabels source.erase),
      frame.target=localTarget ∧
      ∀ n, frame.body=.var (Label.atom n) 0 →
        ∃ own : WindowOccurrences (initLabels source.erase) F n true false,
        ∃ (incomingCtx : SourcePort) (argId : Label),
          own.left.degree=frame.alpha ∧own.right.degree=frame.alpha ∧
          own.left.position=own.right.position ∧
          own.position=(own.left.position++[.fn])++[.body] ∧
          own.node=.var (Label.atom n) 0 ∧own.left.body=.var (Label.atom n) 0 ∧
          BetaNodeHistoryPreimage frame.prefixLabels packet.site own.left.position ∧
          BetaNodeHistoryPreimage frame.prefixLabels (packet.site++[.fn]) (own.left.position++[.fn]) ∧
          SelectedSourceRoute (sourceEdges [] .external (initLabels source.erase))
            (SelectedDegree (initLabels source.erase) F)
            incomingCtx frame.beta (.appContext own.left.beta) ∧
          SelectedSourceRoute (sourceEdges [] .external (initLabels source.erase))
            (SelectedDegree (initLabels source.erase) F)
            (.appFn own.left.beta) frame.alpha (.lamContext frame.alpha) ∧
          SelectedSourceRoute (sourceEdges [] .external (initLabels source.erase))
            (SelectedDegree (initLabels source.erase) F)
            (.lamBody frame.alpha) (Label.atom n) (.lamBind frame.alpha) ∧
          SelectedSourceRoute (sourceEdges [] .external (initLabels source.erase))
            (SelectedDegree (initLabels source.erase) F)
            (.appArg own.left.beta) frame.argument.label (.lamContext argId) ∧
          (∃ k, own.left.beta=Label.atom k ∧frame.beta.lastAtom=some k) ∧
          (∃ stamp inner, frame.argument=.lam stamp inner) ∧
          frame.firstNode=frame.argument ∧frame.lastNode=.var (Label.atom n) 0 ∧
          (sourceEdge own.env own.ctx own.node).fromPort=.lamBody frame.alpha ∧
          (sourceEdge own.env own.ctx own.node).toPort=.lamBind frame.alpha ∧
          frame.marker=.under frame.alpha ∧
          frame.tail=[.under frame.alpha,.atom n,.over frame.alpha]++frame.beta.letters.reverse ∧
          frame.current.label.readLetters false=frame.argument.label.readLetters false++
            [.under frame.alpha,.atom n,.over frame.alpha]++frame.beta.letters.reverse ∧
          frame.current.label.letters=frame.beta.letters++
            [.over frame.alpha,.atom n,.under frame.alpha]++frame.argument.label.letters ∧
          frame.alpha.relabel (initialRelabelling source 0)=degree := by
  obtain ⟨frame,atTarget⟩ := paired_spine_creation_frame packet localHistory (erase_initLabels source.erase).symm
  refine ⟨frame,atTarget,?_⟩
  intro n bodyCase
  let basis := initLabels source.erase
  have initial : INIT basis := init_is_INIT _
  obtain ⟨firstPos,lastPos,argLambda⟩ := copy_coordinates frame.origin frame.reading rootCopy bodyCase
  have currentAt : frame.target.subterm packet.site=some frame.current :=
    (congrArg (fun p=>frame.target.subterm p) rootCopy).symm.trans frame.lookup
  have currentEq : frame.current=LTerm.contract frame.beta frame.alpha frame.body frame.argument :=
    Option.some.inj (currentAt.symm.trans (frame.turn.contract_lookup frame.redex))
  have word : frame.current.label.letters=frame.beta.letters++
      [.over frame.alpha,.atom n,.under frame.alpha]++frame.argument.label.letters := by
    rw [currentEq,bodyCase]
    exact contract_word _ _ _ _
  have argAt : frame.middle.subterm (packet.site++[.arg])=some frame.argument := by
    rw [LTerm.subterm_append,frame.redex];cases frame.argument <;> rfl
  have firstEq : frame.firstNode=frame.argument :=
    Option.some.inj (((congrArg (fun p=>frame.middle.subterm p) firstPos).symm.trans frame.firstLookup).symm.trans argAt)
  have bodyAt : frame.middle.subterm (packet.site++[.fn,.body])=some frame.body := by
    rw [LTerm.subterm_append,frame.redex];cases frame.body <;> rfl
  have lastEq : frame.lastNode=.var (.atom n) 0 :=
    (Option.some.inj (((congrArg (fun p=>frame.middle.subterm p) lastPos).symm.trans frame.lastLookup).symm.trans bodyAt)).trans bodyCase
  have readingWord : frame.current.label.readLetters false=frame.argument.label.readLetters false++
      [.under frame.alpha,.atom n,.over frame.alpha]++frame.beta.letters.reverse := by
    simp only [Label.readLetters,Bool.false_eq_true,if_false]
    rw [word]
    simp only [List.reverse_append,List.reverse_cons,List.cons_append,List.nil_append,List.append_assoc]
  have marker : frame.marker=.under frame.alpha := by
    rcases frame.formula with normal | ⟨bad,_⟩ | ⟨_,mark,_⟩
    · rw [readingWord,firstEq,lastEq] at normal
      have sizes := congrArg List.length normal
      simp only [LTerm.label,Label.readLetters,Bool.false_eq_true,if_false,Label.atom,Label.letters,
        List.length_append,List.length_cons,List.length_nil,List.length_reverse] at sizes
      omega
    · cases bad
    · exact mark
  have tail : frame.tail=[.under frame.alpha,.atom n,.over frame.alpha]++frame.beta.letters.reverse := by
    have equation := frame.tailEquation
    rw [readingWord,firstEq,List.append_assoc] at equation
    exact List.append_cancel_left equation.symm
  have afterOld := old_snoc packet.event.beforeOld packet.event.reduction packet.event.member
  have basisOld : Marked.RelativeOldHistory F packet.pre (Marked.mark F basis.erase) packet.event.markedBefore := by
    simpa only [basis,erase_initLabels] using packet.event.beforeOld
  have afterBasis : Marked.RelativeOldHistory F (packet.pre++[packet.site])
      (Marked.mark F basis.erase) packet.event.markedAfter := by
    simpa only [basis,erase_initLabels] using afterOld
  have relative := (Marked.relativeOld_iff_relative (Marked.selected_mark F basis.erase)).mp afterBasis
  have degreeAt : frame.middle.degreeAt packet.site=some frame.alpha := by
    simp only [LTerm.degreeAt,frame.redex,Option.bind_some,LTerm.degree]
  have selected := relative_last_selected_degree initial relative frame.prefixLabels frame.turn degreeAt
  obtain ⟨a,alphaAtom⟩ := selected.atomic initial
  obtain ⟨q,qMem,⟨oldBeta,oldAlpha,oldBody,oldArg,atQ⟩,appTrace,fnTrace⟩ :=
    basisOld.selected_app_function_preimages frame.prefixLabels packet.event.member
  have atFn : frame.middle.subterm (packet.site++[.fn])=some (.lam frame.alpha frame.body) := by
    rw [LTerm.subterm_append,frame.redex];rfl
  obtain ⟨oldLambda,oldLambdaAt,oldLambdaAtom⟩ := atomic_origin fnTrace atFn alphaAtom
  have sourceFn : basis.subterm (q++[.fn])=some (.lam oldAlpha oldBody) := by
    rw [LTerm.subterm_append,atQ];rfl
  have lambdaEq := Option.some.inj (oldLambdaAt.symm.trans sourceFn)
  have oldAlphaEq : oldAlpha=frame.alpha :=
    ((congrArg LTerm.label lambdaEq).symm.trans oldLambdaAtom).trans alphaAtom.symm
  let chosen : SelectedRedex basis F :=
    ⟨q,qMem,oldBeta,frame.alpha,oldBody,oldArg,by rw [←oldAlphaEq];exact atQ⟩
  have beforeRelative := (Marked.relativeOld_iff_relative (Marked.selected_mark F basis.erase)).mp basisOld
  have routes := relative_development_selected_routes initial beforeRelative frame.prefixLabels
  obtain ⟨env,ctx,appId,lamId,appRoute,fnRoute,bodyRoutes,argRoutes⟩ := routes.redex_children frame.redex
  have atomicFn : SourceRoute (sourceEdges [] .external basis) (.appFn appId) (.atom a) (.lamContext lamId) := by
    rw [←alphaAtom];exact fnRoute.forget
  obtain ⟨cell,member,cellAtom,fromFn,toFn⟩ := atomicFn.initial_atom_edge initial
  obtain ⟨oldEnv,oldCtx,atRedex⟩ := SourceSubterm.of_lookup basis chosen.lookup [] .external
  have fnMember : (sourceEdge oldEnv (.appFn chosen.beta) (.lam frame.alpha oldBody))∈sourceEdges [] .external basis :=
    atRedex.edges_subset _ (by
      simp only [sourceEdges,List.mem_cons,List.mem_append]
      exact Or.inr (Or.inl (Or.inl rfl)))
  have exactCell := sourceEdges_unique initial member fnMember (cellAtom.trans alphaAtom.symm)
  have appEq : appId=chosen.beta := by
    have p := (congrArg SourceEdge.fromPort exactCell).symm.trans fromFn
    exact (SourcePort.appFn.inj p).symm
  have lamEq : lamId=frame.alpha := by
    exact (SourcePort.lamContext.inj ((congrArg SourceEdge.toPort exactCell).symm.trans toFn)).symm
  rw [appEq] at appRoute fnRoute argRoutes
  rw [lamEq] at fnRoute bodyRoutes
  rw [bodyCase] at bodyRoutes
  have bodyRoute : SelectedSourceRoute (sourceEdges [] .external basis) (SelectedDegree basis F)
      (.lamBody frame.alpha) (.atom n) (.lamBind frame.alpha) := by
    cases bodyRoutes with | var route => exact route
  obtain ⟨stamp,inner,argShape⟩ := argLambda
  rw [argShape] at argRoutes
  obtain ⟨argId,argRoute⟩ : ∃argId,SelectedSourceRoute (sourceEdges [] .external basis) (SelectedDegree basis F)
      (.appArg chosen.beta) frame.argument.label (.lamContext argId) := by
    cases argRoutes with | lam route rest => exact ⟨_,by simpa only [argShape,LTerm.label] using route⟩
  obtain ⟨k,lastAtom,betaAtom⟩ := appRoute.forget.app_last_atom
  obtain ⟨bodyCell,bodyMember,bodyAtom,bodyFrom,bodyTo⟩ := bodyRoute.forget.initial_atom_edge initial
  obtain ⟨position,oe,oc,node,occurrence,edgeEq⟩ := edge_occurrence bodyMember
  have fromEq : oc=chosen.afterPort true := by
    exact (source_edge_departure oe oc node).symm.trans ((congrArg SourceEdge.fromPort edgeEq).trans bodyFrom)
  have toEq : (sourceEdge oe oc node).toPort=chosen.beforePort false :=
    (congrArg SourceEdge.toPort edgeEq).trans bodyTo
  have nodeAtomic : node.label=Label.atom n :=
    (source_edge_label oe oc node).symm.trans ((congrArg SourceEdge.atom edgeEq).trans bodyAtom)
  have positionEq := occurrence_after_marker initial occurrence chosen fromEq
  obtain ⟨stamp',index,rest,nodeEq,split,depth⟩ := occurrence_before_marker initial occurrence chosen toEq
  have restNil : rest=[] := by
    exact (List.cons.inj (List.append_cancel_left (positionEq.symm.trans split))).2.symm
  have stampEq : stamp'=Label.atom n := by simpa only [nodeEq,LTerm.label] using nodeAtomic
  have indexEq : index=0 := by simpa only [restNil,binderDepth] using depth
  have nodeFull : node=.var (.atom n) 0 := by rw [nodeEq,stampEq,indexEq]
  have sourceBody : basis.subterm ((chosen.position++[.fn])++[.body])=some chosen.body := by
    rw [List.append_assoc,LTerm.subterm_append,chosen.lookup];cases chosen.body <;> rfl
  have originalBody : chosen.body=.var (.atom n) 0 := by
    have atSame : basis.subterm ((chosen.position++[.fn])++[.body])=some node :=
      (congrArg (fun p=>basis.subterm p) positionEq).symm.trans occurrence.lookup
    exact (Option.some.inj (sourceBody.symm.trans atSame)).trans nodeFull
  let own : WindowOccurrences basis F n true false :=
    ⟨position,oe,oc,node,occurrence,nodeAtomic,chosen,chosen,positionEq,stamp',index,rest,nodeEq,split,depth⟩
  have globalHistory := frame.prefixLabels.relabel (initialRelabelling source 0)
  have factor : (initLabels source.erase).relabel (initialRelabelling source 0)=source :=
    initialRelabelling_factor source 0
  rw [factor] at globalHistory
  have middleEq := globalHistory.deterministic packet.event.labels
  have atSame := congrArg (fun t : LTerm=>t.subterm packet.site) middleEq
  change (frame.middle.relabel (initialRelabelling source 0)).subterm packet.site=packet.middle.subterm packet.site at atSame
  rw [LTerm.subterm_relabel,frame.redex,Option.map_some,packet.event.redex] at atSame
  have globalDegree := congrArg LTerm.degree (Option.some.inj atSame)
  have payload : frame.alpha.relabel (initialRelabelling source 0)=degree := by
    simpa only [LTerm.relabel,LTerm.degree,Option.some.injEq] using globalDegree
  exact ⟨own,ctx,argId,rfl,rfl,rfl,positionEq,nodeFull,originalBody,appTrace,fnTrace,
    appRoute,fnRoute,bodyRoute,argRoute,⟨k,betaAtom,lastAtom⟩,⟨stamp,inner,argShape⟩,
    firstEq,lastEq,(congrArg SourceEdge.fromPort edgeEq).trans bodyFrom,toEq,marker,tail,readingWord,word,payload⟩

#print axioms SpineCreationPacket.actual_copy_overlap_operand_origins
end Lamping.Lambda.Labelled
