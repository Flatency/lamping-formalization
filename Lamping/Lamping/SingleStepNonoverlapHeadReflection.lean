import Lamping.Lamping.ReverseReadingLetterBlocks
import Lamping.Lamping.LocalSourceFragmentEvaluation
import Lamping.Lamping.TerminalCreatedReadingFarChains
import Lamping.Lamping.ActualChainForwardOrder

namespace Lamping.AG
open Graph Lambda Lambda.Labelled

private theorem last_inj {p q : Path} {s t : Step} (eq : p++[s]=q++[t]) : p=q ∧s=t := by
  have rev := congrArg List.reverse eq
  simp only [List.reverse_append,List.reverse_cons,List.reverse_nil,List.nil_append,List.cons_append] at rev
  have pair := List.cons.inj rev
  exact ⟨by simpa using congrArg List.reverse pair.2,pair.1⟩

private theorem unsnoc (q : Path) (ne : q≠[]) : ∃p s,q=p++[s] := by
  induction q with
  | nil => exact False.elim (ne rfl)
  | cons s tail ih =>
    cases tail with
    | nil => exact ⟨[],s,rfl⟩
    | cons t rest =>
      obtain ⟨p,u,eq⟩ := ih (by simp)
      exact ⟨s::p,u,by rw [eq];rfl⟩

private theorem terminal_fn {t : LTerm} {p : Path}
    (reading : PrerequisiteReadsDirected t p p false)
    (chain : PrerequisiteChain t p [p]) : ∃parent,p=parent++[.fn] := by
  rcases reading.1 with ⟨a,f,b,lookup,split⟩|⟨a,b,lookup,split⟩
  · have bad := congrArg List.length split
    simp at bad
  · rcases chain.lambda_cases lookup with ⟨parent,a,arg,split,atParent,es⟩|
      ⟨parent,step,tail,split,notFn,listEq,remaining⟩
    · exact ⟨parent,split⟩
    · have empty : tail=[] := (List.cons.inj listEq).2.symm
      exact False.elim (remaining.nonempty empty)

private theorem false_forms {source target body argument : LTerm} {site p : Path} {beta alpha : Labelled.Label}
    (step : StepAt site source target)
    (redex : source.subterm site=some (.app beta (.lam alpha body) argument))
    (noOverlap : ∀stamp,body≠.var stamp 0)
    (reading : PrerequisiteReadsDirected target p p false)
    (chain : PrerequisiteChain target p [p])
    (created : BetaCreatedIncoming body site p) :
    (p=site ∧∃stamp inner,body=.lam stamp inner) ∨
      ∃parent,ArgumentOccurrence body.erase (parent++[.fn]) ∧p=site++(parent++[.fn]) := by
  obtain ⟨old,first,last,origin⟩ := step.created_reading_origin redex reading.1 (betaCreatedIncoming_iff.mp created)
  obtain ⟨parent,terminal⟩ := terminal_fn reading chain
  cases origin with
  | resultFunction result function =>
    have bad := congrArg List.length (result.trans function)
    simp at bad
  | resultLambda result _ oldLambda => exact Or.inl ⟨result,_,_,oldLambda⟩
  | @copyFunction q occurs copy read =>
    have bad := congrArg List.length (copy.symm.trans read)
    simp at bad
  | @copyLambda q stamp inner occurs copy _ oldLambda =>
    have ne : q≠[] := by
      intro eq
      subst q
      have bare : body.erase=Term.var 0 := by simpa only [ArgumentOccurrence,subtermAt,binderDepth,Option.some.injEq] using occurs
      cases body with
      | var a n => exact noOverlap a (by cases bare;rfl)
      | app => cases bare
      | lam => cases bare
    obtain ⟨pre,s,split⟩ := unsnoc q ne
    have last : s=.fn := (last_inj (by simpa only [split,←List.append_assoc] using copy.symm.trans terminal)).2
    subst s
    exact Or.inr ⟨pre,by simpa only [split] using occurs,by simpa only [split] using copy⟩

section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable {g : Net signature N B W} {root : B} {source localTarget : LTerm}
private noncomputable def revBlocks (selection : SourceEdgeSelection (initLabels source.erase) g root)
    (edge : BetaEdge g) (label : Labelled.Label) :=
  label.readLetters false |>.map (fun letter=>orientPhysical false
    (letter.sourceWord selection.atomWord edge.principal edge.reverseRoute))

private theorem principal_ne_reverse (edge : BetaEdge g) : edge.principal≠edge.reverseRoute := by
  intro same
  have starts := Option.some.inj (edge.principalStart.symm.trans (same ▸ edge.reverse_start))
  have nodes : edge.app=edge.lam := congrArg Sigma.fst (Sum.inl.inj starts)
  have bad := edge.appLabel.symm.trans ((congrArg g.label nodes).trans edge.lamLabel)
  cases bad

private theorem atomic_at {p : Path} {node : LTerm}
    (lookup : (initLabels source.erase).subterm p=some node) : ∃n,node.label=Labelled.Label.atom n :=
  (init_is_INIT source.erase).1 _ (LTerm.label_mem_of_subterm lookup)

private theorem result_blocks
    (selection : SourceEdgeSelection (initLabels source.erase) g root) (edge : BetaEdge g)
    {site : Path} {b a stamp : Labelled.Label} {inner argument node : LTerm}
    (redex : (initLabels source.erase).subterm site=some (.app b (.lam a (.lam stamp inner)) argument))
    (step : StepAt site (initLabels source.erase) localTarget)
    (lookup : localTarget.subterm site=some node) :
    revBlocks selection edge node.label=
      [reverseEdges (selection.evalLabel edge stamp),edge.reverseRoute,reverseEdges (selection.evalLabel edge b)] := by
  have eq := Option.some.inj (lookup.symm.trans (step.contract_lookup redex))
  have atBody : (initLabels source.erase).subterm (site++[.fn,.body])=some (.lam stamp inner) := by
    rw [LTerm.subterm_append,redex];rfl
  obtain ⟨n,bn⟩ := atomic_at redex
  obtain ⟨m,sm⟩ := atomic_at atBody
  change b=Labelled.Label.atom n at bn
  change stamp=Labelled.Label.atom m at sm
  rw [eq]
  simp only [LTerm.contract,LTerm.subst,LTerm.prepend,LTerm.label]
  rw [bn,sm]
  rfl

private theorem copy_blocks
    (selection : SourceEdgeSelection (initLabels source.erase) g root) (edge : BetaEdge g)
    {site q : Path} {b a : Labelled.Label} {body argument node : LTerm}
    (redex : (initLabels source.erase).subterm site=some (.app b (.lam a body) argument))
    (step : StepAt site (initLabels source.erase) localTarget)
    (occurs : ArgumentOccurrence body.erase q) (ne : q≠[])
    (lookup : localTarget.subterm (site++q)=some node) :
    ∃stamp,body.subterm q=some (.var stamp (binderDepth q)) ∧
      revBlocks selection edge node.label=
      [reverseEdges (selection.evalLabel edge argument.label),edge.principal,reverseEdges (selection.evalLabel edge stamp)] := by
  have localLookup := lookup
  rw [LTerm.subterm_append,step.contract_lookup redex,Option.bind_some] at localLookup
  obtain ⟨stamp,old,labelEq⟩ := LTerm.contract_argument_incoming_label occurs localLookup
  rw [if_neg ne] at labelEq
  have atOld : (initLabels source.erase).subterm ((site++[.fn,.body])++q)=some (.var stamp (binderDepth q)) := by
    rw [List.append_assoc,LTerm.subterm_append,redex];simpa only [LTerm.subterm,Option.bind_some] using old
  have atArg : (initLabels source.erase).subterm (site++[.arg])=some argument := by
    rw [LTerm.subterm_append,redex];cases argument <;> rfl
  obtain ⟨n,sn⟩ := atomic_at atOld
  obtain ⟨m,am⟩ := atomic_at atArg
  change stamp=Labelled.Label.atom n at sn
  refine ⟨stamp,old,?_⟩
  rw [labelEq,sn,am]
  change [reverseEdges (selection.atomWord m),reverseEdges edge.reverseRoute,reverseEdges (selection.atomWord n)]=_
  rw [show reverseEdges edge.reverseRoute=edge.principal from reverseEdges_involutive _]
  rfl
end

private theorem same_pair_images
    {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
    {g : Net signature N B W} {root : B} {source : LTerm}
    (selection : OccurrenceFragmentSelection source g root)
    {p q l r common : Path}
    (left : PrerequisiteChain source p [l,common]) (right : PrerequisiteChain source q [r,common])
    (same : (selection (actualChainPosition left ⟨l,by simp⟩)).fragment.segments=
      (selection (actualChainPosition right ⟨r,by simp⟩)).fragment.segments) :
    SameChainRepresentation selection left right := by
  apply List.ext_getElem (by simp only [canonicalChainImage_length,List.length_cons,List.length_nil])
  intro n hn hm
  have bound : n<2 := by simpa only [canonicalChainImage_length,List.length_cons,List.length_nil] using hn
  have casesN : n=0 ∨n=1 := by omega
  rcases casesN with rfl|rfl
  · have a := canonical_chain_slot selection left (actualChainPosition left ⟨l,by simp⟩) (by rfl : [l,common][0]?=some l)
    have b := canonical_chain_slot selection right (actualChainPosition right ⟨r,by simp⟩) (by rfl : [r,common][0]?=some r)
    have eq := a.trans ((congrArg some same).trans b.symm)
    simpa only [List.getElem?_eq_getElem hn,List.getElem?_eq_getElem hm,Option.some.injEq] using eq
  · let pos := actualChainPosition left ⟨common,by simp⟩
    have a := canonical_chain_slot selection left pos (by rfl : [l,common][1]?=some pos.val)
    have b := canonical_chain_slot selection right pos (by rfl : [r,common][1]?=some pos.val)
    simpa only [List.getElem?_eq_getElem hn,List.getElem?_eq_getElem hm,Option.some.injEq] using a.trans b.symm

theorem PathSite.one_step_nonoverlap_false_head_labels
    {K B W V : Type} [FiniteNames K] [FiniteNames B]
    [FiniteNames W] [FiniteNames V]
    {kept : K → Graph.Label signature} {i : Nat}
    (site : PathSite (.beta i) kept (B:=B) (W:=W) (V:=V))
    {root : B} {original source target body argument : LTerm}
    {prior : List Path} {redexSite leftReader rightReader : Path}
    {beta alpha : Labelled.Label} {marked : Marked}
    (initial : INIT original)
    (prefixHistory : History prior original source)
    (closed : Closed source.erase)
    (matching : Matches site.net root source.erase)
    (inputs : RootInputs site.net root)
    {boundary : B → Bool} (flow : FlowBalance site.net boundary)
    (positive : boundary root=true)
    {heights : B → Int} (balance : IndexedLevelBalance site.net heights)
    (rootDepth : heights root=0)
    (transparency : Transparency site.net root)
    (relative : Marked.RelativeHistory [redexSite]
      (Marked.mark (site.betaSyntaxFiber root source.erase) source.erase) marked)
    (normal : Marked.Normal marked)
    (step : StepAt redexSite source target)
    (redex : source.subterm redexSite=
      some (.app beta (.lam alpha body) argument))
    (nonoverlap : ∀ stamp, body≠.var stamp 0)
    (sourceSelection : OccurrenceFragmentSelection source site.net root)
    (sourceJoint : JointRepresentation closed sourceSelection)
    (targetSelection : OccurrenceFragmentSelection target site.reduce root)
    (leftRead : PrerequisiteReadsDirected target leftReader leftReader false)
    (rightRead : PrerequisiteReadsDirected target rightReader rightReader false)
    (leftChain : PrerequisiteChain target leftReader [leftReader])
    (rightChain : PrerequisiteChain target rightReader [rightReader])
    (leftCreated : BetaCreatedIncoming body redexSite leftReader)
    (rightCreated : BetaCreatedIncoming body redexSite rightReader)
    (same : SameChainRepresentation targetSelection leftChain rightChain) :
    target.labelAt leftReader=target.labelAt rightReader
 := by
  classical
  have history : History [redexSite] source target := .cons step (.nil target)
  obtain ⟨localTarget,localHistory,_erase,_targetMatches,edge,selection,geometry,all⟩ :=
    site.beta_evaluated_chain_residuals closed matching inputs flow positive balance rootDepth transparency
      relative normal history targetSelection
  obtain ⟨leftOut⟩ := all leftChain
  obtain ⟨rightOut⟩ := all rightChain
  let lm : {p : Path //p∈[leftReader]} := ⟨leftReader,by simp⟩
  let rm : {p : Path //p∈[rightReader]} := ⟨rightReader,by simp⟩
  have leftAt := leftOut.lookup lm
  have rightAt := rightOut.lookup rm
  change localTarget.subterm leftReader=some (leftOut.node lm) at leftAt
  change localTarget.subterm rightReader=some (rightOut.node rm) at rightAt
  have evalEq : selection.evalLabel edge (leftOut.node lm).label=
      selection.evalLabel edge (rightOut.node rm).label := by
    have blocks := leftOut.blocks_eq_of_target_images site geometry rightOut same
    simpa [EvaluatedChainResiduals.blocks,lm,rm] using blocks
  have lr := leftOut.reverse_reading_letter_blocks_regular site (init_is_INIT source.erase) localHistory lm
  have rr := rightOut.reverse_reading_letter_blocks_regular site (init_is_INIT source.erase) localHistory rm
  have parsed : revBlocks selection edge (leftOut.node lm).label=revBlocks selection edge (rightOut.node rm).label :=
    proper_ended_control_blocks_unique lr.2 rr.2 (lr.1.trans ((congrArg reverseEdges evalEq).trans rr.1.symm))
  cases localHistory with
  | cons localStep tail =>
    cases tail
    obtain ⟨lb,la,localBody,localArg,localRedex,_⟩ := localStep.head_lookups
    have eraseEq : source.erase=(initLabels source.erase).erase := (erase_initLabels source.erase).symm
    have heads := congrArg (fun t=>subtermAt t redexSite) eraseEq
    simp only [←LTerm.erase_subterm,redex,localRedex,Option.map_some,LTerm.erase] at heads
    have parts := Term.app.inj (Option.some.inj heads)
    have bodySame : body.erase=localBody.erase := Term.lam.inj parts.1
    have resultData (p : Path) (node : LTerm) (atNode : localTarget.subterm p=some node)
        (result : p=redexSite) (shape : ∃stamp inner,body=.lam stamp inner) :
        ∃first last,revBlocks selection edge node.label=[first,edge.reverseRoute,last] := by
      obtain ⟨stamp,inner,shape⟩ := shape
      subst body
      cases localBody with
      | var => cases bodySame
      | app => cases bodySame
      | lam stamp inner =>
        exact ⟨_,_,result_blocks selection edge localRedex localStep (result ▸ atNode)⟩
    rcases false_forms step redex nonoverlap leftRead leftChain leftCreated with ⟨leftResult,leftShape⟩|⟨lp,leftOccurs,leftCopy⟩
    · rcases false_forms step redex nonoverlap rightRead rightChain rightCreated with ⟨rightResult,rightShape⟩|⟨rp,rightOccurs,rightCopy⟩
      · rw [leftResult,rightResult]
      · obtain ⟨first,last,blocks⟩ := resultData leftReader _ leftAt leftResult leftShape
        have occurs : ArgumentOccurrence localBody.erase (rp++[.fn]) := by rw [←bodySame];exact rightOccurs
        obtain ⟨stamp,old,copyBlocks⟩ := copy_blocks selection edge localRedex localStep occurs (by simp) ((congrArg localTarget.subterm rightCopy).symm.trans rightAt)
        rw [blocks,copyBlocks] at parsed
        exact False.elim (principal_ne_reverse edge (List.cons.inj (List.cons.inj parsed).2).1.symm)
    · rcases false_forms step redex nonoverlap rightRead rightChain rightCreated with ⟨rightResult,rightShape⟩|⟨rp,rightOccurs,rightCopy⟩
      · obtain ⟨first,last,blocks⟩ := resultData rightReader _ rightAt rightResult rightShape
        have occurs : ArgumentOccurrence localBody.erase (lp++[.fn]) := by rw [←bodySame];exact leftOccurs
        obtain ⟨stamp,old,copyBlocks⟩ := copy_blocks selection edge localRedex localStep occurs (by simp) ((congrArg localTarget.subterm leftCopy).symm.trans leftAt)
        rw [copyBlocks,blocks] at parsed
        exact False.elim (principal_ne_reverse edge (List.cons.inj (List.cons.inj parsed).2).1)
      · have lcOccurs : ArgumentOccurrence localBody.erase (lp++[.fn]) := by rw [←bodySame];exact leftOccurs
        have rcOccurs : ArgumentOccurrence localBody.erase (rp++[.fn]) := by rw [←bodySame];exact rightOccurs
        obtain ⟨ls,lsAt,lblocks⟩ := copy_blocks selection edge localRedex localStep lcOccurs (by simp) ((congrArg localTarget.subterm leftCopy).symm.trans leftAt)
        obtain ⟨rs,rsAt,rblocks⟩ := copy_blocks selection edge localRedex localStep rcOccurs (by simp) ((congrArg localTarget.subterm rightCopy).symm.trans rightAt)
        rw [lblocks,rblocks] at parsed
        have reversed := (List.cons.inj (List.cons.inj (List.cons.inj parsed).2).2).1
        have oldEval : selection.evalLabel edge ls=selection.evalLabel edge rs := by
          have eq := congrArg reverseEdges reversed
          simpa only [reverseEdges_involutive] using eq
        have lc := substituted_function_old_chain redex leftOccurs
        have rc := substituted_function_old_chain redex rightOccurs
        let lpos := actualChainPosition lc ⟨(redexSite++[.fn,.body])++(lp++[.fn]),by simp⟩
        let rpos := actualChainPosition rc ⟨(redexSite++[.fn,.body])++(rp++[.fn]),by simp⟩
        have lold : (initLabels source.erase).subterm lpos.val=some (.var ls (binderDepth (lp++[.fn]))) := by
          change (initLabels source.erase).subterm ((redexSite++[.fn,.body])++(lp++[.fn]))=_
          rw [List.append_assoc,LTerm.subterm_append,localRedex]
          simpa only [LTerm.subterm,Option.bind_some] using lsAt
        have rold : (initLabels source.erase).subterm rpos.val=some (.var rs (binderDepth (rp++[.fn]))) := by
          change (initLabels source.erase).subterm ((redexSite++[.fn,.body])++(rp++[.fn]))=_
          rw [List.append_assoc,LTerm.subterm_append,localRedex]
          simpa only [LTerm.subterm,Option.bind_some] using rsAt
        obtain ⟨lenv,lctx,locc⟩ := SourceSubterm.of_lookup _ lold [] .external
        obtain ⟨renv,rctx,rocc⟩ := SourceSubterm.of_lookup _ rold [] .external
        have localMatching : Matches site.net root (initLabels source.erase).erase := by simpa only [erase_initLabels] using matching
        have leval := selection.evalLabel_occurrence_segments (init_is_INIT source.erase) localMatching matching locc (sourceSelection lpos) edge
        have reval := selection.evalLabel_occurrence_segments (init_is_INIT source.erase) localMatching matching rocc (sourceSelection rpos) edge
        have pieces : (sourceSelection lpos).fragment.segments=(sourceSelection rpos).fragment.segments := leval.symm.trans (oldEval.trans reval)
        have oldSame := same_pair_images sourceSelection lc rc pieces
        obtain ⟨iso⟩ := (sourceJoint.1 lc rc).mp oldSame
        have labels := actual_chain_labels_forward prefixHistory initial closed lc rc iso
        have firstLabels : source.labelAt lpos.val=source.labelAt rpos.val := by simpa only [List.map_cons,List.map_nil,List.cons.injEq,and_true] using (List.cons.inj labels).1
        let ln := (targetSelection (actualChainPosition leftChain lm)).term
        let rn := (targetSelection (actualChainPosition rightChain rm)).term
        have gl : target.subterm leftReader=some ln := (targetSelection (actualChainPosition leftChain lm)).occurrence.lookup
        have gr : target.subterm rightReader=some rn := (targetSelection (actualChainPosition rightChain rm)).occurrence.lookup
        have cl := gl
        have cr := gr
        rw [leftCopy,LTerm.subterm_append,step.contract_lookup redex,Option.bind_some] at cl
        rw [rightCopy,LTerm.subterm_append,step.contract_lookup redex,Option.bind_some] at cr
        obtain ⟨lstamp,lvar,lformula⟩ := LTerm.contract_argument_incoming_label leftOccurs cl
        obtain ⟨rstamp,rvar,rformula⟩ := LTerm.contract_argument_incoming_label rightOccurs cr
        have lsource : source.subterm lpos.val=some (.var lstamp (binderDepth (lp++[.fn]))) := by
          change source.subterm ((redexSite++[.fn,.body])++(lp++[.fn]))=_
          rw [List.append_assoc,LTerm.subterm_append,redex]
          simpa only [LTerm.subterm,Option.bind_some] using lvar
        have rsource : source.subterm rpos.val=some (.var rstamp (binderDepth (rp++[.fn]))) := by
          change source.subterm ((redexSite++[.fn,.body])++(rp++[.fn]))=_
          rw [List.append_assoc,LTerm.subterm_append,redex]
          simpa only [LTerm.subterm,Option.bind_some] using rvar
        have stamps : lstamp=rstamp := by
          simpa only [LTerm.labelAt,lsource,rsource,Option.map_some,LTerm.label,Option.some.injEq] using firstLabels
        simp only [if_neg (show lp++[Step.fn]≠[] by simp)] at lformula
        simp only [if_neg (show rp++[Step.fn]≠[] by simp)] at rformula
        simp only [LTerm.labelAt,gl,gr,Option.map_some,lformula,rformula,stamps]

#print axioms PathSite.one_step_nonoverlap_false_head_labels
end Lamping.AG
