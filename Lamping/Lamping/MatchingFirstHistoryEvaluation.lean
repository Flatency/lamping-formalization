import Lamping.Lambda.ContractumPositionOrigins
import Lamping.Lamping.HistorySelectedPrincipalWord
import Lamping.Lamping.MatchingSharedSyntaxEvaluation
import Lamping.Lamping.MatchingFirstInsertionCoherence
namespace Lamping.AG
open Graph Lambda Lambda.Labelled
section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable {g : Net signature N B W} {root : B}
private theorem labelled_lookup_of_erase {term : LTerm} {p : Path} {u : Term}
    (lookup : subtermAt term.erase p=some u) :
    ∃ sub,term.subterm p=some sub ∧sub.erase=u := by
  rw [←LTerm.erase_subterm] at lookup
  cases found : term.subterm p with
  | none => rw [found] at lookup; cases lookup
  | some sub => exact ⟨sub,rfl,by simpa only [found,Option.map_some,Option.some.injEq] using lookup⟩
private theorem endpoint_roles {T : Type} {canonical : T} {n m : N}
    {p : Port (g.label n).sort} {q : Port (g.label m).sort}
    (nodes : n=m) (left : HEq p canonical) (right : HEq q canonical) :
    (.inl ⟨n,p⟩ : Endpoint g)=.inl ⟨m,q⟩ := by
  subst m
  cases eq_of_heq (left.trans right.symm)
  rfl
private theorem parent_labels (edge : BetaEdge g) {pre : List (Endpoint g)} {a b : Context}
    (labels : Labelling g (pre++edge.principal) a b)
    (preEnd : pre.getLast?=some (g.wire (.inl ⟨edge.app,edge.appCtx⟩))) : Labelling g pre a b := by
  have nonempty : pre≠[] := by intro empty; rw [empty] at preEnd; cases preEnd
  obtain ⟨middle,before⟩ := labels.prefix nonempty
  have whole : Labelling g (pre++edge.principal) a middle := by
    apply before.append_seam (edge.principal_labeling middle)
    intro e f finish head
    have eEq := Option.some.inj (finish.symm.trans preEnd)
    have fEq := Option.some.inj (head.symm.trans edge.principalStart)
    rw [eEq,fEq,Pairing.involutive]
    exact edge.app_fun_turn middle
  exact whole.output_unique labels ▸ before

private theorem evaluated_original_copy
    {appStamp degree : Labelled.Label} {body argument : LTerm}
    {redex : RedexOcc (LTerm.app appStamp (.lam degree body) argument).erase}
    (source : ActualRedexAccess g root redex) (rootName : redex.val=[])
    (initial : INIT (LTerm.app appStamp (.lam degree body) argument))
    (matching : Matches g root (LTerm.app appStamp (.lam degree body) argument).erase)
    (selection : SourceEdgeSelection (LTerm.app appStamp (.lam degree body) argument) g root)
    (inputs : RootInputs g root) {boundary : B → Bool} (flow : FlowBalance g boundary)
    (positive : boundary root=true) {heights : B → Int} (balance : IndexedLevelBalance g heights)
    (rootDepth : heights root=0) (transparency : Transparency g root) (beta : BetaEdge g)
    (app : source.connection.app=beta.app) (lam : source.connection.lam=beta.lam)
    (principal : source.connection.edges=beta.principal)
    (degreeWord : selection.evalLabel beta degree=beta.principal)
    (q : Path) (occurs : ArgumentOccurrence body.erase q) (r : Position argument.erase) :
    ∃ es, (LTerm.contract appStamp degree body argument).sourceTrail selection.atomWord beta.principal beta.reverseRoute
        (q++r.val)=some es ∧GeneratedExpandedProperPath g root es ∧
      ∀ requested : Context,∃ output,CoherentExpandedCore g root es requested output ∧
        BetaDetourBlocks g es requested output 1 := by
  have lookup : subtermAt (LTerm.app appStamp (.lam degree body) argument).erase redex.val=
      some (.app (.lam body.erase) argument.erase) := by rw [rootName]; rfl
  obtain ⟨leaf,loop,initialInput,a,b,binding,leafWord,leafSplit,binder,_loopWord,childLabels⟩ :=
    source.bound_body_loop matching lookup q occurs
  have headerWord : selection.evalLabel beta appStamp=source.parent.val := by
    have eq := selection.original_access_evaluation (beta:=beta) initial matching
      (p:=[]) (sub:=.app appStamp (.lam degree body) argument) rfl source.parent
      (by simpa only [rootName] using source.parentWord)
    exact Option.some.inj eq
  obtain ⟨bodySub,bodyLookup,_bodyErase⟩ := labelled_lookup_of_erase occurs
  obtain ⟨bodyWord,bodyEval⟩ := LTerm.sourceTrail_exists selection.atomWord beta.principal beta.reverseRoute bodyLookup
  have leafEval := selection.original_access_evaluation (beta:=beta) initial matching
    (p:=[Step.fn,Step.body]++q) (sub:=bodySub)
    (by simpa only [List.cons_append,List.nil_append,LTerm.subterm] using bodyLookup) leaf
    (by simpa only [rootName,List.nil_append,List.cons_append] using leafWord)
  have loopEval : body.sourceTrail selection.atomWord beta.principal beta.reverseRoute q=some loop := by
    simp only [LTerm.sourceTrail,List.cons_append,List.nil_append,bodyEval,Option.map_some] at leafEval
    change some (selection.evalLabel beta appStamp++(selection.evalLabel beta degree++bodyWord))=some leaf.val at leafEval
    rw [headerWord,degreeWord,leafSplit,source.split,principal,List.append_assoc] at leafEval
    have equal : bodyWord=loop := List.append_cancel_left
      (List.append_cancel_left (Option.some.inj leafEval))
    simpa only [equal] using bodyEval
  obtain ⟨arg,_oldLeaf,_oldLoop,suffix,_a,_b,_binding,argSplit,_bodySplit,argWord,_word,_binder,
    _argGen,_bodyGen,_inserted⟩ :=
    source.generated_binding_insert_base matching beta app lam principal lookup q occurs
  let position : Position (LTerm.app appStamp (.lam degree body) argument).erase := ⟨[.arg]++r.val,by
    change (subtermAt argument.erase r.val).isSome=true
    exact r.property⟩
  obtain ⟨descendant,descendantWord,_⟩ := Matches.observation g matching position
  obtain ⟨rest,descendantSplit⟩ := matching.access_prefix arg descendant r.val (by
    simpa only [argWord,rootName,List.nil_append] using descendantWord)
  have actualArg : descendant.val=source.parent.val++beta.argEnd::(suffix++rest) := by
    rw [descendantSplit,argSplit]; simp only [List.append_assoc,List.cons_append]
  obtain ⟨argTerm,argTermLookup⟩ := Option.isSome_iff_exists.mp r.property
  obtain ⟨argSub,argSubLookup,_argErase⟩ := labelled_lookup_of_erase argTermLookup
  obtain ⟨argWordList,argEval⟩ := LTerm.sourceTrail_exists selection.atomWord beta.principal beta.reverseRoute argSubLookup
  have descendantEval := selection.original_access_evaluation (beta:=beta) initial matching
    (p:=[Step.arg]++r.val) (sub:=argSub)
    (by simpa only [List.cons_append,List.nil_append,LTerm.subterm] using argSubLookup) descendant descendantWord
  have tailEval : argument.sourceTrail selection.atomWord beta.principal beta.reverseRoute r.val=
      some (beta.argEnd::(suffix++rest)) := by
    simp only [LTerm.sourceTrail,List.cons_append,List.nil_append,argEval,Option.map_some] at descendantEval
    change some (selection.evalLabel beta appStamp++argWordList)=some descendant.val at descendantEval
    rw [headerWord,actualArg] at descendantEval
    have same := List.append_cancel_left (Option.some.inj descendantEval)
    simpa only [same] using argEval
  have ctx := endpoint_roles (g:=g) app source.contextPrincipal beta.appCtx_role
  have preEnd : source.parent.val.getLast?=some (g.wire (.inl ⟨beta.app,beta.appCtx⟩)) := by
    rw [←ctx]; exact source.parentFinish
  have before : Labelling g source.parent.val initialInput a := parent_labels beta
    (by simpa only [source.split,principal] using childLabels) preEnd
  have total := inputs.ordinary_insert_coherent_streams flow positive balance rootDepth
    (balance.nesting root rootDepth) transparency beta source.parent.val loop (suffix++rest)
    descendant actualArg binding (binder.trans lam) before source.parent.property.2.1 preEnd
  let es := source.parent.val++beta.principal++loop++beta.reverseRoute++[beta.argEnd]++(suffix++rest)
  refine ⟨es,?_,?_,total⟩
  · rw [LTerm.sourceTrail_contract_copy selection.atomWord beta.principal beta.reverseRoute
      appStamp degree occurs r.val,loopEval,tailEval]
    simp only [Option.bind_some,Option.map_some]
    change some (selection.evalLabel beta appStamp++beta.principal++loop++beta.reverseRoute++
      (beta.argEnd::(suffix++rest)))=some es
    rw [headerWord]
    simp only [es,List.append_assoc,List.singleton_append]
  · obtain ⟨output,core,_paired⟩ := total Context.empty
    exact (core.erase g).generated g


private theorem evaluated_original_retained
    {appStamp degree : Labelled.Label} {body argument : LTerm}
    (initial : INIT (LTerm.app appStamp (.lam degree body) argument))
    (matching : Matches g root (LTerm.app appStamp (.lam degree body) argument).erase)
    (selection : SourceEdgeSelection (LTerm.app appStamp (.lam degree body) argument) g root)
    (inputs : RootInputs g root) (beta : BetaEdge g)
    (degreeWord : selection.evalLabel beta degree=beta.principal)
    (p : Path) (old : Term) (oldLookup : subtermAt body.erase p=some old)
    (retained : (LTerm.contract appStamp degree body argument).sourceTrail selection.atomWord beta.principal beta.reverseRoute p=
      (body.sourceTrail selection.atomWord beta.principal beta.reverseRoute p).map (fun word =>
        selection.evalLabel beta appStamp++beta.principal++word)) :
    ∃ es,(LTerm.contract appStamp degree body argument).sourceTrail selection.atomWord beta.principal beta.reverseRoute p=some es ∧
      GeneratedExpandedProperPath g root es ∧∀ requested : Context,∃ output,CoherentExpandedCore g root es requested output ∧
        BetaDetourBlocks g es requested output 0 := by
  obtain ⟨sub,lookup,_erase⟩ := labelled_lookup_of_erase oldLookup
  let position : Position (LTerm.app appStamp (.lam degree body) argument).erase :=
    ⟨[.fn,.body]++p,by change (subtermAt body.erase p).isSome=true; rw [oldLookup]; rfl⟩
  obtain ⟨access,word,_⟩ := Matches.observation g matching position
  have originalEval := selection.original_access_evaluation (beta:=beta) initial matching
    (p:=[Step.fn,Step.body]++p) (sub:=sub)
    (by simpa only [List.cons_append,List.nil_append,LTerm.subterm] using lookup) access word
  obtain ⟨bodyWord,bodyEval⟩ := LTerm.sourceTrail_exists selection.atomWord beta.principal beta.reverseRoute lookup
  simp only [LTerm.sourceTrail,List.cons_append,List.nil_append,bodyEval,Option.map_some] at originalEval
  change some (selection.evalLabel beta appStamp++(selection.evalLabel beta degree++bodyWord))=some access.val at originalEval
  have currentEval : (LTerm.contract appStamp degree body argument).sourceTrail selection.atomWord beta.principal beta.reverseRoute p=
      some access.val := by
    rw [retained,bodyEval,Option.map_some]
    rw [degreeWord] at originalEval
    simpa only [List.append_assoc] using originalEval
  refine ⟨access.val,currentEval,.base access.property.1 access.property.2.1,?_⟩
  intro requested
  obtain ⟨output,labels⟩ := inputs.access access requested
  exact ⟨output,.base labels access.property.1.2 access.property.2.1,labels.detour_blocks g⟩
end
section
variable {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K → Graph.Label signature} {i : Nat}

/-- The FIRST actual root event of a selected relative development has a
shared evaluator image which is genuinely generated and coherently labelled
for every root input, at EVERY target syntax position. All principal/common-
prefix/loop certificates are derived from the original source and real event. -/
theorem PathSite.first_relative_root_evaluation
    (site : PathSite (.beta i) kept (B:=B) (W:=W) (V:=V))
    {root : B} {appStamp degree : Labelled.Label} {body argument : LTerm}
    (initial : INIT (LTerm.app appStamp (.lam degree body) argument))
    (closed : Closed (LTerm.app appStamp (.lam degree body) argument).erase)
    (matching : Matches site.net root (LTerm.app appStamp (.lam degree body) argument).erase)
    (inputs : RootInputs site.net root) {boundary : B → Bool} (flow : FlowBalance site.net boundary)
    (positive : boundary root=true) {heights : B → Int} (balance : IndexedLevelBalance site.net heights)
    (rootDepth : heights root=0) (transparency : Transparency site.net root)
    {marked : Marked}
    (relative : Marked.RelativeHistory [[]]
      (Marked.mark (site.betaSyntaxFiber root (LTerm.app appStamp (.lam degree body) argument).erase)
        (LTerm.app appStamp (.lam degree body) argument).erase) marked) :
    ∃ beta : BetaEdge site.net,beta.app=.inr (.inl ()) ∧beta.lam=.inr (.inr ()) ∧
      ∃ selection : SourceEdgeSelection (LTerm.app appStamp (.lam degree body) argument) site.net root,
      ∀ {p sub},(LTerm.contract appStamp degree body argument).subterm p=some sub →
      ∃ es,(LTerm.contract appStamp degree body argument).sourceTrail selection.atomWord beta.principal beta.reverseRoute p=some es ∧
        GeneratedExpandedProperPath site.net root es ∧∃ count,count≤1 ∧
        ∀ requested : Context,∃ output,CoherentExpandedCore site.net root es requested output ∧
          BetaDetourBlocks site.net es requested output count := by
  obtain ⟨beta,atApp,atLam,allWords⟩ := site.selected_principal_word initial matching
  have selected : SelectedDegree (LTerm.app appStamp (.lam degree body) argument)
      (site.betaSyntaxFiber root (LTerm.app appStamp (.lam degree body) argument).erase) degree :=
    relative_last_selected_degree initial relative (.nil _) (.root _ _ _ _) rfl
  obtain ⟨name,member,atDegree⟩ := selected
  have sameName : name=[] := LTerm.initial_degree_injective initial atDegree rfl
  subst name
  let redex : RedexOcc (LTerm.app appStamp (.lam degree body) argument).erase := ⟨[],⟨_,rfl,True.intro⟩⟩
  obtain ⟨source⟩ := matching.actual_redex_access redex
  have physical := (source.physical_selection_iff site.net root _ (.inr (.inl ())) (.inr (.inr ())) matching).mp member
  have app : source.connection.app=beta.app := physical.1.trans atApp.symm
  have lam : source.connection.lam=beta.lam := physical.2.trans atLam.symm
  have principal := source.connection.beta_principal_unique beta app lam
  let selection := matching.source_edge_selection closed
  have degreeWord := allWords selection degree ⟨[],member,rfl⟩
  refine ⟨beta,atApp,atLam,selection,?_⟩
  intro p sub lookup
  have bareLookup : subtermAt (Lambda.contract body.erase argument.erase) p=some sub.erase := by
    rw [←LTerm.erase_contract appStamp degree body argument,←LTerm.erase_subterm,lookup]
    rfl
  rcases subtermAt_contract_origins bareLookup with
    ⟨old,oldLookup,nonvar,_⟩ | ⟨k,j,oldLookup,outside,_,_⟩ | ⟨q,r,split,occurs,copyLookup⟩
  · obtain ⟨oldSub,oldSubLookup,oldErase⟩ := labelled_lookup_of_erase oldLookup
    have nonvariable : ∀ stamp k,oldSub≠.var stamp k := by
      intro stamp k same
      subst oldSub
      exact nonvar k oldErase.symm
    have retained := LTerm.sourceTrail_contract_nonvariable selection.atomWord beta.principal beta.reverseRoute
      appStamp degree oldSubLookup nonvariable argument
    obtain ⟨es,eval,generated,total⟩ := evaluated_original_retained initial matching selection inputs beta degreeWord
      p old oldLookup retained
    exact ⟨es,eval,generated,0,by omega,total⟩
  · have retained := LTerm.sourceTrail_contract_retained_variable selection.atomWord beta.principal beta.reverseRoute
      appStamp degree oldLookup outside argument
    obtain ⟨es,eval,generated,total⟩ := evaluated_original_retained initial matching selection inputs beta degreeWord
      p (.var k) oldLookup retained
    exact ⟨es,eval,generated,0,by omega,total⟩
  · have validArgument : (subtermAt argument.erase r).isSome=true := by
      rw [subtermAt_rename] at copyLookup
      cases found : subtermAt argument.erase r with
      | none => rw [found] at copyLookup; cases copyLookup
      | some term => rfl
    obtain ⟨es,eval,generated,total⟩ := evaluated_original_copy source rfl initial matching selection inputs
      flow positive balance rootDepth transparency beta app lam principal degreeWord q occurs ⟨r,validArgument⟩
    exact ⟨es,by simpa only [split] using eval,generated,1,by omega,total⟩
end
end Lamping.AG

