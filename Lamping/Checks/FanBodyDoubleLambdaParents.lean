import Lamping.Lamping.FanCopiedLambdaContextCuts
import Lamping.Lamping.ActionSyntaxObservationKinds
import Lamping.Checks.FanBodyDoubleLambdaReachable
set_option maxHeartbeats 4000000
namespace Lamping.Checks.FanBodyDoubleLambdaParents
open AG Graph Lambda Lambda.Labelled FanBodyDoubleLambdaReachable

def oldBodyApp : (encode 0 term).N := .inr (.inl (.inr (.inl (.inl ()))))
def oldFnVar : (encode 0 term).N := .inr (.inl (.inr (.inr (.inl ()))))
def appKept : concrete.Kept := ⟨oldBodyApp,by constructor <;> intro h <;> cases h⟩
def varKept : concrete.Kept := ⟨oldFnVar,by constructor <;> intro h <;> cases h⟩
def wrapFnWire (w : (encode 0 (.lam (.app (.var 0) (.var 0)))).W) : (encode 0 term).W := .inl (.inr (.inl w))
def wrapBodyWire (w : (encode 0 (.app (.var 0) (.var 0))).W) : (encode 0 term).W := wrapFnWire (.inl (.inr w))
def appRootWire : (encode 0 term).W := wrapFnWire (.inr (.inl ()))
def fnVarWire : (encode 0 term).W := wrapBodyWire (.inr (.inl (.inl ())))
def fnInputWire : (encode 0 term).W := wrapBodyWire (.inr (.inl (.inr ⟨0,rfl⟩)))
def outsideRoot : concrete.Outside := ⟨appRootWire,by
  rintro ⟨d,h⟩;simp only [corridor,List.mem_cons,List.not_mem_nil,or_false] at h;rcases h with h|h <;> cases h⟩
def outsideFn : concrete.Outside := ⟨fnVarWire,by
  rintro ⟨d,h⟩;simp only [corridor,List.mem_cons,List.not_mem_nil,or_false] at h;rcases h with h|h <;> cases h⟩
def outsideInput : concrete.Outside := ⟨fnInputWire,by
  rintro ⟨d,h⟩;simp only [corridor,List.mem_cons,List.not_mem_nil,or_false] at h;rcases h with h|h <;> cases h⟩
theorem beta_root : concrete.site.reduce.wire (.inr (.inl (.inl ())))=
    .inr (.inr (.inr (.inl false),false)) := beta_lift_wire (.inr (.inl (.inl (.inl ()))) ) (.inr (.inl (.inr (.inl false)))) rfl
theorem beta_root_glue : concrete.site.reduce.wire (.inr (.inr (.inr (.inl false),true)))=
    .inr (.inr (.inr (.inr true),true)) := rfl
theorem beta_body : concrete.site.reduce.wire (.inr (.inr (.inr (.inr true),false)))=
    .inr (.inr (.inl (.inl outsideRoot),false)) := beta_lift_wire (.inr (.inl (.inr (.inr true)))) (.inr (.inr (outsideRoot,false))) rfl
theorem beta_app : concrete.site.reduce.wire (.inr (.inr (.inl (.inl outsideRoot),true)))=
    .inl ⟨.inl appKept,appCtx⟩ := beta_lift_wire (.inr (.inr (outsideRoot,true))) (.inl ⟨appKept,appCtx⟩) rfl
theorem beta_fn : concrete.site.reduce.wire (.inl ⟨.inl appKept,.inl ()⟩)=
    .inr (.inr (.inl (.inl outsideFn),false)) := beta_lift_wire (.inl ⟨appKept,.inl ()⟩) (.inr (.inr (outsideFn,false))) rfl
theorem beta_var_aux : concrete.site.reduce.wire (.inr (.inr (.inl (.inl outsideFn),true)))=
    .inl ⟨.inl varKept,.inr ()⟩ := beta_lift_wire (.inr (.inr (outsideFn,true))) (.inl ⟨varKept,.inr ()⟩) rfl
theorem beta_var_principal : concrete.site.reduce.wire (.inl ⟨.inl varKept,.inl ()⟩)=
    .inr (.inr (.inl (.inl outsideInput),true)) := beta_lift_wire (.inl ⟨varKept,.inl ()⟩) (.inr (.inr (outsideInput,true))) rfl
theorem beta_fan_aux : concrete.site.reduce.wire (.inr (.inr (.inl (.inl outsideInput),false)))=
    .inl ⟨rhsFan,.inr false⟩ := beta_lift_wire (.inr (.inr (outsideInput,false))) (.inl ⟨fanKept,.inr false⟩) rfl

def finalApp : outerFan.Kept := ⟨.inl appKept,by
  constructor <;> intro h <;> have hs:=congrArg Subtype.val (Sum.inl.inj h) <;> cases hs⟩
def finalVar : outerFan.Kept := ⟨.inl varKept,by
  constructor <;> intro h <;> have hs:=congrArg Subtype.val (Sum.inl.inj h) <;> cases hs⟩
def rootOutside : outerFan.Outside := ⟨.inr (.inl false),by
  rintro ⟨d,h⟩;simp only [outerCorridor,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with h|h|h|h|h <;> cases h⟩
def bodyOutside : outerFan.Outside := ⟨.inr (.inr true),by
  rintro ⟨d,h⟩;simp only [outerCorridor,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with h|h|h|h|h <;> cases h⟩
def appOutside : outerFan.Outside := ⟨.inl (.inl outsideRoot),by
  rintro ⟨d,h⟩;simp only [outerCorridor,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with h|h|h|h|h <;> cases h⟩
def fnOutside : outerFan.Outside := ⟨.inl (.inl outsideFn),by
  rintro ⟨d,h⟩;simp only [outerCorridor,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with h|h|h|h|h <;> cases h⟩
def inputOutside : outerFan.Outside := ⟨.inl (.inl outsideInput),by
  rintro ⟨d,h⟩;simp only [outerCorridor,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with h|h|h|h|h <;> cases h⟩
theorem outer_root : outerFan.site.reduce.wire (.inr (.inl (.inl ())))=
    .inr (.inr (.inl (.inl rootOutside),false)) := outer_lift_wire (.inr (.inl (.inl (.inl ())))) (.inr (.inr (rootOutside,false))) beta_root
theorem outer_root_glue : outerFan.site.reduce.wire (.inr (.inr (.inl (.inl rootOutside),true)))=
    .inr (.inr (.inl (.inl bodyOutside),true)) := outer_lift_wire (.inr (.inr (rootOutside,true))) (.inr (.inr (bodyOutside,true))) beta_root_glue
theorem outer_body : outerFan.site.reduce.wire (.inr (.inr (.inl (.inl bodyOutside),false)))=
    .inr (.inr (.inl (.inl appOutside),false)) := outer_lift_wire (.inr (.inr (bodyOutside,false))) (.inr (.inr (appOutside,false))) beta_body
theorem outer_app : outerFan.site.reduce.wire (.inr (.inr (.inl (.inl appOutside),true)))=
    .inl ⟨.inl finalApp,appCtx⟩ := outer_lift_wire (.inr (.inr (appOutside,true))) (.inl ⟨finalApp,appCtx⟩) beta_app
theorem outer_fn : outerFan.site.reduce.wire (.inl ⟨.inl finalApp,.inl ()⟩)=
    .inr (.inr (.inl (.inl fnOutside),false)) := outer_lift_wire (.inl ⟨finalApp,.inl ()⟩) (.inr (.inr (fnOutside,false))) beta_fn
theorem outer_var_aux : outerFan.site.reduce.wire (.inr (.inr (.inl (.inl fnOutside),true)))=
    .inl ⟨.inl finalVar,.inr ()⟩ := outer_lift_wire (.inr (.inr (fnOutside,true))) (.inl ⟨finalVar,.inr ()⟩) beta_var_aux
theorem outer_var_principal : outerFan.site.reduce.wire (.inl ⟨.inl finalVar,.inl ()⟩)=
    .inr (.inr (.inl (.inl inputOutside),true)) := outer_lift_wire (.inl ⟨finalVar,.inl ()⟩) (.inr (.inr (inputOutside,true))) beta_var_principal
theorem outer_fan_front : outerFan.site.reduce.wire (.inr (.inr (.inl (.inl inputOutside),false)))=
    .inr (.inr (.inr (.inl false),false)) := outer_lift_wire (.inr (.inr (inputOutside,false))) (.inr (.inl (.inr (.inl false)))) beta_fan_aux
theorem outer_copy_ctx : outerFan.site.reduce.wire (.inr (.inr (.inr (.inl false),true)))=
    .inl ⟨.inr (.inl false),.inl ()⟩ := rfl

noncomputable abbrev outerNet := outerFan.site.reduce
noncomputable def rootEdges : List (Endpoint outerNet) :=
  [.inr (.inl (.inl ())),.inr (.inr (.inl (.inl rootOutside),true)),
   .inr (.inr (.inl (.inl bodyOutside),false)),.inr (.inr (.inl (.inl appOutside),true))]
theorem rootLabels (a : Context) : Labelling outerNet rootEdges a a := by
  apply Labelling.cons (by rw [outer_root];exact .transparent _ false a)
  apply Labelling.cons (by rw [outer_root_glue];exact .transparent _ true a)
  exact .cons (by rw [outer_body];exact .transparent _ false a) (.single _ _)
theorem rootFinish : rootEdges.getLast?=some (outerNet.wire (.inl ⟨.inl finalApp,appCtx⟩)) := by
  have h:=congrArg outerNet.wire outer_app
  simp only [Pairing.involutive] at h
  exact congrArg some h
noncomputable def rootAccess : RootAccess outerNet (.inl ()) := by
  let flow := Classical.choose outer_certified
  exact ⟨rootEdges,⟨⟨⟨Context.empty,Context.empty,rootLabels _⟩,
    (rootLabels Context.empty).root_forward_of_flow flow (.inl ()) rfl rfl⟩,rfl,⟨.app,by
      unfold accessKind;rw [rootFinish];simp only [Option.bind_some,Pairing.involutive];rfl⟩⟩⟩
noncomputable def fnTail : List (Endpoint outerNet) :=
  [.inl ⟨.inl finalApp,.inl ()⟩,.inr (.inr (.inl (.inl fnOutside),true)),
   .inl ⟨.inl finalVar,.inl ()⟩,.inr (.inr (.inl (.inl inputOutside),false)),
   .inr (.inr (.inr (.inl false),true))]
theorem fnTailLabels : Labelling outerNet fnTail Context.empty Context.empty := by
  have emptyCro : Traversal 0 (.op .cro) (.inr ()) (.inl ()) Context.empty Context.empty := by
    simpa only [Context.cons_empty,Context.replace_zero] using
      (Traversal.direct (Passage.cro (i:=0) Context.empty Context.empty))
  apply Labelling.cons (by rw [outer_fn];exact .transparent _ false Context.empty)
  apply Labelling.cons (by rw [outer_var_aux];exact LabelledTurn.node (g:=outerNet) (.inl finalVar) _ _ emptyCro)
  apply Labelling.cons (by rw [outer_var_principal];exact .transparent _ true Context.empty)
  exact .cons (by rw [outer_fan_front];exact .transparent _ false Context.empty) (.single _ _)
noncomputable def lambdaEdges : List (Endpoint outerNet) := rootEdges++fnTail
theorem lambdaLabels : Labelling outerNet lambdaEdges Context.empty Context.empty :=
  (rootLabels Context.empty).append_seam fnTailLabels (by
    intro e f last first
    have he:=Option.some.inj (last.symm.trans rootFinish)
    have hf:=Option.some.inj first
    subst e;subst f
    rw [Pairing.involutive]
    exact LabelledTurn.node (g:=outerNet) (.inl finalApp) appCtx (.inl ()) (.direct (.appFun Context.empty)))
theorem lambdaWord : accessWord outerNet lambdaEdges=[.fn] := rfl
theorem lambdaFinish : lambdaEdges.getLast?=some (outerNet.wire (.inl ⟨.inr (.inl false),.inl ()⟩)) := by
  have h:=congrArg outerNet.wire outer_copy_ctx
  simp only [Pairing.involutive] at h
  exact congrArg some h
noncomputable def lambdaParent : RootAccess outerNet (.inl ()) := by
  let flow := Classical.choose outer_certified
  exact ⟨lambdaEdges,⟨⟨⟨Context.empty,Context.empty,lambdaLabels⟩,
    lambdaLabels.root_forward_of_flow flow (.inl ()) rfl rfl⟩,rfl,⟨.lam,by
      unfold accessKind;rw [lambdaFinish];simp only [Option.bind_some,Pairing.involutive];rfl⟩⟩⟩
#print axioms rootAccess
#print axioms lambdaParent
#print axioms lambdaWord
#print axioms lambdaFinish
noncomputable def bodyTail : List (Endpoint outerNet) :=
  [.inl ⟨.inr (.inl false),lamBody⟩,innerPrincipal,innerGlue,innerStep]
abbrev bodyOutput := InitialOffsets.fanAt 0 false Context.empty
theorem bodyTailLabels : Labelling outerNet bodyTail Context.empty bodyOutput := by
  have bodyStart : outerNet.wire (.inl ⟨.inr (.inl false),lamBody⟩)=
      .inl ⟨innerFanNode,.inr false⟩ := rfl
  apply Labelling.cons (by rw [bodyStart];exact LabelledTurn.node (g:=outerNet) innerFanNode _ _ (.direct (InitialOffsets.Event.apply_rel (.fan 0 false) Context.empty)))
  apply Labelling.cons (by rw [inner_start_wire];exact LabelledTurn.transparent (g:=outerNet) (.inr (.inr true)) true bodyOutput)
  exact .cons (by rw [inner_glue_wire];exact LabelledTurn.transparent (g:=outerNet) (.inl (.inl outsideBody2)) false bodyOutput) (.single _ _)
noncomputable def bodyEdges : List (Endpoint outerNet) := lambdaEdges++bodyTail
theorem bodyLabels : Labelling outerNet bodyEdges Context.empty bodyOutput :=
  lambdaLabels.append_seam bodyTailLabels (by
    intro e f last first
    have he:=Option.some.inj (last.symm.trans lambdaFinish)
    have hf:=Option.some.inj first
    subst e;subst f
    rw [Pairing.involutive]
    exact LabelledTurn.node (g:=outerNet) (.inr (.inl false)) (.inl ()) lamBody (.direct (.lamBody _)))
theorem bodyWord : accessWord outerNet bodyEdges=[.fn,.body] := rfl
theorem bodyFinish : bodyEdges.getLast?=some (outerNet.wire (.inl ⟨innerLambdaNode,.inl ()⟩)) := by
  have h:=congrArg outerNet.wire inner_finish_wire
  simp only [Pairing.involutive] at h
  exact congrArg some h
noncomputable def bodyChild : RootAccess outerNet (.inl ()) := by
  let flow := Classical.choose outer_certified
  exact ⟨bodyEdges,⟨⟨⟨Context.empty,bodyOutput,bodyLabels⟩,
    bodyLabels.root_forward_of_flow flow (.inl ()) rfl rfl⟩,rfl,⟨.lam,by
      unfold accessKind;rw [bodyFinish];simp only [Option.bind_some,Pairing.involutive];rfl⟩⟩⟩
#print axioms bodyChild
#print axioms bodyWord
#print axioms bodyFinish
noncomputable def innerSourceParent : RootAccess innerFan.site.net (.inl ()) :=
  innerFan.sourceIso.rootAccessBij (.inl ()) lambdaParent
theorem innerSourceWord : accessWord innerFan.site.net innerSourceParent.val=[.fn] :=
  (innerFan.sourceIso.accessWord lambdaParent.val).trans lambdaWord
theorem innerSourceNotPassive : innerSourceParent.val.getLast?≠
    some (innerFan.site.net.wire (.inl ⟨.inr (.inr ()),.inl ()⟩)) := by
  intro wrong
  have original := congrArg (fun xs=>xs.map innerFan.sourceIso.symm.ends) wrong
  change (innerSourceParent.val.getLast?).map innerFan.sourceIso.symm.ends=_ at original
  rw [←List.getLast?_map] at original
  have inverse : innerSourceParent.val.map innerFan.sourceIso.symm.ends=lambdaEdges := by
    simp only [innerSourceParent,NetIso.rootAccessBij,List.map_map]
    have same : (innerFan.sourceIso.symm.ends ∘ innerFan.sourceIso.ends)=id := funext innerFan.sourceIso.ends.left_inv
    change lambdaEdges.map (innerFan.sourceIso.symm.ends ∘ innerFan.sourceIso.ends)=_
    rw [same,List.map_id]
  rw [inverse,lambdaFinish] at original
  have ends := Option.some.inj original
  have h := congrArg outerNet.wire ends
  simp only [Pairing.involutive] at h
  change .inl ⟨.inr (.inl false),.inl ()⟩=outerNet.wire (innerFan.sourceIso.symm.ends
    (innerFan.site.net.wire (.inl ⟨.inr (.inr ()),.inl ()⟩))) at h
  rw [innerFan.sourceIso.symm.wiring,Pairing.involutive] at h
  cases h

theorem final_parent_kept (principal : SiteActionPrincipal innerFan.site) :
    ∃ (parent : RootAccess innerFan.site.reduce (.inl ()))
      (port : NodePort signature innerFan.Kept innerFan.kept),
      accessWord innerFan.site.reduce parent.val=[.fn] ∧
      parent.val.getLast?=some (innerFan.site.reduce.wire (.inl ⟨.inl port.1,port.2⟩)) := by
  obtain ⟨parent,word,sub,lookup,observes⟩ := Matches.observation _ actual_final_matches
    (show Position current.erase from ⟨[.fn],rfl⟩)
  have subEq : sub=FanBodyContextConsumer.K := Option.some.inj lookup.symm
  subst sub
  have typed : accessKind innerFan.site.reduce parent.val=some .lam := observes.1
  rcases innerFan.site.action_access_node_cases (.fan .lam 0 1 (by decide)) parent with kept |⟨node,port,passive,finish⟩
  · obtain ⟨port,finish⟩ := kept;exact ⟨parent,port,word,finish⟩
  · cases passive with
    | fan branch =>
      have actual := accessKind_at_actual_finish typed (.inr (.inl branch)) port finish
      cases port with
      | inr aux => cases aux <;> cases actual
      | inl u =>
        cases u
        obtain ⟨a,b,labels⟩ := parent.property.1.1
        obtain ⟨flow,_,_,_,_⟩ := outer_certified
        obtain ⟨_pending,oldPre,_contexts,_relation,_labels,sourceSplit,_last,_raw⟩ :=
          innerFan.site.fan_lambda_context_canonical_trim (innerFan.sourceIso.flowBalance flow)
            (.inl ()) rfl actual_inner_source_matches principal innerSourceParent parent
            (innerSourceWord.trans word.symm) branch finish labels
        apply False.elim
        apply innerSourceNotPassive
        rw [sourceSplit,List.getLast?_append,principal.last,Option.some_or]
noncomputable def innerSourceChild : RootAccess innerFan.site.net (.inl ()) :=
  innerFan.sourceIso.rootAccessBij (.inl ()) bodyChild
theorem innerChildWord : accessWord innerFan.site.net innerSourceChild.val=[.fn,.body] :=
  (innerFan.sourceIso.accessWord bodyChild.val).trans bodyWord
theorem innerChildFinish : innerSourceChild.val.getLast?=
    some (innerFan.site.net.wire (.inl ⟨.inr (.inr ()),.inl ()⟩)) := by
  change (bodyEdges.map innerFan.sourceIso.ends).getLast?=_
  rw [List.getLast?_map,bodyFinish]
  have mapped := innerFan.sourceIso.wiring (.inl ⟨innerLambdaNode,.inl ()⟩)
  rw [innerFan.sourceIso.node_end,innerFan.passive_port] at mapped
  exact congrArg some mapped

theorem final_child_copied (principal : SiteActionPrincipal innerFan.site) :
    ∃ (child : RootAccess innerFan.site.reduce (.inl ())) (branch : Bool),
      accessWord innerFan.site.reduce child.val=[.fn,.body] ∧
      child.val.getLast?=some (innerFan.site.reduce.wire (.inl ⟨.inr (.inl branch),.inl ()⟩)) := by
  obtain ⟨child,word,sub,lookup,observes⟩ := Matches.observation _ actual_final_matches
    (show Position current.erase from ⟨[.fn,.body],rfl⟩)
  have subEq : sub=Term.lam (.var 1) := Option.some.inj lookup.symm
  subst sub
  have typed : accessKind innerFan.site.reduce child.val=some .lam := observes.1
  rcases innerFan.site.action_access_node_cases (.fan .lam 0 1 (by decide)) child with kept |⟨node,port,passive,finish⟩
  · obtain ⟨⟨node,port⟩,finish⟩ := kept
    obtain ⟨a,b,labels⟩ := child.property.1.1
    obtain ⟨flow,_,_,_,_⟩ := outer_certified
    obtain ⟨_relation,_labels,oldFinish⟩ := innerFan.site.action_kept_canonical_access
      (.fan .lam 0 1 (by decide)) (innerFan.sourceIso.flowBalance flow) (.inl ()) rfl
      actual_inner_source_matches principal innerSourceChild child (innerChildWord.trans word.symm) node port finish labels
    have wrong := Option.some.inj (innerChildFinish.symm.trans oldFinish)
    have impossible := congrArg innerFan.site.net.wire wrong
    simp only [Pairing.involutive] at impossible
    cases impossible
  · cases passive with
    | fan branch =>
      have actual := accessKind_at_actual_finish typed (.inr (.inl branch)) port finish
      cases port with
      | inr aux => cases aux <;> cases actual
      | inl u => cases u;exact ⟨child,branch,word,finish⟩
#print axioms innerSourceNotPassive
#print axioms final_parent_kept
#print axioms innerChildFinish
#print axioms final_child_copied
end Lamping.Checks.FanBodyDoubleLambdaParents