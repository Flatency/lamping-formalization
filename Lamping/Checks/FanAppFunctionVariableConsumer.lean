import Lamping.Lamping.FanAppFunctionVariableTransport
import Lamping.Checks.FanAppSuccessfulReachable
import Lamping.Checks.FanCurrentVariableBinders
set_option maxHeartbeats 4000000
namespace Lamping.Checks.FanAppFunctionVariableConsumer
open AG Graph Lambda Lambda.Labelled FanSuccessfulReachable FanAppSuccessfulReachable
open FanSuccessfulChains hiding current original
open FanLambdaChainPassageConsumer FanCurrentVariableBinderConsumer

-- The BODY fan is auxiliary true of the earlier fan-lambda, not the consumed binding fan.
def bodyRootWire : (encode 0 term).W := wrapArgWire (.inr (.inl ()))
def bodyRootOutside : concrete.Outside := ⟨bodyRootWire,by
  rintro ⟨d,h⟩;simp only [corridor,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with h|h <;> cases h⟩
theorem beta_body_start : concrete.site.reduce.wire (.inl ⟨rhsLambda,lamBody⟩)=
    .inr (.inr (.inl (.inl bodyRootOutside),false)) :=
  beta_lift_wire (.inl ⟨argKept,lamBody⟩) (.inr (.inr (bodyRootOutside,false))) rfl
theorem beta_body_finish : concrete.site.reduce.wire (.inr (.inr (.inl (.inl bodyRootOutside),true)))=
    .inl ⟨.inl appKept,appCtx⟩ :=
  beta_lift_wire (.inr (.inr (bodyRootOutside,true))) (.inl ⟨appKept,appCtx⟩) rfl

def bodyRootOutside2 : actualFanPresentation.Outside := ⟨.inl (.inl bodyRootOutside),by
  rintro ⟨d,h⟩;simp only [actualFanLambdaCorridor,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with h|h|h|h|h|h <;> cases h⟩
theorem lambda_body_exit : actualFanPresentation.site.reduce.wire
    (.inr (.inr (.inr (.inr true),false)))=.inr (.inr (.inl (.inl bodyRootOutside2),false)) :=
  action2_lift_wire (.inr (.inl (.inr (.inr true)))) (.inr (.inr (bodyRootOutside2,false))) beta_body_start
theorem lambda_body_finish : actualFanPresentation.site.reduce.wire
    (.inr (.inr (.inl (.inl bodyRootOutside2),true)))=.inl ⟨.inl appKept2,appCtx⟩ :=
  action2_lift_wire (.inr (.inr (bodyRootOutside2,true))) (.inl ⟨appKept2,appCtx⟩) beta_body_finish

def bodyControl3 : fanCro.Kept := ⟨.inr (.inr true),by constructor <;> intro h <;> cases h⟩
def bodyFront3 : fanCro.Outside := ⟨.inr (.inr true),by
  rintro ⟨d,h⟩;simp only [actualFanCroCorridor,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with h|h|h|h <;> cases h⟩
def bodyRoot3 : fanCro.Outside := ⟨.inl (.inl bodyRootOutside2),by
  rintro ⟨d,h⟩;simp only [actualFanCroCorridor,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with h|h|h|h <;> cases h⟩
theorem third_body_start (branch : Bool) : fanCro.site.reduce.wire
    (.inl ⟨.inl (SuccessfulAuxiliaryPhysicalPair.copiedLambda branch),lamBody⟩)=
    .inl ⟨.inl bodyControl3,.inr branch⟩ :=
  action3_lift_wire (.inl ⟨SuccessfulAuxiliaryPhysicalPair.copiedLambda branch,lamBody⟩) (.inl ⟨bodyControl3,.inr branch⟩) rfl
theorem third_body_control : fanCro.site.reduce.wire (.inl ⟨.inl bodyControl3,.inl ()⟩)=
    .inr (.inr (.inl (.inl bodyFront3),true)) :=
  action3_lift_wire (.inl ⟨bodyControl3,.inl ()⟩) (.inr (.inr (bodyFront3,true))) rfl
theorem third_body_exit : fanCro.site.reduce.wire (.inr (.inr (.inl (.inl bodyFront3),false)))=
    .inr (.inr (.inl (.inl bodyRoot3),false)) :=
  action3_lift_wire (.inr (.inr (bodyFront3,false))) (.inr (.inr (bodyRoot3,false))) lambda_body_exit
theorem third_body_finish : fanCro.site.reduce.wire (.inr (.inr (.inl (.inl bodyRoot3),true)))=
    .inl ⟨newAppNode,appCtx⟩ :=
  action3_lift_wire (.inr (.inr (bodyRoot3,true))) (.inl ⟨appKept3,appCtx⟩) lambda_body_finish

noncomputable def bodyTail (branch : Bool) : List (Endpoint fanCro.site.reduce) := [
 .inl ⟨.inl (SuccessfulAuxiliaryPhysicalPair.copiedLambda branch),lamBody⟩,
 .inl ⟨.inl bodyControl3,.inl ()⟩,
 .inr (.inr (.inl (.inl bodyFront3),false)),
 .inr (.inr (.inl (.inl bodyRoot3),true))]
theorem bodyTailLabels (branch : Bool) (a : Context) : Labelling fanCro.site.reduce (bodyTail branch) a (InitialOffsets.fanAt 0 branch a) := by
  apply Labelling.cons (by rw [third_body_start];exact LabelledTurn.node (g:=fanCro.site.reduce) (.inl bodyControl3) _ _ (.direct (InitialOffsets.Event.apply_rel (.fan 0 branch) a)))
  apply Labelling.cons (by rw [third_body_control];exact LabelledTurn.transparent (g:=fanCro.site.reduce) (.inl (.inl bodyFront3)) true _)
  exact .cons (by rw [third_body_exit];exact LabelledTurn.transparent (g:=fanCro.site.reduce) (.inl (.inl bodyRoot3)) false _) (.single _ _)
theorem bodyTailWord (branch : Bool) : (bodyTail branch).flatMap (arrivalWord fanCro.site.reduce)=[.body] := rfl
theorem bodyTailFinish (branch : Bool) : (bodyTail branch).getLast?=some (fanCro.site.reduce.wire (.inl ⟨newAppNode,appCtx⟩)) := by
  have h:=congrArg fanCro.site.reduce.wire third_body_finish
  simp only [Pairing.involutive] at h
  exact congrArg some h
noncomputable def bodyAppEdges (branch : Bool) := (SuccessfulAuxiliaryPhysicalPair.targetParent branch).val++bodyTail branch

theorem bodyAppWord (branch : Bool) : accessWord fanCro.site.reduce (bodyAppEdges branch)=starting branch := by
  obtain ⟨a,b,labels⟩ := (SuccessfulAuxiliaryPhysicalPair.targetParent branch).property.1.1
  rw [bodyAppEdges,accessWord_append _ _ _ labels.nonempty,
    SuccessfulAuxiliaryPhysicalPair.targetWord,bodyTailWord]
  cases branch <;> rfl

theorem bodyAppAccessProof (branch : Bool) : IsRootAccess fanCro.site.reduce (.inl ()) (bodyAppEdges branch) := by
  obtain ⟨a,b,labels⟩ := (SuccessfulAuxiliaryPhysicalPair.targetParent branch).property.1.1
  have whole := labels.append_seam (bodyTailLabels branch b) (by
    intro e f last first
    have he:=Option.some.inj (last.symm.trans (SuccessfulAuxiliaryPhysicalPair.targetFinish branch))
    have hf:=Option.some.inj first
    subst e;subst f;rw [Pairing.involutive]
    exact LabelledTurn.node (g:=fanCro.site.reduce) (.inl (SuccessfulAuxiliaryPhysicalPair.copiedLambda branch)) (.inl ()) lamBody (.direct (.lamBody b)))
  obtain ⟨flow,_,_,_,_⟩ := cro_certified
  have head : (bodyAppEdges branch).head?=some (.inr (.inl (.inl ()))) := by
    rw [bodyAppEdges,List.head?_append,(SuccessfulAuxiliaryPhysicalPair.targetParent branch).property.2.1,Option.some_or]
  have last : (bodyAppEdges branch).getLast?=some (fanCro.site.reduce.wire (.inl ⟨newAppNode,appCtx⟩)) := by
    rw [bodyAppEdges,List.getLast?_append,bodyTailFinish,Option.some_or]
  exact ⟨⟨⟨a,_,whole⟩,whole.root_forward_of_flow flow (.inl ()) head rfl⟩,head,⟨.app,by
    unfold accessKind;rw [last];simp only [Option.bind_some,Pairing.involutive];rfl⟩⟩
noncomputable def bodyAppParent (branch : Bool) : RootAccess fanCro.site.reduce (.inl ()) := ⟨bodyAppEdges branch,bodyAppAccessProof branch⟩
noncomputable def sourceAppParent (branch : Bool) : RootAccess fanApp.site.net (.inl ()) :=
  fanApp.sourceIso.rootAccessBij (.inl ()) (bodyAppParent branch)
theorem sourceAppWord (branch : Bool) : accessWord fanApp.site.net (sourceAppParent branch).val=starting branch :=
  (fanApp.sourceIso.accessWord (bodyAppParent branch).val).trans (bodyAppWord branch)
theorem sourceAppFinish (branch : Bool) : (sourceAppParent branch).val.getLast?=
    some (fanApp.site.net.wire (.inl ⟨.inr (.inr ()),appCtx⟩)) := by
  change ((bodyAppParent branch).val.map fanApp.sourceIso.ends).getLast?=_
  have last : (bodyAppParent branch).val.getLast?=some (fanCro.site.reduce.wire (.inl ⟨newAppNode,appCtx⟩)) := by
    change (bodyAppEdges branch).getLast?=_
    rw [bodyAppEdges,List.getLast?_append,bodyTailFinish,Option.some_or]
  rw [List.getLast?_map,last]
  simp only [Option.map_some]
  apply congrArg some
  rw [fanApp.sourceIso.wiring]
  apply congrArg fanApp.site.net.wire
  apply fanApp.sourceIso.symm.ends.injective
  change fanApp.sourceIso.ends.invFun (fanApp.sourceIso.ends.toFun (.inl ⟨newAppNode,appCtx⟩))=_
  rw [fanApp.sourceIso.ends.left_inv]
  rfl
noncomputable def targetAppParent (branch : Bool) : RootAccess fanApp.site.reduce (.inl ()) :=
  Classical.choose (Matches.observation fanApp.site.reduce FanAppSuccessfulReachable.actual_target_matches
    (⟨starting branch,by cases branch <;> rfl⟩ : Position current.erase))
theorem targetAppWord (branch : Bool) : accessWord fanApp.site.reduce (targetAppParent branch).val=starting branch :=
  (Classical.choose_spec (Matches.observation fanApp.site.reduce FanAppSuccessfulReachable.actual_target_matches
    (⟨starting branch,by cases branch <;> rfl⟩ : Position current.erase))).1

-- The actual SOURCE finish excludes the kept alternative: target Ne is not inverted.
theorem targetAppCopied (branch : Bool) : ∃ copy : Bool,
    (targetAppParent branch).val.getLast?=some (fanApp.site.reduce.wire (.inl ⟨.inr (.inl copy),appCtx⟩)) := by
  rcases fanApp.site.fan_app_access_cases (targetAppParent branch) with ⟨port,finish⟩|copied
  · obtain ⟨flow,_,_,_,_⟩ := cro_certified
    obtain ⟨principal⟩ := fanApp.site.actionPrincipal_exists
    obtain ⟨a,b,labels⟩ := (targetAppParent branch).property.1.1
    obtain ⟨_,_,sourceFinish⟩ := fanApp.site.action_kept_canonical_access (.fan .app 0 1 (by decide))
      (fanApp.sourceIso.flowBalance flow) (.inl ()) rfl FanAppSuccessfulReachable.actual_source_matches principal
      (sourceAppParent branch) (targetAppParent branch) ((sourceAppWord branch).trans (targetAppWord branch).symm)
      port.1 port.2 finish labels
    have wired := congrArg fanApp.site.net.wire (Option.some.inj ((sourceAppFinish branch).symm.trans sourceFinish))
    simp only [Pairing.involutive] at wired
    have nodes := congrArg Sigma.fst (Sum.inl.inj wired)
    cases nodes
  · exact copied

-- The copied-parent domain is certified above; a concrete expanded low-cut
-- existential is not claimed. The natural top internally consumes the accepted cut.
/-- Complete natural top at the true fourth event and real variable slot0. -/
theorem actual_successful_variable_forward
    (principal : SiteActionPrincipal fanApp.site)
    (source : OccurrenceFragmentSelection current fanApp.site.net (.inl ()))
    (firstTarget secondTarget : OccurrenceFragmentSelection current fanApp.site.reduce (.inl ())) (branch : Bool) :
    (firstTarget (variablePosition branch)).fragment.segments=(secondTarget (variablePosition branch)).fragment.segments := by
  obtain ⟨flow,_,inputs,_,_⟩ := cro_certified
  exact fanApp.site.fan_app_function_variable_same_slot_forward FanAppSuccessfulReachable.actual_source_matches
    FanAppSuccessfulReachable.actual_target_matches (fanApp.sourceIso.flowBalance flow) rfl
    (fanApp.sourceIso.rootInputs inputs) principal source (actualChain branch) (actualChain branch) rfl
    (variablePosition branch) (variablePosition branch) (actual_function_slots branch).2.1 (actual_function_slots branch).2.1
    (variable_lookup branch) (variable_lookup branch) (firstTarget (variablePosition branch)) (secondTarget (variablePosition branch))

theorem actual_reachable_function_variable_transport :
    INIT original ∧Closed original.erase ∧History [[.fn]] original current ∧
    GraphTrace (ActualNet.initial term) (ActualNet.ofNet fanApp.site.reduce)
      [.beta 0,.fanAction .lam 0 1 (by decide),.fanAction .cro 0 1 (by decide),.fanAction .app 0 1 (by decide)] ∧
    Matches fanApp.site.net (.inl ()) current.erase ∧Matches fanApp.site.reduce (.inl ()) current.erase ∧
    Nonempty (OccurrenceFragmentSelection current fanApp.site.net (.inl ())) ∧
    Nonempty (OccurrenceFragmentSelection current fanApp.site.reduce (.inl ())) ∧
    ∃ principal : SiteActionPrincipal fanApp.site,
      ∀ (firstSource secondSource : OccurrenceFragmentSelection current fanApp.site.net (.inl ()))
        (firstTarget secondTarget : OccurrenceFragmentSelection current fanApp.site.reduce (.inl ())) (branch : Bool),
      PrerequisiteChain current (starting branch) (fullEdges branch) ∧
      (fullEdges branch).length=(if branch then 5 else 4) ∧
      (fullEdges branch)[0]?=some (variablePath branch) ∧
      (firstSource (variablePosition branch)).fragment.segments=(secondSource (variablePosition branch)).fragment.segments ∧
      (firstTarget (variablePosition branch)).fragment.segments=(secondTarget (variablePosition branch)).fragment.segments ∧
      (∃ copy,(targetAppParent branch).val.getLast?=some (fanApp.site.reduce.wire (.inl ⟨.inr (.inl copy),appCtx⟩))) := by
  refine ⟨FanSuccessfulChains.initial,sourceClosed,actualHistory,FanAppSuccessfulReachable.actual_four_step_trace,
    FanAppSuccessfulReachable.actual_source_matches,FanAppSuccessfulReachable.actual_target_matches,
    FanAppSuccessfulReachable.actual_source_matches.occurrence_fragment_selection targetClosed,
    FanAppSuccessfulReachable.actual_target_matches.occurrence_fragment_selection targetClosed,?_⟩
  obtain ⟨principal⟩ := fanApp.site.actionPrincipal_exists
  refine ⟨principal,?_⟩
  intro firstSource secondSource firstTarget secondTarget branch
  exact ⟨actualChain branch,(by cases branch <;> rfl),(actual_function_slots branch).2.1,
    OccurrenceFragment.segments_unique FanAppSuccessfulReachable.actual_source_matches _ _,
    actual_successful_variable_forward principal firstSource firstTarget secondTarget branch,targetAppCopied branch⟩
end Lamping.Checks.FanAppFunctionVariableConsumer
#print axioms Lamping.AG.SourceEdgeFragment.fan_app_copied_function_kept_forward
#print axioms Lamping.AG.PathSite.fan_app_function_variable_same_slot_forward
#print axioms Lamping.Checks.FanAppFunctionVariableConsumer.bodyTailLabels
#print axioms Lamping.Checks.FanAppFunctionVariableConsumer.sourceAppFinish
#print axioms Lamping.Checks.FanAppFunctionVariableConsumer.targetAppCopied
#print axioms Lamping.Checks.FanAppFunctionVariableConsumer.actual_successful_variable_forward
#print axioms Lamping.Checks.FanAppFunctionVariableConsumer.actual_reachable_function_variable_transport
