import Lamping.Lamping.ExecutableTraversal
import Lamping.Lamping.Encoding
import Lamping.Lamping.ReadbackCorrectness
import Lamping.Lamping.ReadbackMachine
import Lamping.Lamping.ExecutableEncoding
import Lamping.Lamping.ReadbackScanSimulation
import Lamping.Lamping.InitialPathControls
import Lamping.Lamping.ReadbackBinderCandidates
import Lamping.Lamping.ReadbackFramedPaths
import Lamping.Lamping.InitialTransparency
import Lamping.Lamping.InitialBindingSuffix
import Lamping.Lamping.ReadbackMatchedAccess
import Lamping.Lamping.InitialFullIndependence
import Lamping.Lamping.ReadbackReady
import Lamping.Lamping.ReadbackTermination
import Lamping.Lamping.ExecutableReadback
import Lamping.Lamping.BetaEncodingIso
namespace Lamping.Checks.Readback
open Lamping AG Graph AG.Readback

example : executeControl 0 (.op .fan) fanO [.star .empty]=
    some (.inl (),[.o (.star .empty)]) := rfl
example : executeControl 0 (.op .fan) fanStar [.o .empty]=
    some (.inl (),[.star (.o .empty)]) := rfl
example : executeControl 0 (.op .fan) (.inl ()) [.o (.star .empty)]=
    some (fanO,[.star .empty]) := rfl
example : executeControl 0 (.op .fan) (.inl ()) [.star (.o .empty)]=
    some (fanStar,[.o .empty]) := rfl
example : executeControl 0 (.op .fan) (.inl ()) [.pair .empty .empty]=none := rfl
example : executeControl 1 (.op .cro) (.inr ()) [.o .empty,.star .empty]=
    some (.inl (),[.o .empty,.empty,.star .empty]) := rfl
example : executeControl 1 (.op .cro) (.inl ()) [.o .empty,.empty,.star .empty]=
    some (.inr (),[.o .empty,.star .empty]) := rfl
example : executeControl 1 (.op .cro) (.inl ()) [.o .empty,.star .empty]=none := rfl
example : executeControl 0 (.op .bra) (.inr ()) [.o .empty,.star .empty]=
    some (.inl (),[.pair (.star .empty) (.o .empty)]) := rfl
example : executeControl 0 (.op .bra) (.inl ()) [.pair (.star .empty) (.o .empty)]=
    some (.inr (),[.o .empty,.star .empty]) := rfl
example : executeControl 0 (.op .bra) (.inl ()) [.o .empty]=none := rfl
example : executeControl 20 (.op .cro) (.inr ()) [.star .empty]=
    some (.inl (),[.star .empty]) := rfl

private abbrev identityNet := (encode 0 (.lam (.var 0))).net
private abbrev root : Endpoint identityNet := .inr (.inl (.inl ()))
/-- Raw executable wire traversal reaches the actual lambda context. -/
theorem initial_lambda_scan : scanOne identityNet root []=
    .terminal ⟨.inl (),.inl ()⟩ .lam [] := rfl
/-- The actual Cro and both subdivision vertices are executed. A small
fuel budget exhausts; enough fuel observes the original binding port. -/
theorem actual_binding_scan : scanFuel identityNet 4 (.inl ⟨.inl (),lamBody⟩) []=
    .stopped (.terminal ⟨.inl (),lamBind⟩ .var []) := rfl
theorem short_scan_is_not_done : scanFuel identityNet 3 (.inl ⟨.inl (),lamBody⟩) []=
    .exhausted (.inr (.inr (.inr (.inr ⟨0,rfl⟩),false))) [] := rfl

theorem actual_bra_semantics : Traversal 0 (.op .bra) (.inl ()) (.inr ())
    (Context.ofList [.pair (.star .empty) (.o .empty)])
    (Context.ofList [.o .empty,.star .empty]) :=
  executeControl_sound 0 (.op .bra) (.inl ()) (.inr ()) _ _ rfl

theorem actual_high_cro_semantics : Traversal 20 (.op .cro) (.inr ()) (.inl ())
    (Context.ofList [.star .empty]) (Context.ofList [.star .empty]) :=
  executeControl_sound 20 (.op .cro) (.inr ()) (.inl ()) _ _ rfl

#print axioms ContextData.denote_replaceTail
#print axioms executeControl_sound
#print axioms actual_bra_semantics
#print axioms actual_high_cro_semantics
#print axioms executeControl
#print axioms scanOne
#print axioms scanFuel
#print axioms initial_lambda_scan
#print axioms actual_binding_scan
#print axioms short_scan_is_not_done

theorem identity_readback : readbackFuel identityNet (.inl ()) 7 =
    .done (.lam (.var 0)) := rfl

private abbrev shadowNet := (encode 0 (.lam (.lam (.var 1)))).net
theorem outer_variable_readback : readbackFuel shadowNet (.inl ()) 40 =
    .done (.lam (.lam (.var 1))) := rfl

private abbrev duplicateNet := (encode 0 (.lam (.app (.var 0) (.var 0)))).net
theorem fan_readback : readbackFuel duplicateNet (.inl ()) 80 =
    .done (.lam (.app (.var 0) (.var 0))) := rfl

private abbrev applicationNet :=
  (encode 0 (.app (.lam (.var 0)) (.lam (.var 0)))).net
theorem application_readback : readbackFuel applicationNet (.inl ()) 80 =
    .done (.app (.lam (.var 0)) (.lam (.var 0))) := rfl

private def identityFrame : BinderFrame identityNet :=
  ⟨.inl (),0,[root],.inl ⟨.inl (),lamBody⟩,[]⟩
private def identityLeaf : List (Endpoint identityNet) :=
  [root,.inl ⟨.inl (),lamBody⟩]

theorem zero_shell_does_not_choose_last_node :
    binderCandidates identityNet [identityFrame,identityFrame] (.inl ()) identityLeaf []=[0,1] := rfl

theorem no_frame_is_no_binder :
    binderCandidates identityNet [] (.inl ()) identityLeaf []=[] := rfl

theorem wrong_literal_occurrence_rejected :
    binderCandidates identityNet [{identityFrame with stem:=identityLeaf}]
      (.inl ()) identityLeaf []=[] := rfl

theorem actual_terminal_metadata :
    identityNet.wire root=.inl ⟨.inl (),.inl ()⟩ ∧
      portKind (identityNet.label (.inl ())).sort (.inl ())=some .lam ∧
        ([] : ContextData)=[] :=
  scanOne_terminal_sound identityNet root _ .lam [] [] initial_lambda_scan

private def bodyAfterWire : Endpoint identityNet :=
  match identityNet.wire (.inl ⟨.inl (),lamBody⟩) with
  | .inr (.inr (vertex,direction)) => .inr (.inr (vertex,!direction))
  | _ => root

theorem actual_transparent_scanner_turn :
    LabelledTurn identityNet (identityNet.wire (.inl ⟨.inl (),lamBody⟩)) bodyAfterWire
      (Context.ofList []) (Context.ofList []) :=
  scanOne_next_sound identityNet _ bodyAfterWire [] [] rfl

theorem zero_fuel_not_a_readback : readbackFuel identityNet (.inl ()) 0 =
    .exhausted (initialState identityNet (.inl ())) := rfl

#print axioms machineStep
#print axioms encodedCarrierEquality
#print axioms readbackFuel
#print axioms identity_readback
#print axioms outer_variable_readback
#print axioms fan_readback
#print axioms application_readback
#print axioms zero_shell_does_not_choose_last_node
#print axioms scanOne_next_sound
#print axioms scanOne_terminal_sound
#print axioms actual_terminal_metadata
#print axioms actual_transparent_scanner_turn

/-- Consume the simulation theorem with the real finite initial binding loop,
not just a direct evaluation of the scanner definition. -/
theorem actual_fixed_binding_access_simulation :
    ∃ data,Context.ofList data=Context.empty ∧
      scanFuel identityNet 4 (.inl ⟨.inl (),lamBody⟩) []=
        .stopped (.terminal ⟨.inl (),lamBind⟩ .var data) := by
  let loop := identityBindingLoop 0 Context.empty Context.empty
  obtain ⟨first,data,headEq,output,run⟩ := scanFuel_of_empty_word loop.proper loop.forward
    rfl _ loop.finish ⟨.inl (),lamBind⟩ .var (identityNet.pairing _) rfl [] (by simp)
  have firstEq : first=(.inl ⟨.inl (),lamBody⟩ : Endpoint identityNet) := by
    simpa using headEq.symm
  subst first
  exact ⟨data,by simpa using output,run⟩

#print axioms executeControl_complete
#print axioms scanOne_next_complete
#print axioms scanFuel_of_empty_word
#print axioms actual_fixed_binding_access_simulation

private def identityBodyEdges : List (Endpoint identityNet) :=
  [.inl ⟨.inl (),lamBody⟩,
   .inr (.inr (.inr (.inl ()),true)),
   .inl ⟨.inr (),.inl ()⟩,
   .inr (.inr (.inr (.inr ⟨0,rfl⟩),false))]
private def identityWhole : List (Endpoint identityNet) := [root]++identityBodyEdges

private theorem identityWhole_labels :
    Labelling identityNet identityWhole Context.empty Context.empty := by
  have bodyLabels : Labelling identityNet identityBodyEdges Context.empty Context.empty := by
    simpa using (identityBindingLoop 0 Context.empty Context.empty).proper
  exact .cons (LabelledTurn.node (g:=identityNet) (.inl ()) (.inl ()) lamBody
    (.direct (.lamBody Context.empty))) bodyLabels

private theorem identityWhole_forward : Forward identityNet identityWhole :=
  .node (.inl ()) (.inl ()) lamBody rfl rfl ⟨rfl,rfl⟩
    (identityBindingLoop 0 Context.empty Context.empty).forward

theorem actual_frame_cuts_binding_suffix : BindingSuffix identityNet identityWhole 0 := by
  obtain ⟨tail,split,bound⟩ := frame_binding_suffix identityFrame identityWhole [] []
    (.inl ()) lamBody lamBind rfl HEq.rfl HEq.rfl HEq.rfl rfl rfl rfl
      identityWhole_labels identityWhole_forward (.single root _) rfl rfl rfl
  have tailEq : tail=identityBodyEdges.tail := by
    have stripped := (List.cons.inj (List.cons.inj split).2).2
    exact stripped.symm
  subst tail
  exact bound

theorem actual_runtime_candidate_reflection :
    ∃ frame,(frame,0)∈[identityFrame].zipIdx ∧frame.node=(.inl ()) ∧
      Context.SameShell frame.index (Context.ofList frame.seam) (Context.ofList []) ∧
        ∃ tail,identityWhole=frame.stem++frame.bodyDeparture::tail :=
  (mem_binderCandidates [identityFrame] (.inl ()) identityWhole [] 0).mp (by decide)

#print axioms endpointSame_iff
#print axioms mem_binderCandidates
#print axioms frame_binding_suffix
#print axioms actual_frame_cuts_binding_suffix

private theorem identity_framed_path :
    FramedPath identityNet (.inl ()) [] identityWhole [] [identityFrame] := by
  have start : FramedPath identityNet (.inl ()) [] [root] [] [] := .initial
  have body : FramedPath identityNet (.inl ()) []
      [root,.inl ⟨.inl (),lamBody⟩] [] [identityFrame] :=
    .body start rfl (.inl ()) (.inl ()) lamBody rfl HEq.rfl HEq.rfl rfl
  have first : FramedPath identityNet (.inl ()) []
      [root,.inl ⟨.inl (),lamBody⟩,.inr (.inr (.inr (.inl ()),true))] [] [identityFrame] :=
    .scan body rfl rfl
  have second : FramedPath identityNet (.inl ()) []
      [root,.inl ⟨.inl (),lamBody⟩,.inr (.inr (.inr (.inl ()),true)),
        .inl ⟨.inr (),.inl ()⟩] [] [identityFrame] :=
    .scan first rfl rfl
  exact .scan second rfl rfl

theorem actual_trace_candidates_singleton :
    binderCandidates identityNet [identityFrame] (.inl ()) identityWhole []=[0] := by
  have observed : Observes identityNet identityWhole (.var 0) :=
    encode_observes_var_of_suffix (.lam (.var 0)) 0 rfl actual_frame_cuts_binding_suffix
  exact FramedPath.observed_candidates_singleton identityNet identity_framed_path
    (encode_closed_transparency (.lam (.var 0)) (Nat.zero_lt_succ 0) 0)
      ⟨.inl (),lamBind⟩ rfl rfl 0 observed

theorem actual_body_event_present :
    ∃ (frame : BinderFrame identityNet) (distance : Nat),
      [identityFrame][distance]?=some frame ∧frame.stem=[root] ∧
        frame.bodyDeparture=(.inl ⟨.inl (),lamBody⟩ : Endpoint identityNet) :=
  FramedPath.body_frame_exists identityNet identity_framed_path [root]
    (.inl ⟨.inl (),lamBody⟩) identityBodyEdges.tail rfl rfl

#print axioms FramedPath.frame_origin
#print axioms FramedPath.frame_cut
#print axioms FramedPath.body_frame_exists
#print axioms FramedPath.candidate_binding_suffix
#print axioms FramedPath.observed_candidate_exists
#print axioms FramedPath.observed_candidates_singleton
#print axioms actual_trace_candidates_singleton

private def identityParent : RootAccess identityNet (.inl ()) :=
  ⟨[root],⟨⟨⟨Context.empty,Context.empty,.single root _⟩,.single root⟩,rfl,.lam,rfl⟩⟩
private def identityChild : RootAccess identityNet (.inl ()) :=
  ⟨identityWhole,⟨⟨⟨Context.empty,Context.empty,identityWhole_labels⟩,
    identityWhole_forward⟩,rfl,.var,rfl⟩⟩

theorem actual_root_scan_builds_ready_trace :
    FramedPath identityNet (.inl ()) [] identityParent.val [] [] := by
  obtain ⟨arrival,kind,data,run,trace,_labels,_finish,_terminal⟩ := RootAccess.scan_root
    identityParent (encode_closed_independence (.lam (.var 0)) (Nat.zero_lt_succ 0) 0).rootInputs rfl []
  change (ScanRun.stopped (.terminal ⟨.inl (),.inl ()⟩ .lam []) : ScanRun identityNet)=
    .stopped (.terminal arrival kind data) at run
  have dataEq := (ScanResult.terminal.inj (ScanRun.stopped.inj run)).2.2
  rw [←dataEq] at trace
  exact trace

theorem actual_matching_child_scan :
    ∃ data,Labelling identityNet identityWhole Context.empty (Context.ofList data) ∧
      scanFuel identityNet 4 (.inl ⟨.inl (),lamBody⟩) []=
        .stopped (.terminal ⟨.inl (),lamBind⟩ .var data) := by
  have matching := encode_closed_matches (.lam (.var 0)) (Nat.zero_lt_succ 0) 0
  have inputs := (encode_closed_independence (.lam (.var 0)) (Nat.zero_lt_succ 0) 0).rootInputs
  obtain ⟨node,ctx,departure,tail,arrival,kind,data,_roles,_parentEnd,split,run,labels,finish,terminal⟩ :=
    Matches.scan_child matching inputs identityParent identityChild .body rfl Context.empty [] (.single root _)
  have suffixEq : ((.inl ⟨node,departure⟩)::tail : List (Endpoint identityNet))=identityBodyEdges :=
    (List.cons.inj split).2.symm
  have headEq := (List.cons.inj suffixEq).1
  have lengthEq : tail.length+1=4 := by simpa only [List.length_cons] using congrArg List.length suffixEq
  have endpointEq : (.inl arrival : Endpoint identityNet)=.inl ⟨.inl (),lamBind⟩ := by
    have wired : identityNet.wire (.inl arrival)=identityNet.wire (.inl ⟨.inl (),lamBind⟩) :=
      Option.some.inj (finish.symm.trans rfl)
    have same := congrArg identityNet.wire.mate wired
    simpa only [Pairing.involutive] using same
  have arrivalEq := Sum.inl.inj endpointEq
  subst arrival
  have kindEq : .var=kind := Option.some.inj terminal
  subst kind
  exact ⟨data,labels,by simpa only [headEq,lengthEq] using run⟩

#print axioms RootAccess.scan_root
#print axioms Matches.scan_child
#print axioms FramedPath.follow_empty_word
#print axioms actual_root_scan_builds_ready_trace
#print axioms actual_matching_child_scan

private def identityBeforeBinding : List (Endpoint identityNet) :=
  [root,.inl ⟨.inl (),lamBody⟩,.inr (.inr (.inr (.inl ()),true)),.inl ⟨.inr (),.inl ()⟩]
private def identityBindingDeparture : Endpoint identityNet :=
  .inr (.inr (.inr (.inr ⟨0,rfl⟩),false))

private theorem identityVariableReady : ReadyAccess [] identityChild identityBindingDeparture
    identityBeforeBinding [] [identityFrame] := ⟨rfl,identity_framed_path⟩

theorem actual_variable_step_from_binding_proof :
    machineStep identityNet
      ⟨[.read identityBindingDeparture [] identityBeforeBinding [identityFrame]],[]⟩=
        .next ⟨[],[.var 0]⟩ := by
  have observes : Observes identityNet identityWhole (.var 0) :=
    encode_observes_var_of_suffix (.lam (.var 0)) 0 rfl actual_frame_cuts_binding_suffix
  exact identityVariableReady.variable_step
    (encode_closed_transparency (.lam (.var 0)) (Nat.zero_lt_succ 0) 0) 0 observes [] []

theorem actual_lambda_step_from_ready_proof :
    ∃ (node : (encode 0 (.lam (.var 0))).N)
      (sort : (identityNet.label node).sort=.op .lam),
      identityParent.val.getLast?=some (identityNet.wire (.inl ⟨node,sort.symm ▸(Sum.inl () : Port (.op .lam))⟩)) ∧
      let body : Endpoint identityNet := .inl ⟨node,sort.symm ▸lamBody⟩
      let frame : BinderFrame identityNet := ⟨node,(identityNet.label node).index,identityParent.val,body,[]⟩
      machineStep identityNet ⟨[.read root [] [] []],[]⟩=
        .next ⟨[.read body [] identityParent.val [frame],.buildLam],[]⟩ := by
  have ready : ReadyAccess [] identityParent root [] [] [] := ⟨rfl,.initial⟩
  exact ready.lambda_step ⟨rfl,True.intro⟩ [] []

#print axioms ReadyAccess.variable_step
#print axioms ReadyAccess.application_step
#print axioms ReadyAccess.lambda_step
#print axioms actual_variable_step_from_binding_proof
#print axioms actual_lambda_step_from_ready_proof

/-- Consume the general scheduling/halting theorem on every closed standard
encoding, including arbitrary sharing, binding depths and initial level. -/
theorem all_closed_encoding_fuel_readback (term : Lambda.Term) (closed : Lambda.Closed term)
    (level : Nat) :
    ∃ fuel,readbackFuel (encode level term).net (.inl ()) fuel=.done term :=
  readbackFuel_terminates (encode_closed_matches term closed level)
    (encode_closed_independence term closed level).rootInputs
      (encode_closed_transparency term closed level)

theorem actual_shared_term_terminates_by_proof :
    ∃ fuel,readbackFuel duplicateNet (.inl ()) fuel=.done (.lam (.app (.var 0) (.var 0))) :=
  all_closed_encoding_fuel_readback (.lam (.app (.var 0) (.var 0)))
    ⟨Nat.zero_lt_succ 0,Nat.zero_lt_succ 0⟩ 0

theorem actual_nested_capture_term_terminates_by_proof :
    ∃ fuel,readbackFuel (encode 0 (.lam (.app (.lam (.var 1)) (.var 0)))).net (.inl ()) fuel=
      .done (.lam (.app (.lam (.var 1)) (.var 0))) :=
  all_closed_encoding_fuel_readback (.lam (.app (.lam (.var 1)) (.var 0)))
    ⟨by change 1<2; decide,Nat.zero_lt_succ 0⟩ 0

#print axioms ScanSteps.framed
#print axioms ReadyAccess.run_child
#print axioms ReadyAccess.parses
#print axioms readbackFuel_terminates
#print axioms all_closed_encoding_fuel_readback
#print axioms actual_shared_term_terminates_by_proof

theorem every_closed_initial_effective_readback (term : Lambda.Term) (closed : Lambda.Closed term) :
    readbackInitial term closed=term := readbackInitial_eq term closed

private theorem identityApplicationClosed : Lambda.Closed identityApp :=
  ⟨Nat.zero_lt_succ 0,Nat.zero_lt_succ 0⟩

private def canonicalExecutableSource : ExecutableNet (Boundary identityApp) :=
  (ExecutableNet.initial identityApp).transport (ActualNet.ofNet actualBetaSite.net) betaEncodingIso

private def canonicalBetaRecipe : ExplicitRewriteRecipe canonicalExecutableSource (.beta 0) where
  Kept := _
  OutsideWire := _
  InternalWire := _
  keptFinite := inferInstance
  outsideFinite := inferInstance
  internalFinite := inferInstance
  kept := _
  site := actualBetaSite
  sourceIso := .refl _

private def actualReadbackProgram : ExecutableProgram (ExecutableNet.initial identityApp) :=
  .rename (ActualNet.ofNet actualBetaSite.net) betaEncodingIso
    (.rewrite canonicalBetaRecipe (.stop _))

theorem actual_unbounded_program_returns_reduct :
    readbackProgram identityApp identityApplicationClosed actualReadbackProgram=identity :=
  readbackProgram_eq_of_fuel identityApp identityApplicationClosed actualReadbackProgram (fuel:=60) rfl

theorem actual_unbounded_program_is_sound :
    Lambda.Betas identityApp (readbackProgram identityApp identityApplicationClosed actualReadbackProgram) ∧
      Matches actualReadbackProgram.result.graph.net (.inl ())
        (readbackProgram identityApp identityApplicationClosed actualReadbackProgram) :=
  readbackProgram_sound identityApp identityApplicationClosed actualReadbackProgram

-- These execute the no-fuel entry, rather than evaluating a proved fuel bound.
#eval readbackInitial (.lam (.var 0)) (Nat.zero_lt_succ 0)==(.lam (.var 0))
#eval readbackInitial (.lam (.app (.var 0) (.var 0)))
  ⟨Nat.zero_lt_succ 0,Nat.zero_lt_succ 0⟩==(.lam (.app (.var 0) (.var 0)))
#eval readbackInitial (.lam (.app (.lam (.var 1)) (.var 0)))
  ⟨by change 1<2; decide,Nat.zero_lt_succ 0⟩==(.lam (.app (.lam (.var 1)) (.var 0)))
#eval readbackProgram identityApp identityApplicationClosed actualReadbackProgram==identity

#print axioms readback
#print axioms readbackProgram
#print axioms readbackInitial
#print axioms readbackProgram_sound
#print axioms every_closed_initial_effective_readback
#print axioms actual_unbounded_program_returns_reduct
#print axioms actual_unbounded_program_is_sound
end Lamping.Checks.Readback
