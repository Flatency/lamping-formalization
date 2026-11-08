import Lamping.Lamping.ReadbackReady
import Lamping.Lamping.ReadbackMachineExecution

namespace Lamping.AG.Readback
open Graph Lambda
section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable [DecidableEq N] [DecidableEq B] [DecidableEq W]
variable {g : Net signature N B W} {root : B}

omit [DecidableEq N] [DecidableEq B] [DecidableEq W] in
/-- Frames follow the same executable scan trace as the machine state. No
alternative finite-context witness is chosen for the semantic invariant. -/
theorem ScanSteps.framed {n e a f b} (steps : ScanSteps g n e a f b)
    (input : ContextData) (stem : List (Endpoint g)) (frames : List (BinderFrame g))
    (start : FramedPath g root input (stem++[e]) a frames) :
    FramedPath g root input ((stem++steps.departures)++[f]) b frames := by
  induction steps generalizing stem with
  | refl => simpa only [ScanSteps.departures,List.append_nil] using start
  | @cons n e a f b last output step tail ih =>
    have next : FramedPath g root input ((stem++[e])++[f]) b frames :=
      .scan start (by simp) step
    have result := ih (stem++[e]) next
    simpa only [ScanSteps.departures,List.append_assoc,List.singleton_append] using result

private def departureToken (kind : Kind) (port : Port kind) : Path :=
  match kind,port with
  | .op .app,.inl () => [.fn]
  | .op .app,.inr true => [.arg]
  | .op .lam,.inr true => [.body]
  | _,_ => []

private theorem syntax_child_token {kind ctx child step}
    (roles : SyntaxChildPorts kind ctx child step) : departureToken kind child=[step] := by
  cases roles <;> rfl

/-- A child read task reaches a Ready observation in finitely many actual
machine transitions. The physical child departure is the one already stored
by the parent action; only its existing matching suffix is followed. -/
theorem ReadyAccess.run_child {term : Term} (matching : Matches g root term)
    (inputs : RootInputs g root)
    {input context : ContextData} {parent : RootAccess g root}
    {parentDeparture : Endpoint g} {parentStem : List (Endpoint g)} {parentFrames : List (BinderFrame g)}
    (ready : ReadyAccess input parent parentDeparture parentStem context parentFrames)
    (node : N) (ctx childPort : Port (g.label node).sort) (step : Step)
    (roles : SyntaxChildPorts (g.label node).sort ctx childPort step)
    (parentEnd : parent.val.getLast?=some (g.wire (.inl ⟨node,ctx⟩)))
    (frames : List (BinderFrame g))
    (start : FramedPath g root input (parent.val++[.inl ⟨node,childPort⟩]) context frames)
    (rest : List (ReadbackTask g)) (values : List Term) :
    ∃ (child : RootAccess g root) (last : Endpoint g) (stem : List (Endpoint g))
      (data : ContextData) (count : Nat),
      accessWord g child.val=accessWord g parent.val++[step] ∧
      ReadyAccess input child last stem data frames ∧
      MachineSteps g count ⟨.read (.inl ⟨node,childPort⟩) context parent.val frames::rest,values⟩
        ⟨.read last data stem frames::rest,values⟩ := by
  obtain ⟨child,tail,split,word⟩ := matching.child_access parent node ctx childPort step roles parentEnd
  obtain ⟨otherNode,otherCtx,otherPort,otherTail,otherRoles,otherEnd,otherSplit,forward,splitLabels⟩ :=
    matching.syntax_child_fragment parent child step word
  have suffixEq : ((.inl ⟨node,childPort⟩)::tail : List (Endpoint g))=
      (.inl ⟨otherNode,otherPort⟩)::otherTail :=
    List.append_cancel_left (split.symm.trans otherSplit)
  obtain ⟨output,childLabels⟩ := inputs.access child (Context.ofList input)
  obtain ⟨middle,parentLabels,suffixLabels⟩ := splitLabels _ _ childLabels
  have middleEq : middle=Context.ofList context := parentLabels.output_unique ready.framed.labels
  rw [middleEq,←suffixEq] at suffixLabels
  rw [←suffixEq] at forward
  have token : arrivalWord g (.inl ⟨node,childPort⟩)=[step] := syntax_child_token roles
  have zero : accessWord g ((.inl ⟨node,childPort⟩)::tail)=[] := by
    have same := word
    rw [split,accessWord_append g parent.val _ ready.framed.labels.nonempty] at same
    simp only [List.flatMap_cons,token,List.singleton_append] at same
    exact (List.cons.inj (List.append_cancel_left same)).2
  obtain ⟨data,last,scan,_outputEq,literal⟩ := scanSteps_of_control_path g suffixLabels
    (forward.empty_word_control_only zero) (.inl ⟨node,childPort⟩) rfl context rfl
  let stem := parent.val++scan.departures
  have framed := scan.framed input parent.val frames start
  have physical : child.val=stem++[last] := by
    rw [split,←literal,List.append_assoc]
  change FramedPath g root input (stem++[last]) data frames at framed
  rw [←physical] at framed
  have result : ReadyAccess input child last stem data frames := ⟨physical,framed⟩
  exact ⟨child,last,stem,data,_,word,result,scan.machineSteps parent.val frames rest values⟩

private theorem cast_port_heq {kind target : Kind} (sort : kind=target) (port : Port target) :
    HEq (sort.symm ▸port) port := by subst target; rfl

private theorem cast_function {kind : Kind} (sort : kind=.op .app) :
    SyntaxChildPorts kind (sort.symm ▸appCtx)
      (sort.symm ▸(Sum.inl () : Port (.op .app))) .fn := by subst kind; exact .function
private theorem cast_argument {kind : Kind} (sort : kind=.op .app) :
    SyntaxChildPorts kind (sort.symm ▸appCtx) (sort.symm ▸appArg) .arg := by
  subst kind; exact .argument
private theorem cast_body {kind : Kind} (sort : kind=.op .lam) :
    SyntaxChildPorts kind (sort.symm ▸(Sum.inl () : Port (.op .lam))) (sort.symm ▸lamBody) .body := by
  subst kind; exact .body

omit [DecidableEq N] [DecidableEq B] [DecidableEq W] in
private theorem ready_last {input context : ContextData} {access : RootAccess g root}
    {departure : Endpoint g} {stem : List (Endpoint g)} {frames : List (BinderFrame g)}
    (ready : ReadyAccess input access departure stem context frames) :
    access.val.getLast?=some departure := by rw [ready.split]; simp

omit [DecidableEq N] [DecidableEq B] [DecidableEq W] in
private theorem ready_arrives {input context : ContextData} {access : RootAccess g root}
    {departure : Endpoint g} {stem : List (Endpoint g)} {frames : List (BinderFrame g)}
    (ready : ReadyAccess input access departure stem context frames)
    (node : N) (ctx : Port (g.label node).sort)
    (finish : access.val.getLast?=some (g.wire (.inl ⟨node,ctx⟩))) :
    g.wire departure=.inl ⟨node,ctx⟩ := by
  have same := Option.some.inj ((ready_last ready).symm.trans finish)
  rw [same,g.pairing]

/-- Semantic recursion is on the matched subtree, while every control scan
uses its fixed finite child suffix. The term is a proof-only witness: all
resulting transitions are transitions of the unchanged executable machine. -/
theorem ReadyAccess.parses {term : Term} (matching : Matches g root term)
    (inputs : RootInputs g root) (transparency : Transparency g root) (subterm : Term) :
    ∀ {input context : ContextData} {access : RootAccess g root}
      {departure : Endpoint g} {stem : List (Endpoint g)} {frames : List (BinderFrame g)},
      ReadyAccess input access departure stem context frames →
      subtermAt term (accessWord g access.val)=some subterm →
      ∀ (rest : List (ReadbackTask g)) (values : List Term),
      ∃ count,MachineSteps g count ⟨.read departure context stem frames::rest,values⟩
        ⟨rest,subterm::values⟩ := by
  induction subterm with
  | var index =>
    intro input context access departure stem frames ready lookup rest values
    have observed := Matches.observes_lookup matching access (.var index) lookup
    exact ⟨1,.cons (ready.variable_step transparency index observed rest values) (.refl _)⟩
  | lam bodyTerm ih =>
    intro input context access departure stem frames ready lookup rest values
    have observed := Matches.observes_lookup matching access (.lam bodyTerm) lookup
    obtain ⟨node,sort,parentEnd,first⟩ := ready.lambda_step observed rest values
    let body : Endpoint g := .inl ⟨node,sort.symm ▸lamBody⟩
    let frame : BinderFrame g := ⟨node,(g.label node).index,access.val,body,context⟩
    have start : FramedPath g root input (access.val++[body]) context (frame::frames) :=
      .body ready.framed (ready_last ready) node (sort.symm ▸(.inl ()))
        (sort.symm ▸lamBody) sort (cast_port_heq sort _) (cast_port_heq sort _)
          (ready_arrives ready node _ parentEnd)
    obtain ⟨child,last,childStem,data,scanCount,word,childReady,scan⟩ := ready.run_child matching inputs
      node (sort.symm ▸(.inl ())) (sort.symm ▸lamBody) .body (cast_body sort) parentEnd
        (frame::frames) start (.buildLam::rest) values
    have childLookup : subtermAt term (accessWord g child.val)=some bodyTerm := by
      rw [word,subtermAt_append,lookup]
      simp [subtermAt]
    obtain ⟨bodyCount,parsed⟩ := ih childReady childLookup (.buildLam::rest) values
    have build : MachineSteps g 1 ⟨.buildLam::rest,bodyTerm::values⟩
        ⟨rest,.lam bodyTerm::values⟩ := .cons rfl (.refl _)
    exact ⟨_,.cons first (scan.append (parsed.append build))⟩
  | app function argument ihFunction ihArgument =>
    intro input context access departure stem frames ready lookup rest values
    have observed := Matches.observes_lookup matching access (.app function argument) lookup
    obtain ⟨node,sort,parentEnd,first⟩ := ready.application_step observed rest values
    let functionDeparture : Endpoint g := .inl ⟨node,sort.symm ▸(.inl ())⟩
    let argumentDeparture : Endpoint g := .inl ⟨node,sort.symm ▸appArg⟩
    have startFunction : FramedPath g root input (access.val++[functionDeparture]) context frames :=
      .application ready.framed (ready_last ready) node (sort.symm ▸appCtx)
        (sort.symm ▸(.inl ())) sort (cast_port_heq sort _) (Or.inl (cast_port_heq sort _))
          (ready_arrives ready node _ parentEnd)
    have startArgument : FramedPath g root input (access.val++[argumentDeparture]) context frames :=
      .application ready.framed (ready_last ready) node (sort.symm ▸appCtx)
        (sort.symm ▸appArg) sort (cast_port_heq sort _) (Or.inr (cast_port_heq sort _))
          (ready_arrives ready node _ parentEnd)
    obtain ⟨functionAccess,functionLast,functionStem,functionData,functionScanCount,functionWord,
        functionReady,functionScan⟩ := ready.run_child matching inputs
      node (sort.symm ▸appCtx) (sort.symm ▸(.inl ())) .fn (cast_function sort) parentEnd frames startFunction
        (.read argumentDeparture context access.val frames::.buildApp::rest) values
    have functionLookup : subtermAt term (accessWord g functionAccess.val)=some function := by
      rw [functionWord,subtermAt_append,lookup]
      simp [subtermAt]
    obtain ⟨functionCount,functionParsed⟩ := ihFunction functionReady functionLookup
      (.read argumentDeparture context access.val frames::.buildApp::rest) values
    obtain ⟨argumentAccess,argumentLast,argumentStem,argumentData,argumentScanCount,argumentWord,
        argumentReady,argumentScan⟩ := ready.run_child matching inputs
      node (sort.symm ▸appCtx) (sort.symm ▸appArg) .arg (cast_argument sort) parentEnd frames startArgument
        (.buildApp::rest) (function::values)
    have argumentLookup : subtermAt term (accessWord g argumentAccess.val)=some argument := by
      rw [argumentWord,subtermAt_append,lookup]
      simp [subtermAt]
    obtain ⟨argumentCount,argumentParsed⟩ := ihArgument argumentReady argumentLookup
      (.buildApp::rest) (function::values)
    have build : MachineSteps g 1 ⟨.buildApp::rest,argument::function::values⟩
        ⟨rest,.app function argument::values⟩ := .cons rfl (.refl _)
    exact ⟨_,.cons first (functionScan.append
      (functionParsed.append (argumentScan.append (argumentParsed.append build))))⟩

/-- Caller-free halting and correctness of the actual fuel machine on the
semantic readback domain. Matches is used to prove a finite run, not to select
the algorithm's output. This theorem alone is not an unbounded entry point. -/
theorem readbackFuel_terminates {term : Term} (matching : Matches g root term)
    (inputs : RootInputs g root) (transparency : Transparency g root) :
    ∃ fuel,readbackFuel g root fuel=.done term := by
  let position : Position term := ⟨[],by simp [subtermAt]⟩
  obtain ⟨access,word,sub,lookup,observes⟩ := Matches.observation g matching position
  have emptyWord : accessWord g access.val=[] := word
  obtain ⟨output,labels⟩ := inputs.access access (Context.ofList [])
  obtain ⟨data,last,scan,_outputEq,literal⟩ := scanSteps_of_control_path g labels
    (access.property.1.2.empty_word_control_only emptyWord)
      (.inr (.inl root)) access.property.2.1 [] rfl
  have start : FramedPath g root [] ([]++[.inr (.inl root)]) [] [] := .initial
  have framed := scan.framed [] [] [] start
  have physical : access.val=scan.departures++[last] := literal.symm
  have ready : ReadyAccess [] access last scan.departures data [] := ⟨physical,by
    simpa only [List.nil_append,literal] using framed⟩
  have rootLookup : subtermAt term (accessWord g access.val)=some term := by
    rw [emptyWord]
    simp [subtermAt]
  obtain ⟨parseCount,parsed⟩ := ReadyAccess.parses matching inputs transparency term ready rootLookup [] []
  have reached := (scan.machineSteps [] [] [] []).append parsed
  have doneRun := reached.fuel_more 1
  refine ⟨access.val.length-1+parseCount+1,?_⟩
  simpa only [List.nil_append,initialState,readbackFuel,machineFuel,machineStep] using doneRun

end
end Lamping.AG.Readback
