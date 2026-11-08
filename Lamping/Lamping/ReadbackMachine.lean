import Lamping.Lamping.ExecutableTraversal

namespace Lamping.AG.Readback
open Graph Lambda

private instance signatureKindEquality : DecidableEq signature.Kind :=
  inferInstanceAs (DecidableEq Kind)

def portNumber : (kind : Kind) → Port kind → Nat
  | .garbage,_ => 0
  | .op _,.inl () => 0
  | .op .app,.inr false | .op .lam,.inr false | .op .fan,.inr false => 1
  | .op .app,.inr true | .op .lam,.inr true | .op .fan,.inr true => 2
  | .op .cro,.inr () | .op .bra,.inr () => 1

section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable [DecidableEq N] [DecidableEq B] [DecidableEq W]

def endpointSame (g : Net signature N B W) (left right : Endpoint g) : Bool :=
  match left,right with
    | .inl ⟨n,p⟩,.inl ⟨m,q⟩ =>
      decide (n=m) && decide (portNumber _ p=portNumber _ q)
    | .inr (.inl b),.inr (.inl c) => decide (b=c)
    | .inr (.inr (v,d)),.inr (.inr (w,e)) => decide (v=w) && decide (d=e)
    | _,_ => false

private instance endpointBooleanEquality (g : Net signature N B W) : BEq (Endpoint g) :=
  ⟨endpointSame g⟩

/-- A lexical occurrence, rather than just a physical lambda node. The prefix
ends at its context access; bodyDeparture is the following literal departure. -/
structure BinderFrame (g : Net signature N B W) where
  node : N
  index : Nat
  stem : List (Endpoint g)
  bodyDeparture : Endpoint g
  seam : ContextData

def shellEqual (width : Nat) (left right : ContextData) : Bool :=
  (List.range width).all (fun k => decide (left.get k=right.get k))

/-- The list position is the lexical de Bruijn index. Ambiguity is not silently
resolved by picking the last visit to a shared physical lambda. -/
def binderCandidates (g : Net signature N B W) (frames : List (BinderFrame g))
    (node : N) (path : List (Endpoint g)) (output : ContextData) : List Nat :=
  frames.zipIdx.filterMap fun (frame,k) =>
    if frame.node=node && shellEqual frame.index frame.seam output &&
        (frame.stem++[frame.bodyDeparture]).isPrefixOf path then some k else none

inductive ReadbackTask (g : Net signature N B W) where
  | read (departure : Endpoint g) (context : ContextData)
      (stem : List (Endpoint g)) (frames : List (BinderFrame g))
  | buildApp | buildLam

structure MachineState (g : Net signature N B W) where
  pending : List (ReadbackTask g)
  values : List Term

inductive MachineFailure where
  | scan (reason : ScanFailure)
  | inconsistentTerminal | missingBinder | ambiguousBinder | malformedStack
  deriving DecidableEq,Repr

inductive MachineStep (g : Net signature N B W) where
  | next (state : MachineState g)
  | done (term : Term)
  | failed (reason : MachineFailure)

private def atNode (g : Net signature N B W) (node : N) (op : Op)
    (sort : (g.label node).sort=.op op) (port : Port (.op op)) : Endpoint g :=
  .inl ⟨node,sort.symm ▸ port⟩

/-- One finite machine transition. Its code depends on wire, labels, finite
contexts and explicit carrier equality; neither Matches nor a term witness is
an argument. Contexts of the two children are the same actual parent output. -/
def machineStep (g : Net signature N B W) (state : MachineState g) : MachineStep g :=
  match state.pending with
  | [] => match state.values with
      | [term] => .done term
      | _ => .failed .malformedStack
  | .buildApp::rest => match state.values with
      | argument::function::values => .next ⟨rest,.app function argument::values⟩
      | _ => .failed .malformedStack
  | .buildLam::rest => match state.values with
      | body::values => .next ⟨rest,.lam body::values⟩
      | _ => .failed .malformedStack
  | .read departure context stem frames::rest =>
    match scanOne g departure context with
    | .failed reason => .failed (.scan reason)
    | .next next after =>
      .next ⟨.read next after (stem++[departure]) frames::rest,state.values⟩
    | .terminal arrival kind after =>
      let path := stem++[departure]
      match kind with
      | .app =>
        if sort : (g.label arrival.1).sort=.op .app then
          let function := atNode g arrival.1 .app sort (.inl ())
          let argument := atNode g arrival.1 .app sort appArg
          .next ⟨.read function after path frames::
            .read argument after path frames::.buildApp::rest,state.values⟩
        else .failed .inconsistentTerminal
      | .lam =>
        if sort : (g.label arrival.1).sort=.op .lam then
          let body := atNode g arrival.1 .lam sort lamBody
          let frame : BinderFrame g := ⟨arrival.1,(g.label arrival.1).index,path,body,after⟩
          .next ⟨.read body after path (frame::frames)::.buildLam::rest,state.values⟩
        else .failed .inconsistentTerminal
      | .var => match binderCandidates g frames arrival.1 path after with
          | [index] => .next ⟨rest,.var index::state.values⟩
          | [] => .failed .missingBinder
          | _ => .failed .ambiguousBinder

def initialState (g : Net signature N B W) (root : B) : MachineState g :=
  ⟨[.read (.inr (.inl root)) [] [] []],[]⟩

inductive MachineRun (g : Net signature N B W) where
  | exhausted (state : MachineState g)
  | done (term : Term)
  | failed (reason : MachineFailure)

/-- Exhaustion reports a resumable state. It is distinct from successful
readback and from an invalid traversal; no graph-size fuel bound is asserted. -/
def machineFuel (g : Net signature N B W) : Nat → MachineState g → MachineRun g
  | 0,state => .exhausted state
  | fuel+1,state => match machineStep g state with
      | .next next => machineFuel g fuel next
      | .done term => .done term
      | .failed reason => .failed reason

def readbackFuel (g : Net signature N B W) (root : B) (fuel : Nat) : MachineRun g :=
  machineFuel g fuel (initialState g root)

end
end Lamping.AG.Readback

