import Lamping.Lamping.InitialLoopProjection
namespace Lamping.AG
open Graph Lambda
abbrev duplicatedVariable : Term := .lam (.app (.var 0) (.var 0))
abbrev duplicateBody : Term := .app (.var 0) (.var 0)
abbrev DupBodyWire := (Empty ⊕ (Empty ⊕ Empty)) ⊕ (Boundary (.var 0) ⊕ Boundary (.var 0))
abbrev DupWire := (Empty ⊕ DupBodyWire) ⊕ Boundary duplicateBody
abbrev DupNode := Unit ⊕ (AppNodes (.var 0) (.var 0) ⊕ (Unit ⊕ Unit))
abbrev DupNet (n : Nat) := (encode n duplicatedVariable).net

def dupBodySeam : DupWire := .inr (.inl ())
def dupFunctionSeam : DupWire := .inl (.inr (.inr (.inl (.inl ()))))
def dupVariableSeam : DupWire := .inl (.inr (.inr (.inl (.inr ⟨0,rfl⟩))))
def dupBindingSeam : DupWire := .inr (.inr ⟨0,Or.inl rfl⟩)
def dupFan : DupNode := .inr (.inl (.inr (.inr ⟨⟨0,rfl⟩,rfl⟩)))
/-- Actual left variable occurrence: lambda body→App.fun→Cro(n)→Fan(n).o→binding.
There is no Bra on this control chain (offset zero). -/
def dupLeftEdges (n : Nat) : List (Endpoint (DupNet n)) :=
  [.inl ⟨.inl (),lamBody⟩,
   .inr (.inr (dupBodySeam,true)),
   .inl ⟨.inr (.inl (.inl ())),.inl ()⟩,
   .inr (.inr (dupFunctionSeam,true)),
   .inl ⟨.inr (.inr (.inl ())),.inl ()⟩,
   .inr (.inr (dupVariableSeam,false)),
   .inl ⟨dupFan,.inl ()⟩,
   .inr (.inr (dupBindingSeam,false))]

def dupLeftBindingLoop (n : Nat) (shell tail : Context) :
    BindingLoop (DupNet n) (dupLeftEdges n)
      (shell.replace n tail) (shell.replace n (tail.cons (.o .empty))) where
  binder := .inl ()
  isLam := rfl
  body := lamBody
  bind := lamBind
  body_role := HEq.rfl
  bind_role := HEq.rfl
  start := rfl
  finish := rfl
  proper := .cons (LabelledTurn.transparent (g:=DupNet n) dupBodySeam false _)
    (.cons (LabelledTurn.node (g:=DupNet n) (.inr (.inl (.inl ()))) appCtx (.inl ()) (.direct (.appFun _)))
      (.cons (LabelledTurn.transparent (g:=DupNet n) dupFunctionSeam false _)
        (.cons (LabelledTurn.node (g:=DupNet n) (.inr (.inr (.inl ()))) (.inr ()) (.inl ()) (.direct (.cro shell tail)))
          (.cons (LabelledTurn.transparent (g:=DupNet n) dupVariableSeam true _)
            (.cons (LabelledTurn.node (g:=DupNet n) dupFan fanO (.inl ()) (.direct (.fanO shell tail .empty)))
              (.cons (LabelledTurn.transparent (g:=DupNet n) dupBindingSeam true _) (.single _ _)))))))
  forward := .transparent dupBodySeam false rfl rfl
    (.node (.inr (.inl (.inl ()))) appCtx (.inl ()) rfl rfl ⟨rfl,Or.inl rfl⟩
      (.transparent dupFunctionSeam false rfl rfl
        (.node (.inr (.inr (.inl ()))) (.inr ()) (.inl ()) rfl rfl True.intro
          (.transparent dupVariableSeam true rfl rfl
            (.node dupFan fanO (.inl ()) rfl rfl True.intro
              (.transparent dupBindingSeam true rfl rfl (.single _)))))))
  shell := by intro k hk; change k<n at hk; simp [Context.replace,hk]
end Lamping.AG


namespace Lamping.AG
open Graph Lambda
/-- Count brackets at actual crossed node occurrences, ignoring transparent vertices. -/
def crossedKinds {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
    (g : Net signature N B W) (es : List (Endpoint g)) : List Kind :=
  es.dropLast.filterMap (fun e => match g.wire e with
    | .inl ⟨v,_⟩ => some (g.label v).sort
    | _ => none)
def bracketOffset {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
    (g : Net signature N B W) (es : List (Endpoint g)) : Nat :=
  ((crossedKinds g es).filter (fun k => k==.op .bra)).length
def dupLeftControlEdges (n : Nat) : List (Endpoint (DupNet n)) := (dupLeftEdges n).drop 3
/-- This is the actual Cro→binder suffix, not a separate surrogate graph. -/
theorem dupLeftControlKinds (n : Nat) :
    crossedKinds (DupNet n) (dupLeftControlEdges n) = [.op .cro,.op .fan] := rfl
theorem dupLeftControlOffset (n : Nat) : bracketOffset (DupNet n) (dupLeftControlEdges n)=0 := rfl
/-- Source formula p=0 would require the inserted level to be empty. The real fan
writes an o marker at that very level, even on the smallest closed sharing term. -/
theorem dupLeft_not_printed_zero_offset (n : Nat) (shell tail : Context) :
    shell.replace n (tail.cons (.o .empty)) ≠ shell.replace n (tail.cons .empty) := by
  intro eq
  have level := congrArg (fun c : Context => c.get n) eq
  simp [Context.replace] at level
/-- A concrete closed source counterexample at n=0, with all original levels empty. -/
theorem printed_zero_offset_counterexample :
    Nonempty (BindingLoop (DupNet 0) (dupLeftEdges 0) Context.empty
      (Context.empty.cons (.o .empty))) ∧
    bracketOffset (DupNet 0) (dupLeftControlEdges 0)=0 ∧
    Context.empty.cons (.o .empty) ≠ Context.empty.cons .empty := by
  refine ⟨?_,rfl,?_⟩
  · exact ⟨by simpa using dupLeftBindingLoop 0 Context.empty Context.empty⟩
  · intro eq; have level := congrArg (fun c : Context => c.get 0) eq; cases level
end Lamping.AG
namespace Lamping.AG
open Graph Lambda
def dupArgumentSeam : DupWire := .inl (.inr (.inr (.inr (.inl ()))))
def dupArgumentVariableSeam : DupWire := .inl (.inr (.inr (.inr (.inr ⟨0,rfl⟩))))
def dupBracket : DupNode := .inr (.inl (.inr (.inl ⟨0,rfl⟩)))
def dupRightEdges : List (Endpoint (DupNet 0)) :=
  [.inl ⟨.inl (),lamBody⟩,
   .inr (.inr (dupBodySeam,true)),
   .inl ⟨.inr (.inl (.inl ())),appArg⟩,
   .inr (.inr (dupArgumentSeam,true)),
   .inl ⟨.inr (.inr (.inr ())),.inl ()⟩,
   .inr (.inr (dupArgumentVariableSeam,false)),
   .inl ⟨dupBracket,.inl ()⟩,
   .inl ⟨dupFan,.inl ()⟩,
   .inr (.inr (dupBindingSeam,false))]
theorem empty_replace_empty (n : Nat) : Context.empty.replace n Context.empty=Context.empty := by
  ext k; simp [Context.replace]
def dupRightBindingLoop : BindingLoop (DupNet 0) dupRightEdges Context.empty
    (Context.empty.cons (.star (.pair .empty .empty))) where
  binder := .inl ()
  isLam := rfl
  body := lamBody
  bind := lamBind
  body_role := HEq.rfl
  bind_role := HEq.rfl
  start := rfl
  finish := rfl
  proper := by
    have cro : Traversal 1 (.op .cro) (.inr ()) (.inl ()) Context.empty Context.empty := by
      exact .direct (by simpa only [Context.cons_empty,empty_replace_empty] using Passage.cro (i:=1) Context.empty Context.empty)
    have bra : Traversal 0 (.op .bra) (.inr ()) (.inl ()) Context.empty (Context.empty.cons (.pair .empty .empty)) := by
      exact .direct (by simpa only [Context.cons_empty,Context.replace_zero] using Passage.bra (i:=0) Context.empty Context.empty .empty .empty)
    have fan : Traversal 0 (.op .fan) fanStar (.inl ()) (Context.empty.cons (.pair .empty .empty))
        (Context.empty.cons (.star (.pair .empty .empty))) := by
      exact .direct (by simpa only [Context.replace_zero] using Passage.fanStar (i:=0) Context.empty Context.empty (.pair .empty .empty))
    exact .cons (LabelledTurn.transparent (g:=DupNet 0) dupBodySeam false _)
      (.cons (LabelledTurn.node (g:=DupNet 0) (.inr (.inl (.inl ()))) appCtx appArg (.direct (.appArg _)))
        (.cons (LabelledTurn.transparent (g:=DupNet 0) dupArgumentSeam false _)
          (.cons (LabelledTurn.node (g:=DupNet 0) (.inr (.inr (.inr ()))) (.inr ()) (.inl ()) cro)
            (.cons (LabelledTurn.transparent (g:=DupNet 0) dupArgumentVariableSeam true _)
              (.cons (LabelledTurn.node (g:=DupNet 0) dupBracket (.inr ()) (.inl ()) bra)
                (.cons (LabelledTurn.node (g:=DupNet 0) dupFan fanStar (.inl ()) fan)
                  (.cons (LabelledTurn.transparent (g:=DupNet 0) dupBindingSeam true _) (.single _ _))))))))
  forward := .transparent dupBodySeam false rfl rfl
    (.node (.inr (.inl (.inl ()))) appCtx appArg rfl rfl ⟨rfl,Or.inr rfl⟩
      (.transparent dupArgumentSeam false rfl rfl
        (.node (.inr (.inr (.inr ()))) (.inr ()) (.inl ()) rfl rfl True.intro
          (.transparent dupArgumentVariableSeam true rfl rfl
            (.node dupBracket (.inr ()) (.inl ()) rfl rfl True.intro
              (.node dupFan fanStar (.inl ()) rfl rfl True.intro
                (.transparent dupBindingSeam true rfl rfl (.single _))))))))
  shell := by intro k hk; change k<0 at hk; omega

def dupRightControlEdges : List (Endpoint (DupNet 0)) := dupRightEdges.drop 3
theorem dupRightControlKinds : crossedKinds (DupNet 0) dupRightControlEdges=[.op .cro,.op .bra,.op .fan] := rfl
theorem dupRightControlOffset : bracketOffset (DupNet 0) dupRightControlEdges=1 := rfl
/-- In the printed p>0 formula, the newly inserted level has outer constructor Pair,
regardless of the marker strings on its two components. Here it is Star(Pair...). -/
theorem dupRight_not_printed_positive_offset (x y : Level) :
    Context.empty.cons (.star (.pair .empty .empty)) ≠ Context.empty.cons (.pair x y) := by
  intro eq; have level := congrArg (fun c : Context => c.get 0) eq; cases level
end Lamping.AG
namespace Lamping.AG
open Lambda
theorem duplicatedVariable_closed : Closed duplicatedVariable := by
  change 0<1 ∧ 0<1
  omega
end Lamping.AG
namespace Lamping.AG.InitialOffsets
open Graph
/-- One fan marker acts on an arbitrary Level, including an entire Pair. -/
def mark (branch : Bool) (a : Level) : Level := if branch then .star a else .o a
def marks (word : List Bool) (a : Level) : Level := word.foldl (fun a b => mark b a) a
/-- Corrected recursive shape, not a premise asserting the desired context equation. -/
inductive Shape where
  | base (word : List Bool)
  | lower (higher : Shape) (word : List Bool)
  deriving Repr
def Shape.offset : Shape → Nat | .base _ => 0 | .lower h _ => h.offset+1
def Shape.level : Shape → Context → Nat → Level
  | .base w,_,_ => marks w .empty
  | .lower h w,a,n => marks w (.pair (h.level a (n+1)) (a.get n))
/-- Total printed forward control operations. Each is justified by Passage below. -/
def croAt (n : Nat) (a : Context) : Context := a.replace n ((a.tail n).cons .empty)
def fanAt (n : Nat) (b : Bool) (a : Context) : Context :=
  a.replace n ((a.tail (n+1)).cons (mark b (a.get n)))
def braAt (n : Nat) (a : Context) : Context :=
  a.replace n ((a.tail (n+2)).cons (.pair (a.get (n+1)) (a.get n)))
def fanBlock (n : Nat) (word : List Bool) (a : Context) : Context :=
  word.foldl (fun a b => fanAt n b a) a
/-- The stepwise program crosses one Cro, then descends one level per Bra. -/
def Shape.execute : Shape → Nat → Context → Context
  | .base w,n,a => fanBlock n w (croAt n a)
  | .lower h w,n,a => fanBlock n w (braAt n (h.execute (n+1) a))

theorem tail_replace (a b : Context) (n k : Nat) : (a.replace n b).tail (n+k)=b.tail k := by
  ext t
  change (a.replace n b).get (n+k+t)=b.get (k+t)
  rw [Context.replace_high _ _ (by omega)]
  congr 1; omega
@[simp] theorem tail_cons_one (a : Context) (x : Level) : (a.cons x).tail 1=a := by
  ext t; simp [Context.tail,Nat.add_comm]
@[simp] theorem tail_zero (a : Context) : a.tail 0=a := by ext t; simp [Context.tail]
@[simp] theorem tail_cons_two (a : Context) (x y : Level) : ((a.cons x).cons y).tail 2=a := by
  ext t; simp [Context.tail,Nat.add_comm]

theorem rebuild (a : Context) (n : Nat) : a.replace n ((a.tail (n+1)).cons (a.get n))=a := by
  ext t
  by_cases low : t<n
  · simp [Context.replace,low]
  · by_cases equal : t=n
    · subst t; simp [Context.replace]
    · have diff : t-n=(t-n-1)+1 := by omega
      rw [Context.replace_high _ _ (by omega),diff,Context.cons_succ]
      change a.get (n+1+(t-n-1))=a.get t
      congr 1; omega

theorem replace_successor (a b : Context) (n : Nat) :
    a.replace (n+1) b = a.replace n (b.cons (a.get n)) := by
  ext t
  by_cases low : t<n
  · simp [Context.replace,low,show t<n+1 by omega]
  · by_cases equal : t=n
    · subst t; simp [Context.replace]
    · have diff : t-n=(t-(n+1))+1 := by omega
      rw [Context.replace_high _ _ (by omega),Context.replace_high _ _ (by omega),diff,Context.cons_succ]

theorem fanAt_replace (s a : Context) (n : Nat) (b : Bool) (x : Level) :
    fanAt n b (s.replace n (a.cons x)) = s.replace n (a.cons (mark b x)) := by
  unfold fanAt
  rw [show n+1=n+1 from rfl,tail_replace]
  simp only [tail_cons_one,Context.replace_high s (a.cons x) (Nat.le_refl n),Nat.sub_self,Context.cons_zero,Context.replace_replace]

theorem braAt_replace (s a : Context) (n : Nat) (x y : Level) :
    braAt n (s.replace n ((a.cons x).cons y))=s.replace n (a.cons (.pair x y)) := by
  unfold braAt
  rw [tail_replace]
  simp only [tail_cons_two,Context.replace_high s ((a.cons x).cons y) (Nat.le_refl n),Nat.sub_self,Context.cons_zero]
  rw [Context.replace_high s ((a.cons x).cons y) (by omega)]
  simp only [Nat.add_sub_cancel_left,Context.cons_succ,Context.cons_zero,Context.replace_replace]

theorem fanBlock_replace (s a : Context) (n : Nat) (w : List Bool) (x : Level) :
    fanBlock n w (s.replace n (a.cons x))=s.replace n (a.cons (marks w x)) := by
  induction w generalizing x with
  | nil => rfl
  | cons b bs ih =>
    change fanBlock n bs (fanAt n b (s.replace n (a.cons x)))=_
    rw [fanAt_replace,ih]
    rfl
/-- Algebraic corrected offset formula for every stepwise descending program.
Actual initial-path classification is a separate proof obligation, not an input field. -/
theorem corrected_program_formula (shape : Shape) (n : Nat) (a : Context) :
    shape.execute n a = a.replace n ((a.tail (n+shape.offset)).cons (shape.level a n)) := by
  induction shape generalizing n with
  | base w =>
    change fanBlock n w (a.replace n ((a.tail n).cons .empty))=_
    rw [fanBlock_replace]
    rfl
  | lower h w ih =>
    change fanBlock n w (braAt n (h.execute (n+1) a))=_
    rw [ih,replace_successor,braAt_replace,fanBlock_replace]
    congr 2
    · congr 1; simp only [Shape.offset]; omega
end Lamping.AG.InitialOffsets

namespace Lamping.AG.InitialOffsets
open Graph
inductive Event where
  | cro (index : Nat)
  | fan (index : Nat) (branch : Bool)
  | bra (index : Nat)
  deriving DecidableEq, Repr
def Event.apply : Event → Context → Context
  | .cro n,a => croAt n a
  | .fan n b,a => fanAt n b a
  | .bra n,a => braAt n a
def Event.Rel : Event → Context → Context → Prop
  | .cro n,a,b => Passage n (.op .cro) (.inr ()) (.inl ()) a b
  | .fan n branch,a,b => Passage n (.op .fan) (.inr branch) (.inl ()) a b
  | .bra n,a,b => Passage n (.op .bra) (.inr ()) (.inl ()) a b

theorem rebuild_two (a : Context) (n : Nat) :
    a.replace n (((a.tail (n+2)).cons (a.get (n+1))).cons (a.get n))=a := by
  rw [←replace_successor,←replace_successor]
  exact a.replace_tail (n+2)
theorem Event.apply_rel (event : Event) (a : Context) : event.Rel a (event.apply a) := by
  cases event with
  | cro n =>
    exact by simpa only [Event.Rel,Event.apply,croAt,Context.replace_tail] using Passage.cro (i:=n) a (a.tail n)
  | fan n b =>
    cases b
    · exact by simpa only [Event.Rel,Event.apply,fanAt,mark,Bool.false_eq_true,if_false,rebuild] using Passage.fanO (i:=n) a (a.tail (n+1)) (a.get n)
    · exact by simpa only [Event.Rel,Event.apply,fanAt,mark,if_true,rebuild] using Passage.fanStar (i:=n) a (a.tail (n+1)) (a.get n)
  | bra n =>
    exact by simpa only [Event.Rel,Event.apply,braAt,rebuild_two] using Passage.bra (i:=n) a (a.tail (n+2)) (a.get (n+1)) (a.get n)

inductive Run : List Event → Context → Context → Prop
  | nil (a) : Run [] a a
  | cons (event : Event) {es a b c} : event.Rel a b → Run es b c → Run (event::es) a c

def executeEvents (events : List Event) (a : Context) : Context := events.foldl (fun a e => e.apply a) a
theorem executeEvents_run (events : List Event) (a : Context) : Run events a (executeEvents events a) := by
  induction events generalizing a with
  | nil => exact .nil a
  | cons event events ih => exact .cons event (event.apply_rel a) (ih (event.apply a))

def Shape.events : Shape → Nat → List Event
  | .base w,n => .cro n :: w.map (Event.fan n)
  | .lower h w,n => h.events (n+1) ++ [.bra n] ++ w.map (Event.fan n)
theorem fanBlock_events (w : List Bool) (n : Nat) (a : Context) :
    executeEvents (w.map (Event.fan n)) a=fanBlock n w a := by
  induction w generalizing a with
  | nil => rfl
  | cons b bs ih => exact ih (fanAt n b a)
theorem Shape.events_execute (shape : Shape) (n : Nat) (a : Context) :
    executeEvents (shape.events n) a=shape.execute n a := by
  induction shape generalizing n with
  | base w => exact fanBlock_events w n (croAt n a)
  | lower h w ih =>
    simp only [Shape.events,executeEvents,List.foldl_append]
    change executeEvents (w.map (Event.fan n)) (braAt n (executeEvents (h.events (n+1)) a))=_
    rw [ih,fanBlock_events]
    rfl
/-- The corrected formula is connected to a composition of original Passage rules. -/
theorem corrected_program_run (shape : Shape) (n : Nat) (a : Context) :
    Run (shape.events n) a (a.replace n ((a.tail (n+shape.offset)).cons (shape.level a n))) := by
  have h := executeEvents_run (shape.events n) a
  simpa only [shape.events_execute,corrected_program_formula] using h
end Lamping.AG.InitialOffsets
namespace Lamping.AG.InitialOffsets

theorem croAt_replace (s a : Context) (n : Nat) :
    croAt n (s.replace n a)=s.replace n (a.cons .empty) := by
  have ht : (s.replace n a).tail n=a := by simpa only [Nat.add_zero,tail_zero] using tail_replace s a n 0
  unfold croAt
  rw [ht,Context.replace_replace]

def ControlCompute (i : Nat) : (k : Kind) → Port k → Port k → Context → Context → Prop
  | .op .fan,.inr branch,.inl _,a,b => b=fanAt i branch a
  | .op .cro,.inr _,.inl _,a,b => b=croAt i a
  | .op .bra,.inr _,.inl _,a,b => b=braAt i a
  | _,_,_,a,b => a=b

theorem Passage.computed {i k p q a b} (h : Passage i k p q a b) : ControlCompute i k p q a b := by
  cases h with
  | fanO s t x => exact (fanAt_replace s t i false x).symm
  | fanStar s t x => exact (fanAt_replace s t i true x).symm
  | cro s t => exact (croAt_replace s t i).symm
  | bra s t x y => exact (braAt_replace s t i x y).symm
  | appFun | appArg | lamBody => rfl

theorem Event.Rel_unique (event : Event) {a b : Context} (h : event.Rel a b) : b=event.apply a := by
  cases event <;> exact Passage.computed h

theorem Run.functional {events : List Event} {a b : Context} (h : Run events a b) : b=executeEvents events a := by
  induction h with
  | nil => rfl
  | @cons e es a b c step rest ih =>
    change c=executeEvents es (e.apply a)
    rw [←e.Rel_unique step]
    exact ih
/-- Every labeling satisfying the actual primitive Passage constraints along a
corrected control program has the computed final context; no equality certificate. -/
theorem corrected_program_all_runs (shape : Shape) (n : Nat) (a b : Context)
    (run : Run (shape.events n) a b) :
    b=a.replace n ((a.tail (n+shape.offset)).cons (shape.level a n)) := by
  rw [run.functional,shape.events_execute,corrected_program_formula]

theorem corrected_program_shell (shape : Shape) (n : Nat) (a b : Context)
    (run : Run (shape.events n) a b) : Context.SameShell n a b := by
  rw [corrected_program_all_runs shape n a b run]
  exact Context.sameShell_replace a _ n
end Lamping.AG.InitialOffsets

namespace Lamping.AG.InitialOffsets
open Graph
/-- Read a direct control event from the arrival port of one segment. Proper nodes
and transparent vertices emit no event; no supplied trace certificate is needed. -/
def eventOfPort (i : Nat) : (k : Kind) → Port k → Option Event
  | .op .fan,.inr b => some (.fan i b)
  | .op .cro,.inr _ => some (.cro i)
  | .op .bra,.inr _ => some (.bra i)
  | _,_ => none

def eventsOfEdges {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
    (g : Net signature N B W) : List (Endpoint g) → List Event
  | [] => []
  | [_] => []
  | e::f::es =>
      (match g.wire e with | .inl ⟨n,p⟩ => (eventOfPort (g.label n).index (g.label n).sort p).toList | _ => []) ++ eventsOfEdges g (f::es)

theorem Run.append {xs ys : List Event} {a b c : Context} (h : Run xs a b) (k : Run ys b c) : Run (xs++ys) a c := by
  induction h with
  | nil => exact k
  | cons e step rest ih => exact .cons e step (ih k)

theorem Passage.event_run {i k p q a b} (h : Passage i k p q a b) :
    Run (eventOfPort i k p).toList a b := by
  cases h with
  | fanO s t x => exact .cons (.fan i false) (by exact Passage.fanO s t x) (.nil _)
  | fanStar s t x => exact .cons (.fan i true) (by exact Passage.fanStar s t x) (.nil _)
  | cro s t => exact .cons (.cro i) (by exact Passage.cro s t) (.nil _)
  | bra s t x y => exact .cons (.bra i) (by exact Passage.bra s t x y) (.nil _)
  | appFun | appArg | lamBody => exact .nil _
section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable {g : Net signature N B W}
theorem InitialTurn.event_run {x y : Endpoint g} {a b : Context} (h : InitialTurn (g:=g) x y a b)
    (e : Endpoint g) (arrives : g.wire e=x) :
    Run (match g.wire e with | .inl ⟨n,p⟩ => (eventOfPort (g.label n).index (g.label n).sort p).toList | _ => []) a b := by
  rw [arrives]
  cases h with
  | node n p q rule => exact Passage.event_run rule
  | transparent w d a => exact .nil _
theorem InitialLabelling.events_run {es : List (Endpoint g)} {a b : Context}
    (h : AG.InitialLabelling (g:=g) es a b) : Run (eventsOfEdges g es) a b := by
  induction h with
  | single e a => exact .nil a
  | @cons e f es a b c turn tail ih =>
    exact (InitialTurn.event_run turn e rfl).append ih
end
/-- Every actual initial root path yields a run of the original control rules,
with its event sequence computed directly from the graph edges. -/
theorem encode_root_events (t : Lambda.Term) (n : Nat) (es : List (Endpoint (encode n t).net))
    (rooted : es.head?=some (.inr (.inl (.inl ())))) (h : Labelling (encode n t).net es a b) :
    Run (eventsOfEdges (encode n t).net es) a b :=
  InitialLabelling.events_run (encode_root_initial t n es rooted h)
end Lamping.AG.InitialOffsets

namespace Lamping.AG.InitialOffsets
open Graph Lambda
/-- A raw source loop carries incidence and proper labels, but no binding-shell
condition: proving that condition is the initial correctness obligation. -/
structure RawLoop {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
    (g : Net signature N B W) (es : List (Endpoint g)) (a b : Context) where
  binder : N
  isLam : (g.label binder).sort=.op .lam
  body : Port (g.label binder).sort
  bind : Port (g.label binder).sort
  body_role : HEq body lamBody
  bind_role : HEq bind lamBind
  start : es.head?=some (.inl ⟨binder,body⟩)
  finish : es.getLast?=some (g.wire (.inl ⟨binder,bind⟩))
  proper : Labelling g es a b

theorem lambda_body_polarity {k : Kind} {p : Port k} (isLam : k=.op .lam) (role : HEq p lamBody) :
    initialPortPolarity k p=true := by
  subst k
  have eq : p=lamBody := eq_of_heq role
  subst p; rfl

theorem encode_rawLoop_initial (t : Term) (n : Nat) (es : List (Endpoint (encode n t).net))
    (loop : RawLoop (encode n t).net es a b) : AG.InitialLabelling (g:=(encode n t).net) es a b := by
  obtain ⟨vp,flow⟩ := encode_flow t n
  apply loop.proper.initial_of_flow flow
  intro e he
  rw [loop.start] at he
  simp only [Option.some.injEq] at he
  subst e
  exact lambda_body_polarity loop.isLam loop.body_role
/-- A universal corrected stepwise formula, read from an actual initial loop.
The descending-level normal form and shell preservation remain separate obligations. -/
theorem encode_rawLoop_composition (t : Term) (n : Nat) (es : List (Endpoint (encode n t).net))
    (loop : RawLoop (encode n t).net es a b) : b=executeEvents (eventsOfEdges (encode n t).net es) a :=
  (InitialLabelling.events_run (encode_rawLoop_initial t n es loop)).functional
end Lamping.AG.InitialOffsets
namespace Lamping.AG.InitialOffsets
open Graph Lambda
theorem Traversal.operator {i k p q a b} (h : Traversal i k p q a b) : ∃ f, k=.op f := by
  cases h with
  | direct h => cases h <;> exact ⟨_,rfl⟩
  | inverse h => cases h <;> exact ⟨_,rfl⟩
section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable {g : Net signature N B W}
theorem LabelledTurn.low_bound {e f : Endpoint g} {a b : Context} (h : LabelledTurn g e f a b)
    (n : Nat) (bound : ∀ v op, (g.label v).sort=.op op → n≤(g.label v).index) : Context.SameShell n a b := by
  cases h with
  | node v p q rule =>
    obtain ⟨op,kind⟩ := Traversal.operator rule
    intro t ht
    exact rule.low t (Nat.lt_of_lt_of_le ht (bound v op kind))
  | transparent => intro t _; rfl

theorem Labelling.low_bound {es : List (Endpoint g)} {a b : Context} (h : Labelling g es a b)
    (n : Nat) (bound : ∀ v op, (g.label v).sort=.op op → n≤(g.label v).index) : Context.SameShell n a b := by
  induction h with
  | single => intro t _; rfl
  | cons turn tail ih => intro t ht; exact (LabelledTurn.low_bound turn n bound t ht).trans (ih t ht)
end
/-- Every path in the actual translation preserves its outer translation shell;
this is proved from real node labels, not assumed as a path certificate. -/
theorem encode_path_shell (t : Term) (n : Nat) (es : List (Endpoint (encode n t).net))
    (h : Labelling (encode n t).net es a b) : Context.SameShell n a b :=
  Labelling.low_bound h n (fun v _ kind => encode_level_lower t n v kind)

theorem outer_lambda_node (body : Term) (n : Nat) :
    ∃ v : (encode n (.lam body)).N, (encode n (.lam body)).net.label v=label .lam n := by
  dsimp only [encode]
  by_cases used : free body 0
  · rw [dif_pos used]; exact ⟨.inl (),rfl⟩
  · rw [dif_neg used]; exact ⟨.inl (.inl ()),rfl⟩
/-- Loops at the translation level preserve their binder shell. General nested
binders need the separate actual-subgraph localization theorem. -/
def translation_level_binding (t : Term) (n : Nat) (es : List (Endpoint (encode n t).net))
    (loop : RawLoop (encode n t).net es a b) (binder_level : ((encode n t).net.label loop.binder).index=n) :
    BindingLoop (encode n t).net es a b where
  binder := loop.binder
  isLam := loop.isLam
  body := loop.body
  bind := loop.bind
  body_role := loop.body_role
  bind_role := loop.bind_role
  start := loop.start
  finish := loop.finish
  proper := loop.proper
  forward := (encode_rawLoop_initial t n es loop).forward
  shell := by rw [binder_level]; exact encode_path_shell t n es loop.proper
end Lamping.AG.InitialOffsets
namespace Lamping.AG.InitialOffsets
/-- Append a marker at the current outermost control level. -/
def Shape.addFan : Shape → Bool → Shape
  | .base w,b => .base (w++[b])
  | .lower h w,b => .lower h (w++[b])
@[simp] theorem Shape.addFan_offset (h : Shape) (b : Bool) : (h.addFan b).offset=h.offset := by
  cases h <;> rfl
@[simp] theorem Shape.addFan_events (h : Shape) (b : Bool) (n : Nat) :
    (h.addFan b).events n=h.events n++[.fan n b] := by
  cases h <;> simp [Shape.addFan,Shape.events,List.map_append,List.append_assoc]
@[simp] theorem Shape.addFan_level (h : Shape) (b : Bool) (a : Context) (n : Nat) :
    (h.addFan b).level a n=mark b (h.level a n) := by
  cases h <;> simp [Shape.addFan,Shape.level,marks,List.foldl_append]
def Event.isBra : Event → Bool | .bra _ => true | _ => false
def Event.isCro : Event → Bool | .cro _ => true | _ => false
theorem fanEvents_no_bra (w : List Bool) (n : Nat) : ((w.map (Event.fan n)).filter Event.isBra)=[] := by
  induction w with
  | nil => rfl
  | cons b bs ih => simpa only [List.map_cons,List.filter_cons,Event.isBra,Bool.false_eq_true,if_false] using ih
@[simp] theorem Shape.bracket_count (h : Shape) (n : Nat) : ((h.events n).filter Event.isBra).length=h.offset := by
  induction h generalizing n with
  | base w => simp [Shape.events,Event.isBra,fanEvents_no_bra,Shape.offset]
  | lower h w ih => simp [Shape.events,List.filter_append,Event.isBra,fanEvents_no_bra,ih,Shape.offset]
theorem fanEvents_no_cro (w : List Bool) (n : Nat) : ((w.map (Event.fan n)).filter Event.isCro)=[] := by
  induction w with
  | nil => rfl
  | cons b bs ih => simpa only [List.map_cons,List.filter_cons,Event.isCro,Bool.false_eq_true,if_false] using ih
@[simp] theorem Shape.croissant_count (h : Shape) (n : Nat) : ((h.events n).filter Event.isCro).length=1 := by
  induction h generalizing n with
  | base w => simp [Shape.events,Event.isCro,fanEvents_no_cro]
  | lower h w ih => simp [Shape.events,List.filter_append,Event.isCro,fanEvents_no_cro,ih]

/-- A syntax occurrence of a free variable, preserving the fn/arg branch choice.
This is independent of graph labels and of the desired context formula. -/
inductive FreeOccurrence : Lambda.Term → Nat → Type
  | leaf (i : Nat) : FreeOccurrence (.var i) i
  | lambda {b : Lambda.Term} {k : Nat} : FreeOccurrence b (k+1) → FreeOccurrence (.lam b) k
  | function {f : Lambda.Term} {k : Nat} (a : Lambda.Term) : FreeOccurrence f k → FreeOccurrence (.app f a) k
  | argument (f : Lambda.Term) {a : Lambda.Term} {k : Nat} : FreeOccurrence a k → FreeOccurrence (.app f a) k

def FreeOccurrence.offset : {t : Lambda.Term} → {k : Nat} → FreeOccurrence t k → Nat
  | _,_,.leaf _ => 0
  | _,_,.lambda p => p.offset
  | _,_,.function _ p => p.offset
  | _,_,.argument _ p => p.offset+1

def FreeOccurrence.shape : {t : Lambda.Term} → {k : Nat} → FreeOccurrence t k → Shape
  | _,_,.leaf _ => .base []
  | _,_,.lambda p => p.shape
  | _,k,.function a p => if free a k then p.shape.addFan false else p.shape
  | _,k,.argument f p => .lower p.shape (if free f k then [true] else [])

theorem FreeOccurrence.free {t : Lambda.Term} {k : Nat} (p : FreeOccurrence t k) : AG.free t k := by
  induction p with
  | leaf => rfl
  | lambda p ih => exact ih
  | function a p ih => exact Or.inl ih
  | argument f p ih => exact Or.inr ih

theorem free_occurrence {t : Lambda.Term} {k : Nat} (h : AG.free t k) : Nonempty (FreeOccurrence t k) := by
  induction t generalizing k with
  | var i => change k=i at h; subst k; exact ⟨.leaf i⟩
  | lam b ih => obtain ⟨p⟩:=ih h; exact ⟨.lambda p⟩
  | app f a hf ha =>
    cases h with
    | inl h => obtain ⟨p⟩:=hf h; exact ⟨.function a p⟩
    | inr h => obtain ⟨p⟩:=ha h; exact ⟨.argument f p⟩

theorem FreeOccurrence.shape_offset {t : Lambda.Term} {k : Nat} (p : FreeOccurrence t k) : p.shape.offset=p.offset := by
  induction p with
  | leaf => rfl
  | lambda p ih => exact ih
  | function a p ih => simp [FreeOccurrence.shape,FreeOccurrence.offset]; split <;> simpa using ih
  | argument f p ih => simpa only [FreeOccurrence.shape,FreeOccurrence.offset,Shape.offset] using congrArg (·+1) ih
end Lamping.AG.InitialOffsets


namespace Lamping.AG.InitialOffsets
open Graph

theorem dupLeft_actual_events (n : Nat) :
    eventsOfEdges (DupNet n) (dupLeftEdges n)=(Shape.base [false]).events n := rfl
theorem dupRight_actual_events :
    eventsOfEdges (DupNet 0) dupRightEdges=(Shape.lower (.base []) [true]).events 0 := rfl

theorem dupLeft_all_labelings (n : Nat) (a b : Context)
    (labels : Labelling (DupNet n) (dupLeftEdges n) a b) :
    b=a.replace n ((a.tail n).cons (.o .empty)) := by
  have raw : RawLoop (DupNet n) (dupLeftEdges n) a b :=
    ⟨.inl (),rfl,lamBody,lamBind,HEq.rfl,HEq.rfl,rfl,rfl,labels⟩
  have run := InitialLabelling.events_run (encode_rawLoop_initial duplicatedVariable n (dupLeftEdges n) raw)
  rw [dupLeft_actual_events] at run
  simpa only [Shape.offset,Shape.level,marks,List.foldl_cons,List.foldl_nil,mark,Bool.false_eq_true,if_false,Nat.add_zero] using
    corrected_program_all_runs (.base [false]) n a b run

theorem dupRight_all_labelings (a b : Context)
    (labels : Labelling (DupNet 0) dupRightEdges a b) :
    b=a.replace 0 ((a.tail 1).cons (.star (.pair .empty (a.get 0)))) := by
  have raw : RawLoop (DupNet 0) dupRightEdges a b :=
    ⟨.inl (),rfl,lamBody,lamBind,HEq.rfl,HEq.rfl,rfl,rfl,labels⟩
  have run := InitialLabelling.events_run (encode_rawLoop_initial duplicatedVariable 0 dupRightEdges raw)
  rw [dupRight_actual_events] at run
  exact corrected_program_all_runs (.lower (.base []) [true]) 0 a b run
end Lamping.AG.InitialOffsets
namespace Lamping.AG.InitialOffsets
open Graph
section EventTransport
variable {K R B F W V : Type} [FiniteNames K] [FiniteNames R] [FiniteNames B]
  [FiniteNames F] [FiniteNames W] [FiniteNames V]
variable (c : Net signature K (B⊕F) W) (r : Net signature R F V)
def arrivalEvents {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
    (g : Net signature N B W) (e : Endpoint g) : List Event :=
  match g.wire e with
  | .inl ⟨n,p⟩ => (eventOfPort (g.label n).index (g.label n).sort p).toList
  | _ => []
theorem arrivalEvents_plugLeft (e : Endpoint c) :
    arrivalEvents (plug c r) (plugLeft c r e)=arrivalEvents c e := by
  unfold arrivalEvents
  rw [plugLeft_wire]
  rcases c.wire e with ⟨n,p⟩ | ((b | f) | ⟨w,d⟩) <;> rfl
theorem arrivalEvents_plugRight (e : Endpoint r) :
    arrivalEvents (plug c r) (plugRight c r e)=arrivalEvents r e := by
  unfold arrivalEvents
  rw [plugRight_wire]
  rcases r.wire e with ⟨n,p⟩ | (f | ⟨v,d⟩) <;> rfl

theorem events_plugLeft (es : List (Endpoint c)) :
    eventsOfEdges (plug c r) (es.map (plugLeft c r))=eventsOfEdges c es := by
  induction es with
  | nil => rfl
  | cons e es ih =>
    cases es with
    | nil => rfl
    | cons f es =>
      change arrivalEvents (plug c r) (plugLeft c r e) ++ eventsOfEdges (plug c r) ((f::es).map (plugLeft c r)) = arrivalEvents c e ++ eventsOfEdges c (f::es)
      rw [arrivalEvents_plugLeft,ih]
theorem events_plugRight (es : List (Endpoint r)) :
    eventsOfEdges (plug c r) (es.map (plugRight c r))=eventsOfEdges r es := by
  induction es with
  | nil => rfl
  | cons e es ih =>
    cases es with
    | nil => rfl
    | cons f es =>
      change arrivalEvents (plug c r) (plugRight c r e) ++ eventsOfEdges (plug c r) ((f::es).map (plugRight c r)) = arrivalEvents r e ++ eventsOfEdges r (f::es)
      rw [arrivalEvents_plugRight,ih]
end EventTransport
section EventsAppend
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable (g : Net signature N B W)
theorem events_append (xs ys : List (Endpoint g))
    (lastEmpty : ∀ e, xs.getLast?=some e → arrivalEvents g e=[]) :
    eventsOfEdges g (xs++ys)=eventsOfEdges g xs++eventsOfEdges g ys := by
  induction xs with
  | nil => rfl
  | cons e xs ih =>
    cases xs with
    | nil =>
      cases ys with
      | nil => rfl
      | cons f ys =>
        change arrivalEvents g e ++ eventsOfEdges g (f::ys)=[]++eventsOfEdges g (f::ys)
        rw [lastEmpty e rfl]
    | cons f xs =>
      change arrivalEvents g e ++ eventsOfEdges g ((f::xs)++ys)=(arrivalEvents g e++eventsOfEdges g (f::xs))++eventsOfEdges g ys
      rw [ih (by intro x hx; exact lastEmpty x (by simpa using hx)),List.append_assoc]

theorem LocalPath.last_event_empty {x y : B} {a b : Context} (p : LocalPath g x y a b)
    (e : Endpoint g) (last : p.edges.getLast?=some e) : arrivalEvents g e=[] := by
  have eq : e=g.wire (.inr (.inl y)) := Option.some.inj (last.symm.trans p.finish)
  rw [eq]
  unfold arrivalEvents
  rw [Pairing.involutive]
end EventsAppend
end Lamping.AG.InitialOffsets

namespace Lamping.AG.InitialOffsets
open Graph
section LoopProjection
variable {K R B F W V : Type} [FiniteNames K] [FiniteNames R] [FiniteNames B]
  [FiniteNames F] [FiniteNames W] [FiniteNames V]
variable (c : Net signature K (B⊕F) W) (r : Net signature R F V)
variable {bp : B→Bool} {fp : F→Bool} {wp : W→Bool} {vp : V→Bool}
theorem plugRight_injective : Function.Injective (plugRight c r) := by
  intro x y eq
  exact Sum.inr.inj ((plugEnd c.label r.label).injective eq)
/-- Reflect a raw loop wholly into its encoded child. The no-return premise is
only a property of the actual surrounding source patch and is discharged there. -/
theorem rawLoop_plugRight (cflow : FlowOn c (Sum.elim bp (fun z => !(fp z))) wp)
    (rflow : FlowOn r fp vp)
    (noReturn : ∀ z z' A B', fp z=false → fp z'=true → LocalPath c (.inr z) (.inr z') A B' → False)
    {es : List (Endpoint (plug c r))} {a b : Context}
    (loop : RawLoop (plug c r) es a b) (v : R) (binder : loop.binder=.inr v) :
    ∃ rs, ∃ child : RawLoop r rs a b, child.binder=v ∧ es=rs.map (plugRight c r) := by
  rcases loop with ⟨binderNode,isLam,body,bind,bodyRole,bindRole,start,finish,labels⟩
  dsimp only at binder
  subst binderNode
  cases es with
  | nil => simp at start
  | cons e tail =>
    simp only [List.head?_cons,Option.some.injEq] at start
    subst e
    have out : endPolarity fp vp (Sum.inl ⟨v,body⟩ : Endpoint r)=true :=
      lambda_body_polarity isLam bodyRole
    have finish' : (plugRight c r (.inl ⟨v,body⟩)::tail).getLast?=
        some (plugRight c r (r.wire (.inl ⟨v,bind⟩))) := by
      simpa only [←plugRight_wire] using finish
    obtain ⟨xs,tailMap,localLabels⟩ := labels.child_no_escape c r cflow rflow noReturn out finish'
    have localFinish : (.inl ⟨v,body⟩::xs).getLast?=some (r.wire (.inl ⟨v,bind⟩)) := by
      rw [tailMap] at finish'
      change ((.inl ⟨v,body⟩::xs).map (plugRight c r)).getLast?=some _ at finish'
      rw [List.getLast?_map] at finish'
      cases last : (.inl ⟨v,body⟩::xs).getLast? with
      | none => simp [last] at finish'
      | some z =>
        simp only [last,Option.map_some,Option.some.injEq] at finish'
        rw [(plugRight_injective c r) finish']
    refine ⟨.inl ⟨v,body⟩::xs,⟨v,isLam,body,bind,bodyRole,bindRole,rfl,localFinish,localLabels⟩,rfl,?_⟩
    rw [tailMap]; rfl
end LoopProjection
end Lamping.AG.InitialOffsets
namespace Lamping.AG.InitialOffsets
open Graph
section UnionProjection
variable {N M B C W V : Type} [FiniteNames N] [FiniteNames M] [FiniteNames B]
  [FiniteNames C] [FiniteNames W] [FiniteNames V]
variable (g : Net signature N B W) (h : Net signature M C V)
def unionL (e : Endpoint g) : Endpoint (unionNet g h) := unionEnd g.label h.label (.inl e)
def unionR (e : Endpoint h) : Endpoint (unionNet g h) := unionEnd g.label h.label (.inr e)
theorem unionL_injective : Function.Injective (unionL g h) := by
  intro x y eq; exact Sum.inl.inj ((unionEnd g.label h.label).injective eq)
theorem unionR_injective : Function.Injective (unionR g h) := by
  intro x y eq; exact Sum.inr.inj ((unionEnd g.label h.label).injective eq)
theorem turn_union_cross {x : Endpoint g} {y : Endpoint h} {a b : Context}
    (turn : LabelledTurn (unionNet g h) (unionL g h x) (unionR g h y) a b) : False := by
  rcases x with ⟨n,p⟩ | (b | ⟨w,d⟩)
  all_goals rcases y with ⟨m,q⟩ | (c | ⟨v,e⟩)
  all_goals cases turn
theorem turn_unionL_reflect {x y : Endpoint g} {a b : Context}
    (turn : LabelledTurn (unionNet g h) (unionL g h x) (unionL g h y) a b) : LabelledTurn g x y a b := by
  rcases x with ⟨n,p⟩ | (b | ⟨w,d⟩)
  all_goals rcases y with ⟨m,q⟩ | (c | ⟨v,e⟩)
  all_goals cases turn
  · exact .node _ _ _ ‹Traversal _ _ _ _ _ _›
  · exact .transparent _ _ _
theorem turn_unionR_reflect {x y : Endpoint h} {a b : Context}
    (turn : LabelledTurn (unionNet g h) (unionR g h x) (unionR g h y) a b) : LabelledTurn h x y a b := by
  rcases x with ⟨n,p⟩ | (b | ⟨w,d⟩)
  all_goals rcases y with ⟨m,q⟩ | (c | ⟨v,e⟩)
  all_goals cases turn
  · exact .node _ _ _ ‹Traversal _ _ _ _ _ _›
  · exact .transparent _ _ _
theorem labels_unionL_stay {x : Endpoint g} {es : List (Endpoint (unionNet g h))} {a b : Context}
    (path : Labelling (unionNet g h) (unionL g h x::es) a b) :
    ∃ xs, es=xs.map (unionL g h) ∧ Labelling g (x::xs) a b := by
  induction es generalizing x a b with
  | nil => cases path; exact ⟨[],rfl,.single _ _⟩
  | cons e es ih =>
    have inv := (unionEnd g.label h.label).right_inv e
    generalize (unionEnd g.label h.label).invFun e = side at inv
    cases side with
    | inl y =>
      have eq : e=unionL g h y := inv.symm
      subst e
      cases path with
      | cons turn rest =>
        change LabelledTurn (unionNet g h) ((unionNet g h).wire (unionEnd g.label h.label (.inl x))) _ _ _ at turn
        rw [union_left] at turn
        have localTurn := turn_unionL_reflect g h turn
        obtain ⟨xs,heq,labels⟩ := ih rest
        exact ⟨y::xs,congrArg (unionL g h y::·) heq,.cons localTurn labels⟩
    | inr y =>
      have eq : e=unionR g h y := inv.symm
      subst e
      cases path with
      | cons turn rest =>
        rw [show (unionNet g h).wire (unionL g h x)=unionL g h (g.wire x) from union_left g h x] at turn
        exact False.elim (turn_union_cross g h turn)
theorem labels_unionR_stay {x : Endpoint h} {es : List (Endpoint (unionNet g h))} {a b : Context}
    (path : Labelling (unionNet g h) (unionR g h x::es) a b) :
    ∃ xs, es=xs.map (unionR g h) ∧ Labelling h (x::xs) a b := by
  induction es generalizing x a b with
  | nil => cases path; exact ⟨[],rfl,.single _ _⟩
  | cons e es ih =>
    have inv := (unionEnd g.label h.label).right_inv e
    generalize (unionEnd g.label h.label).invFun e = side at inv
    cases side with
    | inr y =>
      have eq : e=unionR g h y := inv.symm
      subst e
      cases path with
      | cons turn rest =>
        rw [show (unionNet g h).wire (unionR g h x)=unionR g h (h.wire x) from union_right g h x] at turn
        have localTurn := turn_unionR_reflect g h turn
        obtain ⟨xs,heq,labels⟩ := ih rest
        exact ⟨y::xs,congrArg (unionR g h y::·) heq,.cons localTurn labels⟩
    | inl y =>
      have eq : e=unionL g h y := inv.symm
      subst e
      cases path with
      | cons turn rest =>
        rw [show (unionNet g h).wire (unionR g h x)=unionR g h (h.wire x) from union_right g h x] at turn
        exact False.elim (turn_union_cross g h turn.reverse)
end UnionProjection
end Lamping.AG.InitialOffsets
namespace Lamping.AG.InitialOffsets
open Graph Lambda
section UnionRaw
variable {N M B C W V : Type} [FiniteNames N] [FiniteNames M] [FiniteNames B]
  [FiniteNames C] [FiniteNames W] [FiniteNames V]
variable (g : Net signature N B W) (h : Net signature M C V)
theorem rawLoop_unionL {es : List (Endpoint (unionNet g h))} {a b : Context}
    (loop : RawLoop (unionNet g h) es a b) (v : N) (binder : loop.binder=.inl v) :
    ∃ rs, ∃ child : RawLoop g rs a b, child.binder=v ∧ es=rs.map (unionL g h) := by
  rcases loop with ⟨node,isLam,body,bind,bodyRole,bindRole,start,finish,labels⟩
  dsimp only at binder; subst node
  cases es with
  | nil => simp at start
  | cons e tail =>
    simp only [List.head?_cons,Option.some.injEq] at start; subst e
    obtain ⟨xs,tailMap,localLabels⟩ := labels_unionL_stay g h (x:=.inl ⟨v,body⟩) labels
    have localFinish : (.inl ⟨v,body⟩::xs).getLast?=some (g.wire (.inl ⟨v,bind⟩)) := by
      rw [tailMap] at finish
      change ((.inl ⟨v,body⟩::xs).map (unionL g h)).getLast?=some ((unionNet g h).wire (unionL g h (.inl ⟨v,bind⟩))) at finish
      rw [show (unionNet g h).wire (unionL g h (.inl ⟨v,bind⟩))=unionL g h (g.wire (.inl ⟨v,bind⟩)) from union_left g h _,List.getLast?_map] at finish
      cases last : (.inl ⟨v,body⟩::xs).getLast? with
      | none => simp [last] at finish
      | some z => simp only [last,Option.map_some,Option.some.injEq] at finish; rw [unionL_injective g h finish]
    exact ⟨_,⟨v,isLam,body,bind,bodyRole,bindRole,rfl,localFinish,localLabels⟩,rfl,by rw [tailMap]; rfl⟩
theorem rawLoop_unionR {es : List (Endpoint (unionNet g h))} {a b : Context}
    (loop : RawLoop (unionNet g h) es a b) (v : M) (binder : loop.binder=.inr v) :
    ∃ rs, ∃ child : RawLoop h rs a b, child.binder=v ∧ es=rs.map (unionR g h) := by
  rcases loop with ⟨node,isLam,body,bind,bodyRole,bindRole,start,finish,labels⟩
  dsimp only at binder; subst node
  cases es with
  | nil => simp at start
  | cons e tail =>
    simp only [List.head?_cons,Option.some.injEq] at start; subst e
    obtain ⟨xs,tailMap,localLabels⟩ := labels_unionR_stay g h (x:=.inl ⟨v,body⟩) labels
    have localFinish : (.inl ⟨v,body⟩::xs).getLast?=some (h.wire (.inl ⟨v,bind⟩)) := by
      rw [tailMap] at finish
      change ((.inl ⟨v,body⟩::xs).map (unionR g h)).getLast?=some ((unionNet g h).wire (unionR g h (.inl ⟨v,bind⟩))) at finish
      rw [show (unionNet g h).wire (unionR g h (.inl ⟨v,bind⟩))=unionR g h (h.wire (.inl ⟨v,bind⟩)) from union_right g h _,List.getLast?_map] at finish
      cases last : (.inl ⟨v,body⟩::xs).getLast? with
      | none => simp [last] at finish
      | some z => simp only [last,Option.map_some,Option.some.injEq] at finish; rw [unionR_injective g h finish]
    exact ⟨_,⟨v,isLam,body,bind,bodyRole,bindRole,rfl,localFinish,localLabels⟩,rfl,by rw [tailMap]; rfl⟩
end UnionRaw

theorem lambdaUsed_noReturn (n : Nat) (body : Term) (used : free body 0) :
    ∀ z z' A B, initialBoundaryPolarity z=false → initialBoundaryPolarity z'=true →
      LocalPath (lambdaUsed n body used) (.inr z) (.inr z') A B → False := by
  rintro (u|x) (v|y) A B hz hz' p
  · cases hz
  · cases hz
  · cases v; exact lambdaUsed_FV_no_child_root n body used x p
  · cases hz'
theorem lambdaUnused_noReturn (n : Nat) (body : Term) (unused : ¬free body 0) :
    ∀ z z' A B, initialBoundaryPolarity z=false → initialBoundaryPolarity z'=true →
      LocalPath (lambdaUnused n body unused) (.inr z) (.inr z') A B → False := by
  rintro (u|x) (v|y) A B hz hz' p
  · cases hz
  · cases hz
  · cases v; exact lambdaUnused_FV_no_child_root n body unused x p
  · cases hz'
theorem appPatch_noReturn (n : Nat) (f a : Term) :
    ∀ z z' A B, Sum.elim initialBoundaryPolarity initialBoundaryPolarity z=false →
      Sum.elim initialBoundaryPolarity initialBoundaryPolarity z'=true →
      LocalPath (appPatch n f a) (.inr z) (.inr z') A B → False := by
  rintro ((u|x)|(v|y)) ((u'|x')|(v'|y')) A B hz hz' p
  all_goals try cases hz
  all_goals try cases hz'
  · cases u'; exact appPatch_FV_no_child_root n f a (.inl x) false p
  · cases v'; exact appPatch_FV_no_child_root n f a (.inl x) true p
  · cases u'; exact appPatch_FV_no_child_root n f a (.inr y) false p
  · cases v'; exact appPatch_FV_no_child_root n f a (.inr y) true p
end Lamping.AG.InitialOffsets

namespace Lamping.AG.InitialOffsets
open Graph Lambda
/-- Every raw labelled loop in every actual initial encoding preserves the shell
of its own binder, including arbitrarily deeply nested binders. The proof reflects
actual paths into children and uses source patch separation, never a supplied shell. -/
theorem encode_rawLoop_shell (t : Term) (n : Nat) (es : List (Endpoint (encode n t).net))
    (a b : Context) (loop : RawLoop (encode n t).net es a b) :
    Context.SameShell ((encode n t).net.label loop.binder).index a b := by
  induction t generalizing n a b with
  | var k =>
    have impossible := loop.isLam
    change Kind.op .cro=Kind.op .lam at impossible
    cases impossible
  | lam body ih =>
    revert es
    dsimp only [encode]
    obtain ⟨vp,rflow⟩ := encode_flow body n
    by_cases used : free body 0
    · rw [dif_pos used]
      intro es loop
      cases binder : loop.binder with
      | inl u =>
        apply Labelling.low_bound loop.proper n
        rintro (u | v) op kind
        · exact Nat.le_refl n
        · exact encode_level_lower body n v kind
      | inr v =>
        obtain ⟨rs,child,childBinder,_⟩ := rawLoop_plugRight (lambdaUsed n body used) (encode n body).net
          (lambdaUsed_flow n body used) rflow (lambdaUsed_noReturn n body used) loop v binder
        have shell := ih n rs a b child
        change Context.SameShell ((encode n body).net.label v).index a b
        simpa only [childBinder] using shell
    · rw [dif_neg used]
      intro es loop
      cases binder : loop.binder with
      | inl patch =>
        cases patch with
        | inl u =>
          apply Labelling.low_bound loop.proper n
          rintro ((u|v)|w) op kind
          · exact Nat.le_refl n
          · cases kind
          · exact encode_level_lower body n w kind
        | inr u => have impossible:=loop.isLam; rw [binder] at impossible; cases impossible
      | inr v =>
        obtain ⟨rs,child,childBinder,_⟩ := rawLoop_plugRight (lambdaUnused n body used) (encode n body).net
          (lambdaUnused_flow n body used) rflow (lambdaUnused_noReturn n body used) loop v binder
        have shell := ih n rs a b child
        change Context.SameShell ((encode n body).net.label v).index a b
        simpa only [childBinder] using shell
  | app f arg hf ha =>
    dsimp only [encode] at loop ⊢
    cases binder : loop.binder with
    | inl patch =>
      rcases patch with u | (x | x)
      all_goals have impossible:=loop.isLam; rw [binder] at impossible; cases impossible
    | inr v =>
      obtain ⟨wp,fnFlow⟩ := encode_flow f n
      obtain ⟨vp,argFlow⟩ := encode_flow arg (n+1)
      have unionFlow := FlowOn.union (g:=(encode n f).net) (h:=(encode (n+1) arg).net)
        (bp:=initialBoundaryPolarity) (cp:=initialBoundaryPolarity) (wp:=wp) (vp:=vp) fnFlow argFlow
      obtain ⟨rs,child,childBinder,_⟩ := rawLoop_plugRight (appPatch n f arg)
        (unionNet (encode n f).net (encode (n+1) arg).net) (appPatch_flow n f arg) unionFlow
        (appPatch_noReturn n f arg) loop v binder
      cases v with
      | inl v =>
        obtain ⟨ss,localLoop,localBinder,_⟩ := rawLoop_unionL (encode n f).net (encode (n+1) arg).net child v childBinder
        have shell := hf n ss a b localLoop
        change Context.SameShell ((encode n f).net.label v).index a b
        simpa only [localBinder] using shell
      | inr v =>
        obtain ⟨ss,localLoop,localBinder,_⟩ := rawLoop_unionR (encode n f).net (encode (n+1) arg).net child v childBinder
        have shell := ha (n+1) ss a b localLoop
        change Context.SameShell ((encode (n+1) arg).net.label v).index a b
        simpa only [localBinder] using shell
end Lamping.AG.InitialOffsets
namespace Lamping.AG.InitialOffsets
open Graph Lambda
/-- Shell preservation turns a raw actual initial loop into a binding loop;
no binding condition is part of the input. -/
def encode_rawLoop_binding (t : Term) (n : Nat)
    (es : List (Endpoint (encode n t).net)) (a b : Context)
    (loop : RawLoop (encode n t).net es a b) : BindingLoop (encode n t).net es a b where
  binder := loop.binder
  isLam := loop.isLam
  body := loop.body
  bind := loop.bind
  body_role := loop.body_role
  bind_role := loop.bind_role
  start := loop.start
  finish := loop.finish
  proper := loop.proper
  forward := (encode_rawLoop_initial t n es loop).forward
  shell := encode_rawLoop_shell t n es a b loop

/-- Every direct printed passage is defined for every input context. -/
theorem Passage.relabel {i k p q a b} (h : Passage i k p q a b) (c : Context) :
    ∃ d, Passage i k p q c d := by
  cases h with
  | fanO => exact ⟨_,(Event.fan i false).apply_rel c⟩
  | fanStar => exact ⟨_,(Event.fan i true).apply_rel c⟩
  | cro => exact ⟨_,(Event.cro i).apply_rel c⟩
  | bra => exact ⟨_,(Event.bra i).apply_rel c⟩
  | appFun => exact ⟨c,.appFun c⟩
  | appArg => exact ⟨c,.appArg c⟩
  | lamBody => exact ⟨c,.lamBody c⟩
section Relabel
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable {g : Net signature N B W}
theorem InitialTurn.relabel {e f : Endpoint g} {a b : Context}
    (h : AG.InitialTurn (g:=g) e f a b) (c : Context) :
    ∃ d, LabelledTurn g e f c d := by
  cases h with
  | node v p q rule =>
    obtain ⟨d,next⟩ := Passage.relabel rule c
    exact ⟨d,.node v p q (.direct next)⟩
  | transparent w dir _ => exact ⟨c,.transparent w dir c⟩
theorem InitialLabelling.relabel {es : List (Endpoint g)} {a b : Context}
    (h : AG.InitialLabelling (g:=g) es a b) (c : Context) :
    ∃ d, Labelling g es c d := by
  induction h generalizing c with
  | single e a => exact ⟨c,.single e c⟩
  | cons turn tail ih =>
    obtain ⟨mid,next⟩ := InitialTurn.relabel turn c
    obtain ⟨d,last⟩ := ih mid
    exact ⟨d,.cons next last⟩
end Relabel
/-- Universal transparency of the actual source loop's edge sequence: every
input context admits output labels and the binder's low shell is preserved. -/
theorem encode_rawLoop_transparent (t : Term) (n : Nat)
    (es : List (Endpoint (encode n t).net)) {a b : Context}
    (loop : RawLoop (encode n t).net es a b) (c : Context) :
    ∃ d, Nonempty (BindingLoop (encode n t).net es c d) := by
  obtain ⟨d,labels⟩ := InitialLabelling.relabel (encode_rawLoop_initial t n es loop) c
  let raw : RawLoop (encode n t).net es c d :=
    { loop with proper := labels }
  exact ⟨d,⟨encode_rawLoop_binding t n es c d raw⟩⟩
end Lamping.AG.InitialOffsets

namespace Lamping.AG.InitialOffsets
open Graph
section WholeEvents
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable (g : Net signature N B W)
/-- The independently computed word of arrivals, including a final arrival.
For a boundary-ended path that final arrival emits nothing. -/
def allEvents (es : List (Endpoint g)) : List Event := es.flatMap (arrivalEvents g)
theorem events_eq_allEvents (es : List (Endpoint g))
    (lastEmpty : ∀ e, es.getLast?=some e → arrivalEvents g e=[]) :
    eventsOfEdges g es=allEvents g es := by
  induction es with
  | nil => rfl
  | cons e es ih =>
    cases es with
    | nil =>
      have last := lastEmpty e rfl
      simp [eventsOfEdges,allEvents,last]
    | cons f es =>
      change arrivalEvents g e ++ eventsOfEdges g (f::es)=arrivalEvents g e ++ allEvents g (f::es)
      rw [ih (by intro x hx; exact lastEmpty x (by simpa using hx))]

theorem LocalPath.events_all {x y : B} {a b : Context} (p : LocalPath g x y a b) :
    eventsOfEdges g p.edges=allEvents g p.edges :=
  events_eq_allEvents g p.edges (LocalPath.last_event_empty g p)
end WholeEvents
end Lamping.AG.InitialOffsets
