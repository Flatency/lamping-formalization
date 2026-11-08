import Lamping.Lamping.ReadbackCorrectness
import Lamping.Lamping.PathLabelDeterminism
import Lamping.Lamping.ControlOnlyConnections

namespace Lamping.AG.Readback
open Graph

private theorem control_execution_exists {i : Nat} {kind : Kind} {p q : Port kind}
    {before after : Context} (rule : Traversal i kind p q before after)
    (control : kind=.op .fan ∨kind=.op .cro ∨kind=.op .bra)
    (a : ContextData) (input : Context.ofList a=before) :
    ∃ data,executeControl i kind p a=some (q,data) := by
  cases rule with
  | direct passage =>
    cases passage with
    | fanO shell tail child => exact ⟨_,rfl⟩
    | fanStar shell tail child => exact ⟨_,rfl⟩
    | cro shell tail => exact ⟨_,rfl⟩
    | bra shell tail left right => exact ⟨_,rfl⟩
    | appFun context => rcases control with h|h|h <;> cases h
    | appArg context => rcases control with h|h|h <;> cases h
    | lamBody context => rcases control with h|h|h <;> cases h
  | inverse passage =>
    cases passage with
    | fanO shell tail child =>
      have shape : a.get i=.o child := by
        rw [←ContextData.denote_get,input]
        simp [Context.replace]
      simp only [executeControl,shape]
      exact ⟨_,rfl⟩
    | fanStar shell tail child =>
      have shape : a.get i=.star child := by
        rw [←ContextData.denote_get,input]
        simp [Context.replace]
      simp only [executeControl,shape]
      exact ⟨_,rfl⟩
    | cro shell tail =>
      have shape : a.get i=.empty := by
        rw [←ContextData.denote_get,input]
        simp [Context.replace]
      simp only [executeControl,shape]
      exact ⟨_,rfl⟩
    | bra shell tail left right =>
      have shape : a.get i=.pair left right := by
        rw [←ContextData.denote_get,input]
        simp [Context.replace]
      simp only [executeControl,shape]
      exact ⟨_,rfl⟩
    | appFun context => rcases control with h|h|h <;> cases h
    | appArg context => rcases control with h|h|h <;> cases h
    | lamBody context => rcases control with h|h|h <;> cases h

/-- A genuine control traversal is in the exact executable domain. No test for
domain membership or chosen finite representation is supplied by the caller. -/
theorem executeControl_complete {i : Nat} {kind : Kind} {p q : Port kind}
    {before after : Context} (rule : Traversal i kind p q before after)
    (control : kind=.op .fan ∨kind=.op .cro ∨kind=.op .bra)
    (a : ContextData) (input : Context.ofList a=before) :
    ∃ data,executeControl i kind p a=some (q,data) ∧Context.ofList data=after := by
  obtain ⟨data,success⟩ := control_execution_exists rule control a input
  refine ⟨data,success,?_⟩
  have computed := executeControl_sound i kind p q a data success
  rw [input] at computed
  exact computed.output_unique rule

section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable {g : Net signature N B W}

private theorem control_port_kind (kind : Kind) (p : Port kind)
    (control : kind=.op .fan ∨kind=.op .cro ∨kind=.op .bra) :
    portKind kind p=none := by
  rcases control with rfl|rfl|rfl <;> rfl

theorem scanOne_next_complete {e f : Endpoint g} {before after : Context}
    (turn : LabelledTurn g (g.wire e) f before after)
    (controlOnly : ControlOnlyTurn (g:=g) e f)
    (a : ContextData) (input : Context.ofList a=before) :
    ∃ data,scanOne g e a=.next f data ∧Context.ofList data=after := by
  rcases controlOnly with ⟨vertex,direction,arrives,rfl⟩ |
      ⟨node,p,q,op,sort,control,arrives,rfl⟩
  · rw [arrives] at turn
    cases turn
    exact ⟨a,by simp [scanOne,arrives],input⟩
  · rw [arrives] at turn
    cases turn with
    | node node p q rule =>
      have controlKind : (g.label node).sort=.op .fan ∨
          (g.label node).sort=.op .cro ∨(g.label node).sort=.op .bra := by
        rcases control with rfl|rfl|rfl
        · exact Or.inl sort
        · exact Or.inr (Or.inl sort)
        · exact Or.inr (Or.inr sort)
      have role := control_port_kind (g.label node).sort p controlKind
      obtain ⟨data,success,output⟩ := executeControl_complete rule controlKind a input
      exact ⟨data,by simp [scanOne,arrives,role,success],output⟩

/-- Simulation follows one supplied finite labelled path. Its literal
intermediate occurrences all cross controls; fuel decreases on that same list.
The output context is computed, not obtained by choosing a representation. -/
theorem scanFuel_of_control_path {es : List (Endpoint g)} {before after : Context}
    (labels : Labelling g es before after)
    (controlOnly : ∀ e f,(e,f)∈es.zip es.tail →ControlOnlyTurn (g:=g) e f)
    (last : Endpoint g) (lastEq : es.getLast?=some last)
    (arrival : NodePort signature N g.label) (kind : AccessKind)
    (finish : g.wire last=.inl arrival)
    (terminal : portKind (g.label arrival.1).sort arrival.2=some kind)
    (a : ContextData) (input : Context.ofList a=before) :
    ∃ first data,es.head?=some first ∧Context.ofList data=after ∧
      scanFuel g es.length first a=.stopped (.terminal arrival kind data) := by
  induction labels generalizing a with
  | single e context =>
    simp only [List.getLast?_singleton,Option.some.injEq] at lastEq
    subst last
    exact ⟨e,a,rfl,input,by simp [scanFuel,scanOne,finish,terminal]⟩
  | @cons e f es before middle after turn tail ih =>
    have thisControl : ControlOnlyTurn (g:=g) e f := controlOnly e f (by simp)
    obtain ⟨middleData,step,contextEq⟩ := scanOne_next_complete turn thisControl a input
    have tailControl : ∀ x y,(x,y)∈(f::es).zip (f::es).tail →
        ControlOnlyTurn (g:=g) x y := by
      intro x y member
      apply controlOnly x y
      simp only [List.tail_cons,List.zip_cons_cons]
      exact List.mem_cons.mpr (Or.inr member)
    have tailLast : (f::es).getLast?=some last := by simpa using lastEq
    obtain ⟨first,data,headEq,output,run⟩ := ih tailControl tailLast middleData contextEq
    have firstEq : first=f := by simpa using headEq.symm
    subst first
    refine ⟨e,data,rfl,output,?_⟩
    simpa only [List.length_cons,scanFuel,step] using run

/-- Existing ordinary forward-path geometry supplies the control-only fact
from zero access word. This is a finite-path theorem, not a graph-size bound. -/
theorem scanFuel_of_empty_word {es : List (Endpoint g)} {before after : Context}
    (labels : Labelling g es before after) (forward : Forward g es)
    (word : accessWord g es=[])
    (last : Endpoint g) (lastEq : es.getLast?=some last)
    (arrival : NodePort signature N g.label) (kind : AccessKind)
    (finish : g.wire last=.inl arrival)
    (terminal : portKind (g.label arrival.1).sort arrival.2=some kind)
    (a : ContextData) (input : Context.ofList a=before) :
    ∃ first data,es.head?=some first ∧Context.ofList data=after ∧
      scanFuel g es.length first a=.stopped (.terminal arrival kind data) :=
  scanFuel_of_control_path labels (forward.empty_word_control_only word)
    last lastEq arrival kind finish terminal a input

end
end Lamping.AG.Readback
