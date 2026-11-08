import Lamping.Lamping.InitialAddresses

namespace Lamping.AG
open Graph Lambda

/-- Geometric input ports of original APP, lambda and variable-Cro nodes. -/
def initialAtomInput : (kind : Kind) → Port kind → Bool
  | .op .app,.inr false => true
  | .op .lam,.inl () => true
  | .op .cro,.inr () => true
  | _,_ => false

section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable {g : Net signature N B W}

def initialAtomAddress (nodes : N → Path) : Endpoint g → Option Path
  | .inl ⟨n,p⟩ => if initialAtomInput (g.label n).sort p then some (nodes n) else none
  | _ => none

/-- Marker position is a physical port test, independent of label words. -/
def InitialMarkerAt (nodes : N → Path) (e : Endpoint g) (p : Path) : Prop :=
  initialAtomAddress nodes (g.wire e)=some p

private theorem input_address {kind : Kind} {port : Port kind} (p : Path)
    (input : initialAtomInput kind port=true) : syntaxPortAddress kind port p=some p := by
  cases kind with
  | garbage => cases port;cases input
  | op op =>
    cases op <;> cases port with
    | inl u => cases u <;> simp_all [initialAtomInput,syntaxPortAddress]
    | inr aux => cases aux <;> simp_all [initialAtomInput,syntaxPortAddress]

private theorem passage_no_input {kind : Kind} {i : Nat} {p q : Port kind}
    {a b : Context} (rule : Passage i kind p q a b) : initialAtomInput kind q=false := by
  cases rule <;> rfl

theorem InitialTurn.output_no_initial_input {e f : Endpoint g} {a b : Context}
    (turn : InitialTurn (g:=g) e f a b) (nodes : N → Path) :
    initialAtomAddress nodes f=none := by
  cases turn with
  | node n p q rule => simp only [initialAtomAddress,passage_no_input rule,Bool.false_eq_true,ite_false]
  | transparent => rfl

/-- Restrict the actual whole derivation, retaining its final assignment. -/
theorem InitialLabelling.suffix {pre es : List (Endpoint g)} {a b : Context}
    (labels : InitialLabelling (g:=g) (pre++es) a b) (nonempty : es≠[]) :
    ∃ middle,InitialLabelling (g:=g) es middle b := by
  cases es with
  | nil => exact False.elim (nonempty rfl)
  | cons f es =>
   induction pre generalizing a with
  | nil => exact ⟨a,labels⟩
  | cons e pre ih =>
    cases pre with
    | nil => cases labels with | cons turn tail => exact ⟨_,tail⟩
    | cons x pre => cases labels with | cons turn tail => exact ih tail

/-- The singleton head is explicit: a labelled path alone cannot forbid it. -/
theorem InitialLabelling.no_initial_inputs {es : List (Endpoint g)} {a b : Context}
    (labels : InitialLabelling (g:=g) es a b) (nodes : N → Path)
    (headNoInput : ∀ e,es.head?=some e → initialAtomAddress nodes e=none) :
    ∀ i : Fin es.length,initialAtomAddress nodes es[i]=none := by
  induction labels with
  | single e a =>
    intro i
    have h : i=⟨0,by simp⟩ := by
      apply Fin.ext
      change i.val=0
      have bound : i.val<1 := i.isLt
      omega
    subst i
    exact headNoInput e rfl
  | @cons e f tail a middle b turn after ih =>
    intro i
    refine Fin.cases (headNoInput e rfl) (fun j => ?_) i
    exact ih (fun x head => by
      have same : f=x := Option.some.inj head
      subst x
      exact turn.output_no_initial_input nodes) j

variable {boundary : B → Option Path} (addr : Addressing g boundary)

theorem InitialMarkerAt.phase {e : Endpoint g} {p : Path}
    (marker : InitialMarkerAt addr.nodes e p) :
    endpointAddress g addr.nodes boundary addr.vertices e=some p := by
  unfold InitialMarkerAt at marker
  have same := addr.wiring e
  cases wireEq : g.wire e with
  | inl np =>
    rcases np with ⟨n,port⟩
    rw [wireEq] at marker same
    simp only [initialAtomAddress] at marker
    split at marker
    next positive =>
      have eq := Option.some.inj marker
      rw [←eq]
      exact same.symm.trans (input_address (addr.nodes n) (by simpa using positive))
    next negative => cases marker
  | inr outside => cases outside <;> simp [wireEq,initialAtomAddress] at marker

private theorem passage_zero_table {kind : Kind} {i : Nat} {p q : Port kind}
    {a b : Context} (rule : Passage i kind p q a b) (address : Path)
    (zero : syntaxDepartureWord kind q=[]) :
    (∀ r,syntaxPortAddress kind q address=some r →
      syntaxPortAddress kind p address=some r ∧
        (if initialAtomInput kind p then some address else none)=none) ∧
    (∀ r,syntaxPortAddress kind p address=some r →
      syntaxPortAddress kind q address=none →
        (if initialAtomInput kind p then some address else none)=some r) ∧
    (syntaxPortAddress kind p address=none →
      syntaxPortAddress kind q address=none ∧
        (if initialAtomInput kind p then some address else none)=none) := by
  cases rule <;> simp_all [syntaxDepartureWord,syntaxPortAddress,initialAtomInput,appArg,lamBody]

private theorem turn_zero_table {x f : Endpoint g} {a b : Context}
    (turn : InitialTurn (g:=g) x f a b) (nodes : N → Path)
    (vertices : W → Option Path) (boundary : B → Option Path)
    (zero : arrivalWord g f=[]) :
    (∀ p,endpointAddress g nodes boundary vertices f=some p →
      endpointAddress g nodes boundary vertices x=some p ∧ initialAtomAddress nodes x=none) ∧
    (∀ p,endpointAddress g nodes boundary vertices x=some p →
      endpointAddress g nodes boundary vertices f=none → initialAtomAddress nodes x=some p) ∧
    (endpointAddress g nodes boundary vertices x=none →
      endpointAddress g nodes boundary vertices f=none ∧ initialAtomAddress nodes x=none) := by
  cases turn with
  | node n p q rule =>
    exact passage_zero_table rule (nodes n) zero
  | transparent w d a =>
    simp only [endpointAddress,initialAtomAddress]
    constructor
    · intro p phase;exact ⟨phase,True.intro⟩
    constructor
    · intro p positive negative;exact False.elim (Option.noConfusion (positive.symm.trans negative))
    · intro phase;exact ⟨phase,True.intro⟩

theorem InitialTurn.initial_marker_phases {e f : Endpoint g} {a b : Context}
    (turn : InitialTurn (g:=g) (g.wire e) f a b) (zero : arrivalWord g f=[]) :
    (∀ p,endpointAddress g addr.nodes boundary addr.vertices f=some p →
      endpointAddress g addr.nodes boundary addr.vertices e=some p ∧
        ∀ q,¬InitialMarkerAt addr.nodes e q) ∧
    (∀ p,endpointAddress g addr.nodes boundary addr.vertices e=some p →
      endpointAddress g addr.nodes boundary addr.vertices f=none → InitialMarkerAt addr.nodes e p) ∧
    (endpointAddress g addr.nodes boundary addr.vertices e=none →
      endpointAddress g addr.nodes boundary addr.vertices f=none ∧
        ∀ q,¬InitialMarkerAt addr.nodes e q) := by
  have table := turn_zero_table turn addr.nodes addr.vertices boundary zero
  rw [addr.wiring] at table
  constructor
  · intro p phase
    obtain ⟨prior,noInput⟩ := table.1 p phase
    exact ⟨prior,fun q marked => by unfold InitialMarkerAt at marked;rw [noInput] at marked;cases marked⟩
  constructor
  · exact table.2.1
  · intro phase
    obtain ⟨next,noInput⟩ := table.2.2 phase
    exact ⟨next,fun q marked => by unfold InitialMarkerAt at marked;rw [noInput] at marked;cases marked⟩

private theorem no_marker_of_none {e : Endpoint g}
    (phase : endpointAddress g addr.nodes boundary addr.vertices e=none) :
    ∀ p,¬InitialMarkerAt addr.nodes e p := by
  intro p hit
  have positive := hit.phase addr
  rw [phase] at positive
  cases positive

private theorem zero_tail {e f : Endpoint g} {tail : List (Endpoint g)}
    (zero : accessWord g (e::f::tail)=[]) :
    arrivalWord g f=[] ∧ accessWord g (f::tail)=[] :=
  List.append_eq_nil_iff.mp zero

/-- NONE is irreversible along an actual initial derivation with zero TAIL word. -/
theorem InitialLabelling.none_markers {es : List (Endpoint g)} {a b : Context}
    (labels : InitialLabelling (g:=g) es a b) (e : Endpoint g)
    (head : es.head?=some e)
    (phase : endpointAddress g addr.nodes boundary addr.vertices e=none)
    (zero : accessWord g es=[]) :
    ∀ i : Fin es.length,∀ p,¬InitialMarkerAt addr.nodes es[i] p := by
  induction labels generalizing e with
  | single x a =>
    have same : x=e := Option.some.inj head
    subst e
    intro i p
    have index : i.val=0 := by have bound : i.val<1:=i.isLt;omega
    have ordinal : i=⟨0,by simp⟩ := Fin.ext index
    subst i
    exact no_marker_of_none addr phase p
  | @cons x f tail a middle b turn after ih =>
    have same : x=e := Option.some.inj head
    subst e
    have words := zero_tail zero
    have next := (turn.initial_marker_phases addr words.1).2.2 phase
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact no_marker_of_none addr phase
    · exact ih f rfl next.1 words.2 j

/-- A SOME-to-NONE path has one marker ORDINAL, even with repeated endpoints. -/
theorem InitialLabelling.drop_marker {es : List (Endpoint g)} {a b : Context}
    (labels : InitialLabelling (g:=g) es a b) (e f : Endpoint g)
    (head : es.head?=some e) (last : es.getLast?=some f) (p : Path)
    (start : endpointAddress g addr.nodes boundary addr.vertices e=some p)
    (finish : endpointAddress g addr.nodes boundary addr.vertices f=none)
    (zero : accessWord g es=[]) :
    ∃ i : Fin es.length,InitialMarkerAt addr.nodes es[i] p ∧
      ∀ j : Fin es.length,∀ q,InitialMarkerAt addr.nodes es[j] q → j=i ∧ q=p := by
  induction labels generalizing e f p with
  | single x a =>
    have hx : x=e := Option.some.inj head
    have hy : x=f := Option.some.inj last
    subst e;subst f
    rw [start] at finish
    cases finish
  | @cons x y tail a middle b turn after ih =>
    have same : x=e := Option.some.inj head
    subst e
    have words := zero_tail zero
    have final : (y::tail).getLast?=some f := by simpa only [List.getLast?_cons_cons] using last
    cases nextPhase : endpointAddress g addr.nodes boundary addr.vertices y with
    | none =>
      have hit : InitialMarkerAt addr.nodes x p :=
        (turn.initial_marker_phases addr words.1).2.1 p start nextPhase
      have suffix := after.none_markers addr y rfl nextPhase words.2
      refine ⟨⟨0,by simp⟩,hit,?_⟩
      intro j
      refine Fin.cases ?_ (fun k => ?_) j
      · intro q marker
        have eq : q=p := Option.some.inj ((marker.phase addr).symm.trans start)
        exact ⟨rfl,eq⟩
      · intro q marker;exact False.elim (suffix k q marker)
    | some q =>
      have prior := (turn.initial_marker_phases addr words.1).1 q nextPhase
      have eq : q=p := Option.some.inj (prior.1.symm.trans start)
      subst q
      obtain ⟨i,hit,unique⟩ := ih y f rfl final p nextPhase finish words.2
      refine ⟨i.succ,hit,?_⟩
      intro j
      refine Fin.cases ?_ (fun k => ?_) j
      · intro q marker;exact False.elim (prior.2 q marker)
      · intro q marker
        obtain ⟨ordinal,address⟩ := unique k q marker
        exact ⟨congrArg Fin.succ ordinal,address⟩

/-- An actual final marked input is the unique final ORDINAL; merely having
a SOME final phase would not imply that a marker exists. -/
theorem InitialLabelling.final_marker {es : List (Endpoint g)} {a b : Context}
    (labels : InitialLabelling (g:=g) es a b) (e f : Endpoint g)
    (head : es.head?=some e) (last : es.getLast?=some f) (p q : Path)
    (start : endpointAddress g addr.nodes boundary addr.vertices e=some p)
    (marked : InitialMarkerAt addr.nodes f q) (zero : accessWord g es=[]) :
    ∃ i : Fin es.length,i.val=es.length-1 ∧ es[i]=f ∧ InitialMarkerAt addr.nodes es[i] p ∧
      ∀ j : Fin es.length,∀ r,InitialMarkerAt addr.nodes es[j] r → j=i ∧ r=p := by
  induction labels generalizing e f p q with
  | single x a =>
    have hx : x=e := Option.some.inj head
    have hy : x=f := Option.some.inj last
    subst e;subst f
    have address : q=p := Option.some.inj ((marked.phase addr).symm.trans start)
    subst q
    refine ⟨⟨0,by simp⟩,rfl,rfl,marked,?_⟩
    intro j r hit
    have ordinal : j=⟨0,by simp⟩ := by
      apply Fin.ext;change j.val=0;have bound : j.val<1:=j.isLt;omega
    subst j
    exact ⟨rfl,Option.some.inj ((hit.phase addr).symm.trans start)⟩
  | @cons x y tail a middle b turn after ih =>
    have same : x=e := Option.some.inj head
    subst e
    have words := zero_tail zero
    have final : (y::tail).getLast?=some f := by simpa only [List.getLast?_cons_cons] using last
    obtain ⟨prior,phase,relation⟩ := addr.path_predecessor g after y f rfl final q (marked.phase addr)
    rw [words.2,List.append_nil] at relation
    subst q
    have current := (turn.initial_marker_phases addr words.1).1 prior phase
    have sameAddress : prior=p := Option.some.inj (current.1.symm.trans start)
    subst prior
    obtain ⟨i,ordinal,atEnd,hit,unique⟩ := ih y f rfl final p p phase marked words.2
    refine ⟨i.succ,?_,atEnd,hit,?_⟩
    · simp only [Fin.val_succ,List.length_cons] at ordinal ⊢
      omega
    · intro j
      refine Fin.cases ?_ (fun k => ?_) j
      · intro r marker;exact False.elim (current.2 r marker)
      · intro r marker
        obtain ⟨index,address⟩ := unique k r marker
        exact ⟨congrArg Fin.succ index,address⟩
end

#print axioms InitialTurn.output_no_initial_input
#print axioms InitialLabelling.suffix
#print axioms InitialLabelling.no_initial_inputs
#print axioms InitialMarkerAt.phase
#print axioms InitialTurn.initial_marker_phases
#print axioms InitialLabelling.none_markers
#print axioms InitialLabelling.drop_marker
#print axioms InitialLabelling.final_marker
end Lamping.AG
