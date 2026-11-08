import Lamping.Lamping.GraphFlowPreservation
namespace Lamping.AG
open Graph Lambda

/-- At proper nodes a negative arriving polarity forces the printed forward
direction; at controls both genuine traversal directions remain allowed. -/
theorem Traversal.forward_of_flow {i k p q a b} (rule : Traversal i k p q a b)
    (base : Bool) (incoming : flowPort k base p=false) : ForwardPorts k p q := by
  cases rule with
  | direct passage => exact passage.forward_ports
  | inverse passage =>
    cases passage <;> simp_all [flowPort,ForwardPorts,AG.appArg,AG.lamBody]

section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable {g : Net signature N B W} {boundary : B → Bool}

theorem LabelledTurn.prepend_forward_of_flow {e f : Endpoint g} {a b : Context}
    (turn : LabelledTurn g e f a b) (flow : FlowBalance g boundary)
    (incoming : flowEndpoint g flow.nodes boundary flow.vertices e=false)
    (x : Endpoint g) (arrives : g.wire x=e) {tail : List (Endpoint g)}
    (rest : Forward g (f::tail)) : Forward g (x::f::tail) := by
  cases turn with
  | node n p q rule => exact .node n p q arrives rfl (rule.forward_of_flow (flow.nodes n) incoming) rest
  | transparent w d a => exact .transparent w d arrives rfl rest

/-- Structural flow derives ordinary forward direction for actual labels.
It does not assert that an arbitrary unlabelled walk is proper. -/
theorem Labelling.forward_of_flow {es : List (Endpoint g)} {a b : Context}
    (labels : Labelling g es a b) (flow : FlowBalance g boundary)
    (first : ∀ e, es.head?=some e → flowEndpoint g flow.nodes boundary flow.vertices e=true) :
    Forward g es := by
  induction labels with
  | single e a => exact .single e
  | @cons e f es a b c turn rest ih =>
    have pe := first e rfl
    have incoming : flowEndpoint g flow.nodes boundary flow.vertices (g.wire e)=false := by
      rw [flow.wiring,pe]
      rfl
    have pf : flowEndpoint g flow.nodes boundary flow.vertices f=true := by
      rw [turn.flow_flip flow.nodes flow.vertices,incoming]
      rfl
    apply turn.prepend_forward_of_flow flow incoming e rfl
    apply ih
    intro x head
    simp only [List.head?_cons,Option.some.injEq] at head
    subst x
    exact pf

theorem Labelling.root_forward_of_flow {es : List (Endpoint g)} {a b : Context}
    (labels : Labelling g es a b) (flow : FlowBalance g boundary) (root : B)
    (rooted : es.head?=some (.inr (.inl root))) (rootPolarity : boundary root=true) :
    Forward g es := by
  apply labels.forward_of_flow flow
  intro e head
  rw [rooted] at head
  cases Option.some.inj head
  exact rootPolarity
end

section
variable {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K → Label signature} {i : Nat}
variable (site : PathSite (.beta i) kept (B:=B) (W:=W) (V:=V))
variable {boundary : B → Bool} (old : FlowBalance site.net boundary) (root : B)
include old

/-- The erased beta wire cannot be entered through its old application argument
frontier by a genuine rooted labelled path. This is an actual occurrence
exclusion, rather than a direction premise on a proposed ancestor. -/
theorem PathSite.beta_no_argument_entry {es : List (Endpoint site.reduce)} {a b : Context}
    (labels : Labelling site.reduce es a b)
    (rooted : es.head? = some (.inr (.inl root))) (rootPolarity : boundary root = true) :
    (.inr (.inr (.inr (.inl true),true)) : Endpoint site.reduce) ∉ es := by
  obtain ⟨changed,glue⟩ := site.reduce_flowBalance_glue old
  intro member
  have positive := labels.root_positive_departures changed root rooted rootPolarity _ member
  change (!(changed.vertices (.inr (.inl true)))) = true at positive
  rw [glue] at positive
  change (!(!(!true))) = true at positive
  cases positive

/-- The other forbidden beta excursion would enter the RHS through the old
lambda body, reversing the context-to-body shortcut. -/
theorem PathSite.beta_no_body_entry {es : List (Endpoint site.reduce)} {a b : Context}
    (labels : Labelling site.reduce es a b)
    (rooted : es.head? = some (.inr (.inl root))) (rootPolarity : boundary root = true) :
    (.inr (.inr (.inr (.inr true),true)) : Endpoint site.reduce) ∉ es := by
  obtain ⟨changed,glue⟩ := site.reduce_flowBalance_glue old
  intro member
  have positive := labels.root_positive_departures changed root rooted rootPolarity _ member
  change (!(changed.vertices (.inr (.inr true)))) = true at positive
  rw [glue] at positive
  change (!(!(!true))) = true at positive
  cases positive
end

/-- Reachable labelled root paths have positive departure polarity with respect
to a witness constructed along the actual finite rewrite trace. -/
theorem initial_trace_positive_departures (t : Term) (target : ActualNet (Boundary t))
    (schemas : List Schema) (trace : GraphTrace (ActualNet.initial t) target schemas)
    {es : List (Endpoint target.net)} {a b : Context} (labels : Labelling target.net es a b)
    (rooted : es.head? = some (.inr (.inl (.inl ())))) :
    ∃ flow : FlowBalance target.net initialBoundaryPolarity,
      ∀ e ∈ es, flowEndpoint target.net flow.nodes initialBoundaryPolarity flow.vertices e = true := by
  obtain ⟨flow⟩ := initial_trace_flowBalance t target schemas trace
  exact ⟨flow,labels.root_positive_departures flow (.inl ()) rooted rfl⟩
end Lamping.AG
