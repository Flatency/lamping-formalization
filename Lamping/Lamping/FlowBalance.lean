import Lamping.Lamping.InitialFlow
namespace Lamping.AG
open Graph Lambda

/-- Incidence polarity. Control bases are freely chosen per physical node,
not fixed by the control's rewrite index or by its printed direction. -/
def flowPort (kind : Kind) (base : Bool) : Port kind → Bool :=
  match kind with
  | .op .app => fun p => match p with | .inl _ => true | .inr b => b
  | .op .lam => fun p => match p with | .inl _ => false | .inr b => b
  | .op .fan => fun p => match p with | .inl _ => base | .inr _ => !base
  | .op .cro => fun p => match p with | .inl _ => base | .inr _ => !base
  | .op .bra => fun p => match p with | .inl _ => base | .inr _ => !base
  | .garbage => fun _ => base

section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable (g : Net signature N B W)

def flowEndpoint (nodes : N → Bool) (boundary : B → Bool) (vertices : W → Bool) : Endpoint g → Bool
  | .inl ⟨n,p⟩ => flowPort (g.label n).sort (nodes n) p
  | .inr (.inl b) => boundary b
  | .inr (.inr (w,d)) => if d then !(vertices w) else vertices w

/-- A purely structural witness: wires join opposite polarities. It carries no
path, matching, reachability, or soundness assertion. -/
structure FlowBalance (boundary : B → Bool) where
  nodes : N → Bool
  vertices : W → Bool
  wiring : ∀ e, flowEndpoint g nodes boundary vertices (g.wire e) =
    !(flowEndpoint g nodes boundary vertices e)
end

theorem Passage.flow_flip {i k p q a b} (h : Passage i k p q a b) (base : Bool) :
    flowPort k base q = !(flowPort k base p) := by
  cases h <;> cases base <;> rfl

theorem Traversal.flow_flip {i k p q a b} (h : Traversal i k p q a b) (base : Bool) :
    flowPort k base q = !(flowPort k base p) := by
  cases h with
  | direct h => exact h.flow_flip base
  | inverse h => rw [h.flow_flip base]; simp

section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable {g : Net signature N B W} {boundary : B → Bool}

theorem LabelledTurn.flow_flip {e f : Endpoint g} {a b : Context}
    (h : LabelledTurn g e f a b) (nodes : N → Bool) (vertices : W → Bool) :
    flowEndpoint g nodes boundary vertices f = !(flowEndpoint g nodes boundary vertices e) := by
  cases h with
  | node n p q rule => exact rule.flow_flip (nodes n)
  | transparent w d a => cases d <;> simp [flowEndpoint]

/-- Every segment occurrence in an actual labelled root path has positive
departure polarity. No forward-path or semantic invariant is assumed. -/
theorem Labelling.positive_departures {es : List (Endpoint g)} {a b : Context}
    (h : Labelling g es a b) (flow : FlowBalance g boundary)
    (first : ∀ e, es.head? = some e → flowEndpoint g flow.nodes boundary flow.vertices e = true) :
    ∀ e ∈ es, flowEndpoint g flow.nodes boundary flow.vertices e = true := by
  induction h with
  | single e a =>
    intro x hx
    simp only [List.mem_singleton] at hx
    subst x
    exact first e rfl
  | @cons e f es a b c turn tail ih =>
    have pe := first e rfl
    have pf : flowEndpoint g flow.nodes boundary flow.vertices f = true := by
      rw [turn.flow_flip flow.nodes flow.vertices, flow.wiring e, pe]
      rfl
    have rest := ih (by
      intro x hx
      simp only [List.head?_cons, Option.some.injEq] at hx
      subst x
      exact pf)
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact pe
    · exact rest x hx

theorem Labelling.root_positive_departures {es : List (Endpoint g)} {a b : Context}
    (h : Labelling g es a b) (flow : FlowBalance g boundary) (root : B)
    (rooted : es.head? = some (.inr (.inl root))) (rootPolarity : boundary root = true) :
    ∀ e ∈ es, flowEndpoint g flow.nodes boundary flow.vertices e = true := by
  apply h.positive_departures flow
  intro e he
  rw [rooted] at he
  cases Option.some.inj he
  exact rootPolarity
end

theorem flowPort_initial (k : Kind) (p : Port k) :
    flowPort k true p = initialPortPolarity k p := by
  cases k with
  | garbage => rfl
  | op o => cases o <;> cases p <;> rfl

/-- The previous initial orientation is exactly the all-true-node instance of
the structural polarity invariant, including the actual gluing vertices. -/
theorem flowEndpoint_initial {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
    (g : Net signature N B W) (bp : B → Bool) (vp : W → Bool) (e : Endpoint g) :
    flowEndpoint g (fun _ => true) bp vp e = endPolarity bp vp e := by
  rcases e with ⟨n,p⟩ | (b | ⟨w,d⟩)
  · exact flowPort_initial _ _
  · rfl
  · rfl

theorem encode_flowBalance (t : Term) (n : Nat) :
    Nonempty (FlowBalance (encode n t).net initialBoundaryPolarity) := by
  obtain ⟨vertices,flow⟩ := encode_flow t n
  refine ⟨⟨fun _ => true, vertices, ?_⟩⟩
  intro e
  simpa only [flowEndpoint_initial] using flow e
end Lamping.AG
