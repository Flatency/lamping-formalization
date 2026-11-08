import Lamping.Lamping.ControlLeafPrefixes
namespace Lamping.AG
open Graph

theorem fanRight_copied_aux_prefix (f : Op) (i j : Nat) (branch : Bool) (q : Aux f)
    (entry : Bool⊕Aux f) (es : List (Endpoint (fanRight f i j))) (a b : Context)
    (labels : Labelling (fanRight f i j) es a b)
    (start : es.head?=some (.inr (.inl entry)))
    (finish : es.getLast?=some ((fanRight f i j).wire (.inl ⟨.inl branch,.inr q⟩))) :
    entry=.inr q ∧es=[.inr (.inl (.inr q)),.inl ⟨.inr q,.inr branch⟩] ∧
      Traversal i (.op .fan) (.inl ()) (.inr branch) a b :=
  labels.control_leaf_prefix entry (.inr q) start (.inr q) .fan i rfl (Or.inl rfl)
    (.inl ()) (.inr branch) branch HEq.rfl HEq.rfl rfl finish

theorem unaryRight_copied_aux_prefix (c f : Op) (single : Bij Unit (Aux c))
    (control : c=.fan ∨c=.cro ∨c=.bra) (i k : Nat) (q : Aux f)
    (entry : Unit⊕Aux f) (es : List (Endpoint (unaryRightCore c f single i k))) (a b : Context)
    (labels : Labelling (unaryRightCore c f single i k) es a b)
    (start : es.head?=some (.inr (.inl entry)))
    (finish : es.getLast?=some ((unaryRightCore c f single i k).wire (.inl ⟨.inl (),.inr q⟩))) :
    entry=.inr q ∧es=[.inr (.inl (.inr q)),.inl ⟨.inr q,.inr (single ())⟩] ∧
      Traversal i (.op c) (.inl ()) (.inr (single ())) a b :=
  labels.control_leaf_prefix entry (.inr q) start (.inr q) c i rfl control
    (.inl ()) (.inr (single ())) (single ()) HEq.rfl HEq.rfl rfl finish

/-- A copied application's context endpoint has only this real two-segment
RHS prefix. The final context is related by the inverse low fan passage;
it is not silently identified with the frontier context. -/
theorem fanRight_app_context_prefix (i j : Nat) (branch : Bool) (entry : Bool⊕Bool)
    (es : List (Endpoint (fanRight .app i j))) (a b : Context)
    (labels : Labelling (fanRight .app i j) es a b)
    (start : es.head?=some (.inr (.inl entry)))
    (finish : es.getLast?=some ((fanRight .app i j).wire (.inl ⟨.inl branch,appCtx⟩))) :
    entry=.inr false ∧
      es=[.inr (.inl (.inr false)),.inl ⟨.inr false,.inr branch⟩] ∧
      Traversal i (.op .fan) (.inl ()) (.inr branch) a b :=
  labels.control_leaf_prefix entry (.inr false) start (.inr false) .fan i rfl (Or.inl rfl)
    (.inl ()) (.inr branch) branch HEq.rfl HEq.rfl rfl finish

theorem unaryRight_app_context_prefix (c : Op) (single : Bij Unit (Aux c))
    (control : c=.fan ∨c=.cro ∨c=.bra) (i k : Nat) (entry : Unit⊕Bool)
    (es : List (Endpoint (unaryRightCore c .app single i k))) (a b : Context)
    (labels : Labelling (unaryRightCore c .app single i k) es a b)
    (start : es.head?=some (.inr (.inl entry)))
    (finish : es.getLast?=some ((unaryRightCore c .app single i k).wire (.inl ⟨.inl (),appCtx⟩))) :
    entry=.inr false ∧
      es=[.inr (.inl (.inr false)),.inl ⟨.inr false,.inr (single ())⟩] ∧
      Traversal i (.op c) (.inl ()) (.inr (single ())) a b :=
  labels.control_leaf_prefix entry (.inr false) start (.inr false) c i rfl control
    (.inl ()) (.inr (single ())) (single ()) HEq.rfl HEq.rfl rfl finish

/-- The copied lambda's context is wired directly to its active frontier.
A prefix arriving there has no RHS turn at all. -/
theorem fanRight_lam_context_prefix (i j : Nat) (branch : Bool) (entry : Bool⊕Bool)
    (es : List (Endpoint (fanRight .lam i j))) (a b : Context)
    (labels : Labelling (fanRight .lam i j) es a b)
    (start : es.head?=some (.inr (.inl entry)))
    (finish : es.getLast?=some ((fanRight .lam i j).wire (.inl ⟨.inl branch,.inl ()⟩))) :
    entry=.inl branch ∧es=[.inr (.inl (.inl branch))] ∧a=b := by
  obtain ⟨shape,same⟩ := labels.boundary_last (.inl branch) finish
  rw [shape] at start
  exact ⟨(Sum.inl.inj (Sum.inr.inj (Option.some.inj start))).symm,shape,same⟩

theorem unaryRight_lam_context_prefix (c : Op) (single : Bij Unit (Aux c))
    (i k : Nat) (entry : Unit⊕Bool)
    (es : List (Endpoint (unaryRightCore c .lam single i k))) (a b : Context)
    (labels : Labelling (unaryRightCore c .lam single i k) es a b)
    (start : es.head?=some (.inr (.inl entry)))
    (finish : es.getLast?=some ((unaryRightCore c .lam single i k).wire (.inl ⟨.inl (),.inl ()⟩))) :
    entry=.inl () ∧es=[.inr (.inl (.inl ()))] ∧a=b := by
  obtain ⟨shape,same⟩ := labels.boundary_last (.inl ()) finish
  rw [shape] at start
  exact ⟨(Sum.inl.inj (Sum.inr.inj (Option.some.inj start))).symm,shape,same⟩
end Lamping.AG

