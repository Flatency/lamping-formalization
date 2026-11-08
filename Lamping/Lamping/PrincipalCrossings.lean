import Lamping.Lamping.PathSitePrincipalRoutes
namespace Lamping.AG
open Graph
section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable (g : Net signature N B W)

private theorem append_node_labels {es : List (Endpoint g)} (labels : Labelling g es a b)
    (last : Endpoint g) (finish : es.getLast?=some last)
    (node : N) (p q : Port (g.label node).sort) (arrival : g.wire last=.inl ⟨node,p⟩)
    (rule : Traversal (g.label node).index (g.label node).sort p q b d) :
    Labelling g (es++[.inl ⟨node,q⟩]) a d := by
  induction labels with
  | single e a =>
    have same : e=last := Option.some.inj finish
    subst e
    apply Labelling.cons
    · rw [arrival]
      exact .node node p q rule
    · exact .single _ _
  | cons turn tail ih =>
    exact .cons turn (ih (by simpa only [List.getLast?_cons_cons] using finish) rule)

private theorem append_node_forward {es : List (Endpoint g)} (path : Forward g es)
    (last : Endpoint g) (finish : es.getLast?=some last)
    (node : N) (p q : Port (g.label node).sort) (arrival : g.wire last=.inl ⟨node,p⟩)
    (direction : ForwardPorts (g.label node).sort p q) : Forward g (es++[.inl ⟨node,q⟩]) := by
  induction path with
  | single e =>
    have same : e=last := Option.some.inj finish
    subst e
    exact .node node p q arrival rfl direction (.single _)
  | node n p q arrives leaves dir rest ih =>
    exact .node n p q arrives leaves dir (ih (by simpa only [List.getLast?_cons_cons] using finish))
  | transparent w d arrives leaves rest ih =>
    exact .transparent w d arrives leaves (ih (by simpa only [List.getLast?_cons_cons] using finish))

/-- Labels alone permit either genuine direction at a proper node. -/
theorem principal_crossing_labels (left right : N)
    (entry primary : Port (g.label left).sort) (other exit : Port (g.label right).sort)
    (es : List (Endpoint g))
    (start : es.head?=some (.inl ⟨left,primary⟩))
    (finish : es.getLast?=some (g.wire (.inl ⟨right,other⟩)))
    (transparent : ∀ e f,(e,f)∈es.zip es.tail →
      ∃ w d,g.wire e=.inr (.inr (w,d)) ∧f=.inr (.inr (w,!d)))
    (first : Traversal (g.label left).index (g.label left).sort entry primary a middle)
    (second : Traversal (g.label right).index (g.label right).sort other exit middle b) :
    Labelling g (g.wire (.inl ⟨left,entry⟩)::(es++[.inl ⟨right,exit⟩])) a b := by
  have nonempty : es≠[] := by intro empty; rw [empty] at start; cases start
  have labels := append_node_labels g (transparent_route_labelling g es nonempty transparent middle)
    _ finish right other exit (by rw [Pairing.involutive]) second
  cases es with
  | nil => exact False.elim (nonempty rfl)
  | cons e tail =>
    have same : e=.inl ⟨left,primary⟩ := Option.some.inj start
    subst e
    apply Labelling.cons
    · rw [Pairing.involutive]
      exact .node left entry primary first
    · exact labels

/-- Splice two actual node passages around a physical transparent principal
route. Each directed segment is retained; no local correctness certificate
or assumption about path simplicity is required. -/
theorem principal_crossing (left right : N)
    (entry primary : Port (g.label left).sort) (other exit : Port (g.label right).sort)
    (es : List (Endpoint g))
    (start : es.head?=some (.inl ⟨left,primary⟩))
    (finish : es.getLast?=some (g.wire (.inl ⟨right,other⟩)))
    (transparent : ∀ e f,(e,f)∈es.zip es.tail →
      ∃ w d,g.wire e=.inr (.inr (w,d)) ∧f=.inr (.inr (w,!d)))
    (first : Traversal (g.label left).index (g.label left).sort entry primary a middle)
    (second : Traversal (g.label right).index (g.label right).sort other exit middle b)
    (firstDir : ForwardPorts (g.label left).sort entry primary)
    (secondDir : ForwardPorts (g.label right).sort other exit) :
    Labelling g (g.wire (.inl ⟨left,entry⟩)::(es++[.inl ⟨right,exit⟩])) a b ∧
    Forward g (g.wire (.inl ⟨left,entry⟩)::(es++[.inl ⟨right,exit⟩])) := by
  have nonempty : es≠[] := by intro empty; rw [empty] at start; cases start
  have labels := append_node_labels g (transparent_route_labelling g es nonempty transparent middle)
    _ finish right other exit (by rw [Pairing.involutive]) second
  have fw := append_node_forward g (transparent_route_forward g es nonempty transparent)
    _ finish right other exit (by rw [Pairing.involutive]) secondDir
  cases es with
  | nil => exact False.elim (nonempty rfl)
  | cons e tail =>
    have same : e=.inl ⟨left,primary⟩ := Option.some.inj start
    subst e
    constructor
    · apply Labelling.cons
      · rw [Pairing.involutive]
        exact .node left entry primary first
      · exact labels
    · exact .node left entry primary (by rw [Pairing.involutive]) rfl firstDir fw
end
end Lamping.AG
