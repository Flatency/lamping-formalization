import Lamping.Lamping.PrincipalCorridorExtraction
namespace Lamping.AG
open Graph

private theorem last_split {A : Type} (xs : List A) (nonempty : xs≠[]) :
    ∃ initial last,xs=initial++[last] := by
  induction xs with
  | nil => exact False.elim (nonempty rfl)
  | cons x xs ih =>
    cases xs with
    | nil => exact ⟨[],x,rfl⟩
    | cons y ys =>
      obtain ⟨initial,last,split⟩ := ih (by simp)
      exact ⟨x::initial,last,congrArg (List.cons x) split⟩

private theorem pair_in_append {A : Type} (before : List A) (e f : A) (after : List A) :
    (e,f)∈(before++e::f::after).zip (before++e::f::after).tail := by
  induction before with
  | nil => simp
  | cons x before ih =>
    cases before with
    | nil => exact List.mem_cons_of_mem _ ih
    | cons y before => exact List.mem_cons_of_mem _ ih

section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable {g : Net signature N B W}

def IsControlNode (node : N) : Prop :=
  ∃ op,(g.label node).sort=.op op ∧(op=.fan ∨op=.cro ∨op=.bra)

theorem ControlOnlyTurn.departure_control {e : Endpoint g}
    (node : N) (p : Port (g.label node).sort)
    (turn : ControlOnlyTurn (g:=g) e (.inl ⟨node,p⟩)) : IsControlNode (g:=g) node := by
  rcases turn with ⟨w,d,_arrival,leaves⟩ |⟨other,q,r,op,sort,control,_arrival,leaves⟩
  · cases leaves
  · have same : node=other := congrArg Sigma.fst (Sum.inl.inj leaves)
    subst other
    exact ⟨op,sort,control⟩

theorem ControlOnlyTurn.arrival_control {e f : Endpoint g}
    (node : N) (p : Port (g.label node).sort)
    (arrival : g.wire e=.inl ⟨node,p⟩) (turn : ControlOnlyTurn (g:=g) e f) :
    IsControlNode (g:=g) node := by
  rcases turn with ⟨w,d,arrives,_leaves⟩ |⟨other,q,r,op,sort,control,arrives,_leaves⟩
  · rw [arrival] at arrives; cases arrives
  · have same : other=node := congrArg Sigma.fst (Sum.inl.inj (arrives.symm.trans arrival))
    subst other
    exact ⟨op,sort,control⟩

theorem control_corridor_left {es : List (Endpoint g)}
    (only : ∀ e f,(e,f)∈es.zip es.tail →ControlOnlyTurn (g:=g) e f)
    (route : TransparentCorridor g) (before after : List (Endpoint g))
    (split : es=(before++route.edges)++after) (nonempty : before≠[]) :
    IsControlNode (g:=g) route.first.1 := by
  obtain ⟨initial,previous,beforeSplit⟩ := last_split before nonempty
  obtain ⟨rest,routeSplit⟩ := List.head?_eq_some_iff.mp route.start
  have pair : (previous,.inl route.first)∈es.zip es.tail := by
    rw [split,beforeSplit,routeSplit]
    simpa only [List.append_assoc,List.singleton_append,List.cons_append] using
      pair_in_append initial previous (.inl route.first) (rest++after)
  exact (only _ _ pair).departure_control route.first.1 route.first.2

theorem control_corridor_right {es : List (Endpoint g)}
    (only : ∀ e f,(e,f)∈es.zip es.tail →ControlOnlyTurn (g:=g) e f)
    (route : TransparentCorridor g) (before after : List (Endpoint g))
    (split : es=(before++route.edges)++after) (nonempty : after≠[]) :
    IsControlNode (g:=g) route.last.1 := by
  cases after with
  | nil => exact False.elim (nonempty rfl)
  | cons next remaining =>
    obtain ⟨initial,routeSplit⟩ := List.getLast?_eq_some_iff.mp route.finish
    have pair : (g.wire (.inl route.last),next)∈es.zip es.tail := by
      rw [split,routeSplit]
      simpa only [List.append_assoc,List.singleton_append] using
        pair_in_append (before++initial) (g.wire (.inl route.last)) next remaining
    exact (only _ _ pair).arrival_control route.last.1 route.last.2 (Pairing.involutive _ _)

/-- Endpoint kinds of this selected literal redex corridor: only the whole
application/lambda endpoints can be proper; internal boundaries are controls.
Kinds alone do not assert compatible marker values or a rewrite schema. -/
theorem RedexConnection.corridor_endpoint_kinds (connection : RedexConnection g)
    (route : TransparentCorridor g) (before after : List (Endpoint g))
    (split : connection.edges=(before++route.edges)++after) :
    (route.first=⟨connection.app,connection.appPort⟩ ∨IsControlNode (g:=g) route.first.1) ∧
    (route.last=⟨connection.lam,connection.lamPort⟩ ∨IsControlNode (g:=g) route.last.1) := by
  constructor
  · by_cases empty : before=[]
    · have start := connection.start
      rw [split,empty,List.nil_append,List.head?_append,route.start,Option.some_or] at start
      exact Or.inl (Sum.inl.inj (Option.some.inj start))
    · exact Or.inr (control_corridor_left connection.control_only route before after split empty)
  · by_cases empty : after=[]
    · have finish := connection.finish
      rw [split,empty,List.append_nil,List.getLast?_append,route.finish,Option.some_or] at finish
      have same := congrArg g.wire.mate (Option.some.inj finish)
      simp only [Pairing.involutive] at same
      exact Or.inl (Sum.inl.inj same)
    · exact Or.inr (control_corridor_right connection.control_only route before after split empty)
end
end Lamping.AG
