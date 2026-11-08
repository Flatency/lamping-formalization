import Lamping.Lamping.GraphBalancePreservation
namespace Lamping.AG
open Graph Lambda
private theorem principal_depth (actual : Label signature) (op : Op) (index : Nat) (base : Int)
    (p : Port actual.sort) (lab : actual=label op index) (proper : op=.app ∨op=.lam)
    (principal : HEq p (Sum.inl () : Port (.op op))) :
    portDepth actual.index actual.sort base p=(index : Int) := by
  subst actual
  have same : p=.inl () := eq_of_heq principal
  subst p
  rcases proper with same | same <;> subst op <;> rfl
section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable {g : Net signature N B W} {boundary : B → Int}

/-- Depth is constant along a real wire route with arbitrary transparent
subdivisions. No labelled-path existence or bound on its length is assumed. -/
theorem LevelBalance.transparent_route_depth (balance : LevelBalance g boundary)
    (es : List (Endpoint g)) (first last : Endpoint g)
    (head : es.head?=some first) (finish : es.getLast?=some last)
    (transparent : ∀ e f,(e,f)∈es.zip es.tail →
      ∃ w d,g.wire e=.inr (.inr (w,d)) ∧f=.inr (.inr (w,!d))) :
    endpointDepth g balance.nodes boundary balance.vertices first=
      endpointDepth g balance.nodes boundary balance.vertices (g.wire last) := by
  induction es generalizing first with
  | nil => cases head
  | cons e tail ih =>
    have same : e=first := Option.some.inj head
    subst first
    cases tail with
    | nil =>
      have same : e=last := Option.some.inj finish
      subst last
      exact (balance.wiring e).symm
    | cons f tail =>
      obtain ⟨w,d,arrival,departure⟩ := transparent e f (by simp)
      have step : endpointDepth g balance.nodes boundary balance.vertices e=
          endpointDepth g balance.nodes boundary balance.vertices f := by
        rw [←balance.wiring e,arrival,departure]
        rfl
      apply step.trans
      apply ih f rfl (by simpa only [List.getLast?_cons_cons] using finish)
      intro x y member
      exact transparent x y (by simp only [List.tail_cons,List.zip_cons_cons,List.mem_cons]; exact Or.inr member)

theorem LevelBalance.proper_principal_route_indices (balance : LevelBalance g boundary)
    (es : List (Endpoint g)) (left right : N) (p : Port (g.label left).sort) (q : Port (g.label right).sort)
    (lop rop : Op) (li ri : Nat) (leftLabel : g.label left=label lop li) (rightLabel : g.label right=label rop ri)
    (leftProper : lop=.app ∨lop=.lam) (rightProper : rop=.app ∨rop=.lam)
    (leftPrincipal : HEq p (Sum.inl () : Port (.op lop))) (rightPrincipal : HEq q (Sum.inl () : Port (.op rop)))
    (head : es.head?=some (.inl ⟨left,p⟩)) (finish : es.getLast?=some (g.wire (.inl ⟨right,q⟩)))
    (transparent : ∀ e f,(e,f)∈es.zip es.tail →
      ∃ w d,g.wire e=.inr (.inr (w,d)) ∧f=.inr (.inr (w,!d))) : li=ri := by
  have same := balance.transparent_route_depth es _ _ head finish transparent
  rw [Pairing.involutive] at same
  have leftDepth : endpointDepth g balance.nodes boundary balance.vertices (.inl ⟨left,p⟩)=(li : Int) :=
    principal_depth _ lop li (balance.nodes left) p leftLabel leftProper leftPrincipal
  have rightDepth : endpointDepth g balance.nodes boundary balance.vertices (.inl ⟨right,q⟩)=(ri : Int) :=
    principal_depth _ rop ri (balance.nodes right) q rightLabel rightProper rightPrincipal
  rw [leftDepth,rightDepth] at same
  omega
end

/-- The second obstruction of AG3.5.24 is absent from actual reachable
graphs, including a principal wire subdivided by arbitrary transparent W. -/
theorem reachable_proper_principal_indices (t : Term) (target : ActualNet (Boundary t))
    (reachable : GraphReachable (ActualNet.initial t) target)
    (es : List (Endpoint target.net)) (left right : target.Node)
    (p : Port (target.net.label left).sort) (q : Port (target.net.label right).sort)
    (lop rop : Op) (li ri : Nat)
    (leftLabel : target.net.label left=label lop li) (rightLabel : target.net.label right=label rop ri)
    (leftProper : lop=.app ∨lop=.lam) (rightProper : rop=.app ∨rop=.lam)
    (leftPrincipal : HEq p (Sum.inl () : Port (.op lop))) (rightPrincipal : HEq q (Sum.inl () : Port (.op rop)))
    (head : es.head?=some (.inl ⟨left,p⟩))
    (finish : es.getLast?=some (target.net.wire (.inl ⟨right,q⟩)))
    (transparent : ∀ e f,(e,f)∈es.zip es.tail →
      ∃ w d,target.net.wire e=.inr (.inr (w,d)) ∧f=.inr (.inr (w,!d))) : li=ri := by
  obtain ⟨schemas,trace⟩ := reachable
  obtain ⟨balance⟩ := initial_trace_balance t target schemas trace
  exact balance.proper_principal_route_indices es left right p q lop rop li ri leftLabel rightLabel
    leftProper rightProper leftPrincipal rightPrincipal head finish transparent
end Lamping.AG
