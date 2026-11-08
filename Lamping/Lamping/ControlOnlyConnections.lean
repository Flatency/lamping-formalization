import Lamping.Lamping.MatchingRedexConnection
namespace Lamping.AG
open Graph Lambda

private def emitted : (kind : Kind) → Port kind → Path
  | .op .app,.inl () => [.fn]
  | .op .app,.inr true => [.arg]
  | .op .lam,.inr true => [.body]
  | _,_ => []

private theorem zero_departure_control (kind : Kind) (p q : Port kind)
    (direction : ForwardPorts kind p q) (zero : emitted kind q=[]) :
    ∃ op,kind=.op op ∧(op=.fan ∨op=.cro ∨op=.bra) := by
  cases kind with
  | garbage => exact False.elim direction
  | op op =>
    cases op with
    | app =>
      rcases direction.2 with same |same <;> rw [same] at zero <;> cases zero
    | lam => rw [direction.2] at zero; cases zero
    | fan => exact ⟨.fan,rfl,Or.inl rfl⟩
    | cro => exact ⟨.cro,rfl,Or.inr (Or.inl rfl)⟩
    | bra => exact ⟨.bra,rfl,Or.inr (Or.inr rfl)⟩

section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable {g : Net signature N B W}

/-- One actual step either crosses a transparent W vertex or a control node.
This predicate records physical incidence; it is not a rewrite certificate. -/
def ControlOnlyTurn (e f : Endpoint g) : Prop :=
  (∃ w d,g.wire e=.inr (.inr (w,d)) ∧f=.inr (.inr (w,!d))) ∨
  ∃ (node : N) (p q : Port (g.label node).sort) (op : Op),
    (g.label node).sort=.op op ∧(op=.fan ∨op=.cro ∨op=.bra) ∧
    g.wire e=.inl ⟨node,p⟩ ∧f=.inl ⟨node,q⟩

/-- Zero syntax word on an existing ordinary forward path excludes all
proper-node turns. The first departure is retained and is never declared
token-free merely because accessWord skips it. -/
theorem Forward.empty_word_control_only {es : List (Endpoint g)}
    (forward : Forward g es) (word : accessWord g es=[]) :
    ∀ e f,(e,f)∈es.zip es.tail →ControlOnlyTurn (g:=g) e f := by
  induction forward with
  | single e => intro x y pair; simp at pair
  | @node e f es node p q arrives leaves direction after ih =>
    have zero : arrivalWord g f=[] ∧es.flatMap (arrivalWord g)=[] :=
      List.append_eq_nil_iff.mp word
    have token : emitted (g.label node).sort q=[] := by rw [leaves] at zero; exact zero.1
    obtain ⟨op,sort,control⟩ := zero_departure_control _ p q direction token
    have remaining := ih zero.2
    intro x y pair
    rcases List.mem_cons.mp pair with same |rest
    · cases same
      exact Or.inr ⟨node,p,q,op,sort,control,arrives,leaves⟩
    · exact remaining x y rest
  | @transparent e f es w d arrives leaves after ih =>
    have zero : arrivalWord g f=[] ∧es.flatMap (arrivalWord g)=[] :=
      List.append_eq_nil_iff.mp word
    have remaining := ih zero.2
    intro x y pair
    rcases List.mem_cons.mp pair with same |rest
    · cases same
      exact Or.inl ⟨w,d,arrives,leaves⟩
    · exact remaining x y rest

theorem RedexConnection.control_only (connection : RedexConnection g) :
    ∀ e f,(e,f)∈connection.edges.zip connection.edges.tail →ControlOnlyTurn (g:=g) e f :=
  connection.proper.2.empty_word_control_only connection.emptyWord
end
end Lamping.AG
