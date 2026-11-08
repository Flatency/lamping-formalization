import Lamping.Lamping.PairedStreamAssignments
import Lamping.Lamping.LocalTransport
namespace Lamping.AG
open Graph
private theorem no_binding {i kind p q a b}
    (rule : Traversal i kind p q a b) (sort : kind=.op .lam) (role : HEq p lamBind) : False := by
  subst kind
  exact rule.no_binding.1 (eq_of_heq role)
section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable {g : Net signature N B W}

private theorem first_ordinary {e f : Endpoint g} {tail : List (Endpoint g)} {a b middle : Context} {count : Nat}
    (path : BetaDetourBlocks g (e::f::tail) a b count)
    (ordinary : LabelledTurn g (g.wire e) f a middle) :
    BetaDetourBlocks g (f::tail) middle b count := by
  generalize eqs : (e::f::tail : List (Endpoint g))=raw at path
  cases path with
  | single => cases eqs
  | ordinary turn rest =>
    cases eqs
    have same := turn.output_unique ordinary
    subst middle
    exact rest
  | backward edge x arrival head rest =>
    have same : e=x := (List.cons.inj eqs).1
    subst x
    rw [arrival] at ordinary
    obtain ⟨q,_leaving,rule⟩ := ordinary.from_node edge.lam edge.lamBind rfl
    exact False.elim (no_binding rule (congrArg Label.sort edge.lamLabel) edge.lamBind_role)

/-- Remove an existing ordinary prefix from an existing paired stream.
The shared segment is kept in the suffix once; no backward block can have
been consumed, since its first binding turn is never an ordinary turn. -/
theorem BetaDetourBlocks.ordinary_suffix
    {pre post : List (Endpoint g)} {e : Endpoint g} {a middle b : Context} {count : Nat}
    (path : BetaDetourBlocks g (pre++e::post) a b count)
    (before : Labelling g (pre++[e]) a middle) :
    BetaDetourBlocks g (e::post) middle b count := by
  induction pre generalizing a with
  | nil => cases before with | single => exact path
  | cons x pre ih =>
    cases pre with
    | nil =>
      cases before with
      | cons turn rest =>
        cases rest with
        | single => exact first_ordinary path turn
    | cons y pre =>
      cases before with
      | cons turn rest =>
        have after := first_ordinary path turn
        exact ih after rest
end
end Lamping.AG

