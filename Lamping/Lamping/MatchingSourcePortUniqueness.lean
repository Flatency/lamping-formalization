import Lamping.Lamping.MatchingSourceEdgeRealization
import Lamping.Lambda.DegreeFamily
namespace Lamping.AG
open Graph Lambda Lambda.Labelled
section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable {g : Net signature N B W} {root : B} {original : LTerm}
private theorem old_access_unique (initial : INIT original)
    (matching : Matches g root original.erase)
    (hp : original.subterm p=some v) (hq : original.subterm q=some w)
    (label : v.label=w.label) (a b : RootAccess g root)
    (ha : accessWord g a.val=p) (hb : accessWord g b.val=q) : a=b := by
  have same := LTerm.subterm_label_injective original initial.2 hp hq label
  exact matching.accessWord_injective (ha.trans (same.trans hb.symm))
private theorem finish_node {a b : RootAccess g root} (same : a=b)
    {n m : N} {c : Port (g.label n).sort} {d : Port (g.label m).sort}
    (ha : a.val.getLast?=some (g.wire (.inl ⟨n,c⟩)))
    (hb : b.val.getLast?=some (g.wire (.inl ⟨m,d⟩))) : n=m := by
  have wires := Option.some.inj (ha.symm.trans (same ▸ hb))
  have endpoints := congrArg g.wire wires
  simp only [g.wire.involutive] at endpoints
  exact congrArg Sigma.fst (Sum.inl.inj endpoints)
private theorem departure_unique {kind : Kind} {c d e f : Port kind}
    (left : SyntaxChildPorts kind c d step) (right : SyntaxChildPorts kind e f step) : d=f := by
  cases left <;> cases right <;> rfl

/-- INIT fixes the original occurrence; Matches fixes its actual access.
Only then do the typed source-port roles fix the physical endpoint. -/
theorem SourcePortRealizes.unique (initial : INIT original)
    (matching : Matches g root original.erase)
    (left : SourcePortRealizes original g root port e)
    (right : SourcePortRealizes original g root port f) : e=f := by
  cases left with
  | external =>
    cases right with
    | external => rfl
    | departure _ role => cases role
  | departure hp role a ha roles finish =>
    cases role <;> cases right with
    | departure hq role b hb roles' finish' =>
      cases role
      have accesses := old_access_unique initial matching hp hq rfl a b ha hb
      have nodes := finish_node accesses finish finish'
      subst nodes
      have ports := departure_unique roles roles'
      cases ports
      rfl
  | appContext hp a ha shape role finish =>
    cases right with
    | departure _ sourceRole => cases sourceRole
    | appContext hq b hb shape' role' finish' =>
      have accesses := old_access_unique initial matching hp hq rfl a b ha hb
      have nodes := finish_node accesses finish finish'
      subst nodes
      have ports := eq_of_heq (role.trans role'.symm)
      cases ports
      rfl
  | lamContext hp a ha shape role finish =>
    cases right with
    | departure _ sourceRole => cases sourceRole
    | lamContext hq b hb shape' role' finish' =>
      have accesses := old_access_unique initial matching hp hq rfl a b ha hb
      have nodes := finish_node accesses finish finish'
      subst nodes
      have ports := eq_of_heq (role.trans role'.symm)
      cases ports
      rfl
  | binding hp a ha shape ctxRole role finish =>
    cases right with
    | departure _ sourceRole => cases sourceRole
    | binding hq b hb shape' ctxRole' role' finish' =>
      have accesses := old_access_unique initial matching hp hq rfl a b ha hb
      have nodes := finish_node accesses finish finish'
      subst nodes
      have ports := eq_of_heq (role.trans role'.symm)
      cases ports
      rfl
end
end Lamping.AG
