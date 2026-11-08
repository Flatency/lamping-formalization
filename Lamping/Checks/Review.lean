import Lamping.Lambda.Named
import Lamping.Graph.Examples

/-! Independent semantic counterchecks; no algorithm correctness is claimed. -/
namespace Lamping.Checks.Review
open Lamping.Lambda

-- A free variable inserted under lambda must not become the bound variable.
example : subst (fun _ => Term.var 0) (.lam (.var 1)) ≠ .lam (.var 0) := by decide
-- Shadowing selects the closest binder; a different inner name retains index 1.
example : Named.erase [] (.lam "x" (.lam "x" (.var "x"))) = .lam (.lam (.var 0)) := rfl
example : Named.erase [] (.lam "x" (.lam "y" (.var "x"))) ≠ .lam (.lam (.var 0)) := by decide

open Lamping.Graph
-- The old internal subdivision vertex is absent from this exact result type.
example : Net fixtureSignature (Empty ⊕ Empty) Empty ((Empty ⊕ Empty) ⊕ (Bool × Bool)) := annihilated
example : annihilated.wire (.inr (.inr (.inr (false,false),false))) =
    .inr (.inr (.inr (true,false),false)) := rfl
example : annihilated.wire (.inr (.inr (.inr (false,false),true))) =
    .inr (.inr (.inr (true,false),true)) := rfl
example : closedCircle.wire (.inr (.inr (.inr (),false))) =
    .inr (.inr (.inr (),true)) := rfl
#print axioms Lamping.Lambda.subst_comp
#print axioms Lamping.Lambda.Named.alpha_iff_erase
#print axioms cutFragment_boundary
#print axioms replace_pairing
#print axioms replace_boundary
#print axioms NetIso.refl
#print axioms NetIso.trans
#print axioms NetIso.symm
#print axioms restrict_natural
#print axioms plug_natural
end Lamping.Checks.Review

