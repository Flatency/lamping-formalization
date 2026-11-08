import Lamping.Lamping.CancellationUnobservedExits
namespace Lamping.AG
open Graph Lambda

private def port_token : (k : Kind) → Port k → Path
  | .op .app,.inl () => [.fn]
  | .op .app,.inr true => [.arg]
  | .op .lam,.inr true => [.body]
  | _,_ => []

private theorem forward_unobserved_token (k : Kind) (p q : Port k)
    (forward : ForwardPorts k p q) (unobserved : portKind k p=none) : port_token k q=[] := by
  cases k with
  | garbage => exact False.elim forward
  | op op => cases op <;> simp_all [ForwardPorts,portKind,port_token,AG.appCtx,AG.appArg,AG.lamBody]

section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable {g : Net signature N B W}

/-- A forward path without proper arrivals before its final segment emits
no syntax turns. The first segment is skipped by accessWord: its departure
token is deliberately NOT asserted to be empty. -/
theorem Forward.unobserved_access_word {es : List (Endpoint g)} (forward : Forward g es)
    (unobserved : ∀ e∈es.dropLast,accessKind g [e]=none) : accessWord g es=[] := by
  induction forward with
  | single e => rfl
  | @node e f es node p q arrives leaves direction rest ih =>
    have before : accessKind g [e]=none := unobserved e (by
      change e∈e::(f::es).dropLast
      exact List.mem_cons_self)
    have portNone : portKind (g.label node).sort p=none := by
      change (match g.wire e with
        | .inl ⟨n,port⟩ => portKind (g.label n).sort port
        | _ => none)=none at before
      rw [arrives] at before
      exact before
    have emitted : arrivalWord g f=[] := by
      rw [leaves]
      exact forward_unobserved_token (g.label node).sort p q direction portNone
    have after := ih (by
      intro x member
      exact unobserved x (by
        change x∈e::(f::es).dropLast
        exact List.mem_cons_of_mem _ member))
    change arrivalWord g f++es.flatMap (arrivalWord g)=[]
    change es.flatMap (arrivalWord g)=[] at after
    rw [emitted,after]
    rfl
  | @transparent e f es vertex d arrives leaves rest ih =>
    have emitted : arrivalWord g f=[] := by rw [leaves]; rfl
    have after := ih (by
      intro x member
      exact unobserved x (by
        change x∈e::(f::es).dropLast
        exact List.mem_cons_of_mem _ member))
    change arrivalWord g f++es.flatMap (arrivalWord g)=[]
    change es.flatMap (arrivalWord g)=[] at after
    rw [emitted,after]
    rfl
end
end Lamping.AG
