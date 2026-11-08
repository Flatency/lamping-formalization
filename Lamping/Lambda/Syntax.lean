import Std
namespace Lamping.Lambda
inductive Term where
  | var : Nat → Term
  | app : Term → Term → Term
  | lam : Term → Term
  deriving DecidableEq, Repr

def Scoped (n : Nat) : Term → Prop
  | .var i => i < n
  | .app f a => Scoped n f ∧ Scoped n a
  | .lam b => Scoped (n+1) b
abbrev Closed := Scoped 0
end Lamping.Lambda
