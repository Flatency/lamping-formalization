import Lamping.Graph.Rewrite
namespace Lamping.Graph

private def sumFlip : Bij (E ⊕ I) (I ⊕ E) where
  toFun := Sum.swap
  invFun := Sum.swap
  left_inv := by rintro (e | i) <;> rfl
  right_inv := by rintro (i | e) <;> rfl

private theorem right_closed (p : Pairing (E ⊕ I))
    (closed : ∀ i e,p (.inr i)≠.inl e) :
    ∀ i e,(p.rename (sumFlip (E:=E) (I:=I))) (.inl i)≠.inr e := by
  intro i e impossible
  have original := congrArg Sum.swap impossible
  change Sum.swap (Sum.swap (p (.inr i)))=Sum.inl e at original
  have same : Sum.swap (Sum.swap (p (.inr i)))=p (.inr i) := by cases p (.inr i) <;> rfl
  rw [same] at original
  exact closed i e original

/-- Restrict the actual pairing to a physically closed right-hand subset. -/
def Pairing.restrictRight (p : Pairing (E ⊕ I))
    (closed : ∀ i e,p (.inr i)≠.inl e) : Pairing I :=
  restrict (p.rename sumFlip) (right_closed p closed)

/-- The restricted pair is the same literal original mate, with its actual
subset tag. This does not choose a new wiring. -/
theorem Pairing.restrictRight_mate (p : Pairing (E ⊕ I))
    (closed : ∀ i e,p (.inr i)≠.inl e) (i : I) :
    p (.inr i)=.inr (p.restrictRight closed i) := by
  have actual := restrict_mate (p.rename (sumFlip (E:=E) (I:=I))) (right_closed p closed) i
  have original := congrArg Sum.swap actual
  change Sum.swap (Sum.swap (p (.inr i)))=Sum.inr (p.restrictRight closed i) at original
  have same : Sum.swap (Sum.swap (p (.inr i)))=p (.inr i) := by cases p (.inr i) <;> rfl
  rw [same] at original
  exact original
end Lamping.Graph
