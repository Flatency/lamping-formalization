import Lamping.Lamping.ControlContextTails
namespace Lamping.AG
open Graph

private def InverseDomain (i : Nat) : (k : Kind) → Port k → Port k → Context → Context → Prop
  | .op .fan,.inl _,.inr q,a,_ => ∀ changed,changed.get i=a.get i →
      ∃ result,Traversal i (.op .fan) (.inl ()) (.inr q) changed result
  | .op .cro,.inl _,.inr q,a,_ => ∀ changed,changed.get i=a.get i →
      ∃ result,Traversal i (.op .cro) (.inl ()) (.inr q) changed result
  | .op .bra,.inl _,.inr q,a,_ => ∀ changed,changed.get i=a.get i →
      ∃ result,Traversal i (.op .bra) (.inl ()) (.inr q) changed result
  | _,_,_,_,_ => True

private theorem inverse_domain {i k p q a b} (rule : Traversal i k p q a b) : InverseDomain i k p q a b := by
  cases rule with
  | direct passage => cases passage <;> trivial
  | inverse passage =>
    cases passage <;> try trivial
    case fanO pre tail x =>
      intro changed level
      have atLevel : changed.get i=.o x := by simpa [Context.replace] using level
      have rebuilt := InitialOffsets.rebuild changed i
      rw [atLevel] at rebuilt
      have actual := Traversal.inverse (Passage.fanO (i:=i) changed (changed.tail (i+1)) x)
      rw [rebuilt] at actual
      exact ⟨_,actual⟩
    case fanStar pre tail x =>
      intro changed level
      have atLevel : changed.get i=.star x := by simpa [Context.replace] using level
      have rebuilt := InitialOffsets.rebuild changed i
      rw [atLevel] at rebuilt
      have actual := Traversal.inverse (Passage.fanStar (i:=i) changed (changed.tail (i+1)) x)
      rw [rebuilt] at actual
      exact ⟨_,actual⟩
    case cro pre tail =>
      intro changed level
      have atLevel : changed.get i=.empty := by simpa [Context.replace] using level
      have rebuilt := InitialOffsets.rebuild changed i
      rw [atLevel] at rebuilt
      have actual := Traversal.inverse (Passage.cro (i:=i) changed (changed.tail (i+1)))
      rw [rebuilt] at actual
      exact ⟨_,actual⟩
    case bra pre tail x y =>
      intro changed level
      have atLevel : changed.get i=.pair x y := by simpa [Context.replace] using level
      have rebuilt := InitialOffsets.rebuild changed i
      rw [atLevel] at rebuilt
      have actual := Traversal.inverse (Passage.bra (i:=i) changed (changed.tail (i+1)) x y)
      rw [rebuilt] at actual
      exact ⟨_,actual⟩

/-- Inverse control legality depends on the constructor at exactly its index.
Other levels and the context above that index may change freely. -/
theorem Traversal.control_inverse_transfer {c : Op} {i : Nat} {q : Aux c} {a b : Context}
    (control : c=.fan ∨c=.cro ∨c=.bra)
    (rule : Traversal i (.op c) (.inl ()) (.inr q) a b)
    (changed : Context) (level : changed.get i=a.get i) :
    ∃ result,Traversal i (.op c) (.inl ()) (.inr q) changed result := by
  have domain := inverse_domain rule
  rcases control with rfl |rfl |rfl <;> exact domain changed level
end Lamping.AG
