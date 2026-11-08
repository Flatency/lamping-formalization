import Lamping.Lambda.CreationPrefixOutside
import Lamping.Lambda.FiniteSelectionReindex
namespace Lamping.Lambda

/-- One genuine syntax constructor surrounding a fixed child. -/
inductive SyntaxFrame where
  | fn (argument : Term)
  | arg (function : Term)
  | body

namespace SyntaxFrame
def edge : SyntaxFrame → Step
  | .fn _ => .fn
  | .arg _ => .arg
  | .body => .body
def plug : SyntaxFrame → Term → Term
  | .fn a, t => .app t a
  | .arg f, t => .app f t
  | .body, t => .lam t
 theorem lookup (C : SyntaxFrame) (t : Term) : subtermAt (C.plug t) [C.edge] = some t := by
   cases C <;> simp [plug, edge, subtermAt]
 theorem plug_injective (C : SyntaxFrame) : Function.Injective C.plug := by
   intro t u he
   cases C <;> simp_all [plug]
 theorem beta_reflect (C : SyntaxFrame) (h : BetaAt (C.plug t) (C.edge :: p) u) :
     ∃ v, BetaAt t p v ∧ u = C.plug v := by
   have hp := C.lookup t
   have h' : BetaAt (C.plug t) ([C.edge] ++ p) u := h
   obtain ⟨v, hv, hr, _⟩ := h'.prefix_reflect hp
   refine ⟨v, hv, ?_⟩
   cases C <;> simpa [plug, edge, replaceAt, Option.some.injEq] using hr.symm
 theorem parallel_reflect (C : SyntaxFrame)
     (h : ParallelStep (F.map (C.edge :: ·)) (C.plug t) u) :
     ∃ v, ∃ k : ParallelStep F t v, u = C.plug v ∧ h.paths = k.paths.map (C.edge :: ·) := by
   cases C with
   | fn a => exact h.app_left_scope
   | arg f => exact h.app_right_scope
   | body => exact h.lam_scope
 def redex_lift (C : SyntaxFrame) (r : RedexOcc t) : RedexOcc (C.plug t) :=
   ⟨C.edge :: r.val, by
     have hp : subtermAt (C.plug t) (C.edge :: r.val) = subtermAt t r.val := by
       change subtermAt (C.plug t) ([C.edge] ++ r.val) = subtermAt t r.val
       rw [subtermAt_append, C.lookup, Option.bind_some]
     rw [hp]
     exact r.property⟩
 def redex_reflect (C : SyntaxFrame) (R : RedexOcc (C.plug t)) (p : Path)
     (he : R.val = C.edge :: p) : RedexOcc t :=
   ⟨p, by
     have hp := R.property
     rw [he] at hp
     have hlookup : subtermAt (C.plug t) ([C.edge] ++ p) = subtermAt t p := by
       rw [subtermAt_append, C.lookup, Option.bind_some]
     exact hlookup ▸ hp⟩
end SyntaxFrame
end Lamping.Lambda
