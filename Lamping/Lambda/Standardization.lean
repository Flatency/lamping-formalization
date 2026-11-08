import Lamping.Lambda.Permutation
namespace Lamping.Lambda

/-- Strict leftmost-outermost order on actual lambda occurrences: a proper
 pre precedes its descendants, and a function subtree precedes an argument.
 The body edge has no competing sibling. -/
inductive LeftOf : Path → Path → Prop where
  | outer (s : Step) (p : Path) : LeftOf [] (s :: p)
  | child (s : Step) : LeftOf p q → LeftOf (s :: p) (s :: q)
  | branch (p q : Path) : LeftOf (.fn :: p) (.arg :: q)

namespace LeftOf
 theorem irrefl (p : Path) : ¬ LeftOf p p := by
   intro h
   induction p with
   | nil => cases h
   | cons s p ih =>
     cases h with
     | child _ h => exact ih h
end LeftOf

/-- The selected set is read extensionally; LO is an actual redex occurrence. -/
def LeftmostSelected (F : List Path) (r : RedexOcc t) : Prop :=
  r.val ∈ F ∧ ∀ s : RedexOcc t, s.val ∈ F → ¬ LeftOf s.val r.val

/-- No later contracted LO redex is a residual of a source redex lying left
 of the earlier LO contraction (AG5.1, printed105/PDF107). Quantification over
 decompositions retains real intermediate terms and the residual history. -/
def DoesNotReturnLeft (r : RedexOcc t) (h : ParallelHistory t u) : Prop :=
  ∀ (s : RedexOcc t), LeftOf s.val r.val →
    ∀ {v w : Term} {F : List Path}
      (pre : ParallelHistory t v) (step : ParallelStep F v w)
      (suffix : ParallelHistory w u),
      h = pre.append (.cons step suffix) →
      ∀ q : RedexOcc v, LeftmostSelected F q →
        ¬ pre.derivation.Residual s q

/-- Source standardness, including the vacuous cases created by an empty
 parallel step. Nonempty steps must possess the genuine selected LO redex. -/
inductive Standard : ParallelHistory t u → Prop where
  | nil (t) : Standard (.nil t)
  | empty (h : ParallelStep [] t u) : Standard hs → Standard (.cons h hs)
  | cons (h : ParallelStep F t u) (r : RedexOcc t) :
      LeftmostSelected F r → DoesNotReturnLeft r (.cons h hs) →
      Standard hs → Standard (.cons h hs)

 theorem standard_nil (t : Term) : Standard (.nil t) := .nil t
 theorem leftmost_singleton (r : RedexOcc t) : LeftmostSelected [r.val] r := by
   constructor
   · exact List.mem_singleton_self _
   · intro s hs
     have he : s.val = r.val := List.mem_singleton.mp hs
     rw [he]
     exact LeftOf.irrefl _
end Lamping.Lambda

