import Lamping.Lamping.MatchingRedexEndpointUniqueness

namespace Lamping.AG
open Graph Lambda
section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable {g : Net signature N B W} {root : B}

/-- The same matched occurrence determines the complete ordered connection. -/
theorem ActualRedexAccess.connection_edges_unique {t : Term} {redex : RedexOcc t}
    (matching : Matches g root t) (first second : ActualRedexAccess g root redex) :
    first.connection.edges=second.connection.edges := by
  obtain ⟨parent,child,_app,_lam⟩ := ActualRedexAccess.endpoints_unique matching first second
  have parents : first.parent.val=second.parent.val := congrArg Subtype.val parent
  have children : first.child.val=second.child.val := congrArg Subtype.val child
  rw [first.split,second.split,parents] at children
  exact List.append_cancel_left children
end
end Lamping.AG
