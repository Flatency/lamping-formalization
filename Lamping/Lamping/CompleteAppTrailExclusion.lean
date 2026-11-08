import Lamping.Lamping.CompletePhysicalAppOrigins
import Lamping.Lamping.CurrentRedexPorts

namespace Lamping.AG
open Graph Lambda Lambda.Labelled
section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable {g : Net signature N B W} {root : B} {original target : LTerm}

/-- A genuine CURRENT syntax trail for a completed physical fiber cannot
observe the selected application's context. Its source-port witness and
final atom are read from the SAME trail. No equality of original origins
is inferred from physical node identity alone. -/
theorem BetaEdge.complete_app_trail_exclusion
    (beta : BetaEdge g) (initial : INIT original) (matching : Matches g root original.erase)
    {boundary : B → Bool} (flow : FlowBalance g boundary) (positive : boundary root=true)
    {ps : List Path} {marked : Marked}
    (relative : Marked.RelativeHistory ps
      (Marked.mark (physicalBetaFiberPaths g root original.erase beta.app beta.lam) original.erase) marked)
    (normal : Marked.Normal marked) (labels : History ps original target)
    {env ctx p stamp fn arg finish}
    (trail : PhysicalSyntaxTrail original root beta env ctx target p (.app stamp fn arg) finish)
    (atSelected : trail.toEndpoint=.inl ⟨beta.app,beta.appCtx⟩) : False := by
  obtain ⟨n,lastAtom,sourceFinish⟩ := trail.image.app_finish
  have realizes : SourcePortRealizes original g root finish (.inl ⟨beta.app,beta.appCtx⟩) := by
    rw [←atSelected]
    exact trail.toRealizes
  rw [sourceFinish] at realizes
  exact beta.complete_no_realized_app_origin initial matching flow positive relative normal labels
    realizes trail.lookup (by rw [lastAtom]; rfl)

end
end Lamping.AG
