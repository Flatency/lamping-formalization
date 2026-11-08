import Lamping.Lamping.ActionSyntaxEndpointCases
namespace Lamping.AG
open Graph Lambda
section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable {g : Net signature N B W} {es : List (Endpoint g)}

theorem accessKind_at_actual_finish {kind : AccessKind}
    (typed : accessKind g es=some kind) (node : N) (port : Port (g.label node).sort)
    (finish : es.getLast?=some (g.wire (.inl ⟨node,port⟩))) :
    portKind (g.label node).sort port=some kind := by
  simpa only [accessKind,finish,Option.bind_some,Pairing.involutive] using typed
end
section
variable {s : Schema} {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K → Label signature}
variable (site : PathSite s kept (B:=B) (W:=W) (V:=V))

/-- A passive-kind exclusion is a literal port fact, not a representation premise. -/
theorem PathSite.action_access_kept_of_kind_excluded (action : IsAction s)
    {root : B} (path : RootAccess site.reduce root) {kind : AccessKind}
    (typed : accessKind site.reduce path.val=some kind)
    (excluded : ∀port : Port (.op s.passive),portKind (.op s.passive) port≠some kind) :
    ∃ port : NodePort signature K kept,
      path.val.getLast?=some (site.reduce.wire (.inl ⟨.inl port.1,port.2⟩)) := by
  rcases site.action_access_node_cases action path with kept |⟨node,port,passive,finish⟩
  · exact kept
  · have actual := accessKind_at_actual_finish typed (.inr node) port finish
    change portKind (s.right.net.label node).sort port=some kind at actual
    cases passive with
    | fan copy => exact (excluded port actual).elim
    | cro => exact (excluded port actual).elim
    | bra => exact (excluded port actual).elim
end
#print axioms accessKind_at_actual_finish
#print axioms PathSite.action_access_kept_of_kind_excluded
end Lamping.AG
