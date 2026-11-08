import Lamping.Lambda.AppIdentity
import Lamping.Lambda.RootHeadGuard
namespace Lamping.Lambda.Marked

theorem trace_markAllAt_empty (apart : ∀ q, r≠pre++q) :
    tracePositions r (markAllAt F t pre)=[] := by
  cases he : tracePositions r (markAllAt F t pre) with
  | nil => rfl
  | cons q qs =>
    have hq : q∈tracePositions r (markAllAt F t pre) := by rw [he]; exact List.mem_cons_self
    have id := initial_application_identityAt ((mem_tagsAt _ r q).mpr hq)
    exact False.elim (apart q id)

/-- Initialize the nonredex application which a pending outer beta will
create. It is not yet a redex anywhere in this guarded source. -/
theorem rootHeadGuard_markAll
    (hp : subtermAt b site=some (.app (.var (binderDepth site)) inner)) :
    RootHeadGuard ([.fn,.body]++site) (markAll F (.app (.lam b) a)) := by
  have body : HeadVariable ([.fn,.body]++site) 0 (markAllAt F b [.fn,.body]) :=
    headVariable_markAllAt (by simpa using hp)
  have noRoot : [.fn,.body]++site ∉ ([[]] : List Path) := by simp
  have noArg : tracePositions ([.fn,.body]++site) (markAllAt F a [.arg])=[] :=
    trace_markAllAt_empty (by intro q eq; cases eq)
  simp only [markAll,markAllAt]
  split <;> exact ⟨body,noRoot,noArg⟩

def allRootTarget (F : List Path) (b a : Term) : Marked :=
  contract (markAllAt F b [.fn,.body]) (markAllAt F a [.arg])

theorem allRootTracking (F : List Path) (b a : Term) :
    History [[]] (markAll F (.app (.lam b) a)) (allRootTarget F b a) := by
  simp only [markAll,markAllAt]
  split
  · exact .cons (.redRoot [[]] _ _) (.nil _)
  · exact .cons (.appRoot [[]] _ _) (.nil _)

/-- The potential application's actual identity survives its creating root
contraction at the same body-local position, including nested binders. -/
theorem allRoot_created_identity
    (hp : subtermAt b site=some (.app (.var (binderDepth site)) inner)) :
    site∈tracePositions ([.fn,.body]++site) (allRootTarget F b a) := by
  have initial : site∈tracePositions ([.fn,.body]++site) (markAllAt F b [.fn,.body]) := by
    apply (mem_tagsAt _ _ _).mp
    rw [tagsAt_markAllAt,hp]
    exact List.mem_singleton_self _
  exact trace_subst_preserve initial _
end Lamping.Lambda.Marked
