import Lamping.Lamping.InternalControlCorridorStep
import Lamping.Lamping.InitialControlCorridorStep
import Lamping.Lamping.TerminalControlCorridorStep
import Lamping.Lamping.TransparentRedexStep
import Lamping.Lambda.BetaPaths
namespace Lamping.AG
open Graph Lambda
section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable {g : Net signature N B W} {directions : B → Bool} {depths : B → Int} {root : B}

/-- All four finite-corridor cases of an actual redex connection. Full
Independence remains an explicit source hypothesis, used only for the initial
application/control case; no assertion of reachable Independence is made. -/
theorem RedexConnection.graph_step (connection : RedexConnection g)
    (independence : Independence g root) (balance : IndexedLevelBalance g depths)
    (rootDepth : depths root=0) (flow : FlowBalance g directions) :
    ∃ schema target,GraphStep schema (ActualNet.ofNet g) target := by
  obtain ⟨route,leftPrincipal,rightPrincipal,before,after,split⟩ := connection.principal_corridor
  have leftEndpoint (empty : before=[]) : route.first=⟨connection.app,connection.appPort⟩ := by
    have start := connection.start
    rw [split,empty,List.nil_append,List.head?_append,route.start,Option.some_or] at start
    exact Sum.inl.inj (Option.some.inj start)
  have rightEndpoint (empty : after=[]) : route.last=⟨connection.lam,connection.lamPort⟩ := by
    have finish := connection.finish
    rw [split,empty,List.append_nil,List.getLast?_append,route.finish,Option.some_or] at finish
    have same := congrArg g.wire.mate (Option.some.inj finish)
    simp only [Pairing.involutive] at same
    exact Sum.inl.inj same
  cases before with
  | nil =>
    cases after with
    | nil =>
      have transparent : TransparentTurns (g:=g) connection.edges := by
        simpa only [split,List.nil_append,List.append_nil] using route.transparent
      obtain ⟨target,step⟩ := connection.transparent_graph_step balance.toLevelBalance flow transparent
      exact ⟨_,target,step⟩
    | cons next remaining =>
      have rightControl := control_corridor_right connection.control_only route [] (next::remaining) split (by simp)
      exact connection.initial_control_graph_step independence flow route (leftEndpoint rfl) rightPrincipal
        rightControl next remaining (by simpa only [List.nil_append] using split)
  | cons previous initial =>
    cases after with
    | nil =>
      have leftControl := control_corridor_left connection.control_only route (previous::initial) [] split (by simp)
      exact connection.terminal_control_graph_step balance rootDepth flow route (rightEndpoint rfl) leftPrincipal
        leftControl (previous::initial) (by simp) (by simpa only [List.append_nil] using split)
    | cons next remaining =>
      obtain ⟨a,b,labels⟩ := connection.proper.1
      exact labels.internal_control_corridor_step connection.control_only flow route leftPrincipal rightPrincipal
        (previous::initial) (next::remaining) split (by simp) (by simp)

/-- Source Matches supplies the existing physical connection for a particular
syntax redex. This does not assume target Matches or a readback certificate. -/
theorem Matches.syntax_redex_graph_step {t : Term} (matching : Matches g root t)
    (independence : Independence g root) (balance : IndexedLevelBalance g depths)
    (rootDepth : depths root=0) (flow : FlowBalance g directions) (redex : RedexOcc t) :
    ∃ schema target,GraphStep schema (ActualNet.ofNet g) target := by
  obtain ⟨connection⟩ := matching.redex_connection redex
  exact connection.graph_step independence balance rootDepth flow

/-- Conditional NF reflection. Reachable source Matches and full ordinary
Independence are separate theorem obligations, not fields of ActualNet. -/
theorem GraphNormal.no_syntax_redex {t : Term} (normal : GraphNormal (ActualNet.ofNet g))
    (matching : Matches g root t) (independence : Independence g root)
    (balance : IndexedLevelBalance g depths) (rootDepth : depths root=0)
    (flow : FlowBalance g directions) : ∀ _ : RedexOcc t,False := by
  intro redex
  obtain ⟨schema,target,step⟩ := matching.syntax_redex_graph_step independence balance rootDepth flow redex
  exact normal schema target step

theorem GraphNormal.no_syntax_beta {t : Term} (normal : GraphNormal (ActualNet.ofNet g))
    (matching : Matches g root t) (independence : Independence g root)
    (balance : IndexedLevelBalance g depths) (rootDepth : depths root=0)
    (flow : FlowBalance g directions) : ¬∃ u,Beta t u := by
  rintro ⟨u,beta⟩
  obtain ⟨p,contraction⟩ := beta_iff_betaAt.mp beta
  exact normal.no_syntax_redex matching independence balance rootDepth flow ⟨p,contraction.redex⟩
end
end Lamping.AG
