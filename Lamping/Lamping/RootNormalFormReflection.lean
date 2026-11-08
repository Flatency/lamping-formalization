import Lamping.Lamping.ConditionalNormalFormReflection
import Lamping.Lamping.RootInitialControlStep
namespace Lamping.AG
open Graph Lambda
section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable {g : Net signature N B W} {directions : B → Bool} {depths : B → Int} {root : B}

/-- The actual four-corridor proof with root-input existence replacing full
proper-source Independence. Rich source access provenance is essential to
the initial control case; it is not erased to a bare connecting path. -/
theorem ActualRedexAccess.graph_step_of_root_inputs {t : Term} {redex : RedexOcc t}
    (access : ActualRedexAccess g root redex) (inputs : RootInputs g root)
    (balance : IndexedLevelBalance g depths) (rootDepth : depths root=0)
    (flow : FlowBalance g directions) :
    ∃ schema target,GraphStep schema (ActualNet.ofNet g) target := by
  obtain ⟨route,leftPrincipal,rightPrincipal,before,after,split⟩ := access.connection.principal_corridor
  have leftEndpoint (empty : before=[]) : route.first=⟨access.connection.app,access.connection.appPort⟩ := by
    have start := access.connection.start
    rw [split,empty,List.nil_append,List.head?_append,route.start,Option.some_or] at start
    exact Sum.inl.inj (Option.some.inj start)
  have rightEndpoint (empty : after=[]) : route.last=⟨access.connection.lam,access.connection.lamPort⟩ := by
    have finish := access.connection.finish
    rw [split,empty,List.append_nil,List.getLast?_append,route.finish,Option.some_or] at finish
    have same := congrArg g.wire.mate (Option.some.inj finish)
    simp only [Pairing.involutive] at same
    exact Sum.inl.inj same
  cases before with
  | nil =>
    cases after with
    | nil =>
      have transparent : TransparentTurns (g:=g) access.connection.edges := by
        simpa only [split,List.nil_append,List.append_nil] using route.transparent
      obtain ⟨target,step⟩ := access.connection.transparent_graph_step balance.toLevelBalance flow transparent
      exact ⟨_,target,step⟩
    | cons next remaining =>
      have rightControl := control_corridor_right access.connection.control_only route [] (next::remaining) split (by simp)
      exact access.root_initial_control_graph_step inputs balance rootDepth flow route (leftEndpoint rfl)
        rightPrincipal rightControl next remaining (by simpa only [List.nil_append] using split)
  | cons previous initial =>
    cases after with
    | nil =>
      have leftControl := control_corridor_left access.connection.control_only route (previous::initial) [] split (by simp)
      exact access.connection.terminal_control_graph_step balance rootDepth flow route (rightEndpoint rfl)
        leftPrincipal leftControl (previous::initial) (by simp) (by simpa only [List.append_nil] using split)
    | cons next remaining =>
      obtain ⟨a,b,labels⟩ := access.connection.proper.1
      exact labels.internal_control_corridor_step access.connection.control_only flow route leftPrincipal
        rightPrincipal (previous::initial) (next::remaining) split (by simp) (by simp)

theorem Matches.syntax_redex_graph_step_of_root_inputs {t : Term} (matching : Matches g root t)
    (inputs : RootInputs g root) (balance : IndexedLevelBalance g depths)
    (rootDepth : depths root=0) (flow : FlowBalance g directions) (redex : RedexOcc t) :
    ∃ schema target,GraphStep schema (ActualNet.ofNet g) target := by
  obtain ⟨access⟩ := matching.actual_redex_access redex
  exact access.graph_step_of_root_inputs inputs balance rootDepth flow

/-- Source-root-input NF reflection. Source Matches and RootInputs still
require actual trace-preservation proofs; neither is a presumed graph field. -/
theorem GraphNormal.no_syntax_redex_of_root_inputs {t : Term}
    (normal : GraphNormal (ActualNet.ofNet g)) (matching : Matches g root t)
    (inputs : RootInputs g root) (balance : IndexedLevelBalance g depths)
    (rootDepth : depths root=0) (flow : FlowBalance g directions) : ∀ _ : RedexOcc t,False := by
  intro redex
  obtain ⟨schema,target,step⟩ := matching.syntax_redex_graph_step_of_root_inputs inputs balance rootDepth flow redex
  exact normal schema target step

theorem GraphNormal.no_syntax_beta_of_root_inputs {t : Term}
    (normal : GraphNormal (ActualNet.ofNet g)) (matching : Matches g root t)
    (inputs : RootInputs g root) (balance : IndexedLevelBalance g depths)
    (rootDepth : depths root=0) (flow : FlowBalance g directions) : ¬∃ u,Beta t u := by
  rintro ⟨u,beta⟩
  obtain ⟨p,contraction⟩ := beta_iff_betaAt.mp beta
  exact normal.no_syntax_redex_of_root_inputs matching inputs balance rootDepth flow ⟨p,contraction.redex⟩
end
end Lamping.AG
