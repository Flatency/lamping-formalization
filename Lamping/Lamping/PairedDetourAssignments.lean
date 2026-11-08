import Lamping.Lamping.PairedStreamCuts
import Lamping.Lamping.PairedStreamAppend
namespace Lamping.AG
open Graph
private theorem proper_incoming_flow (actual : Graph.Label signature) (p : Port actual.sort)
    (op : Op) (i : Nat) (canonical : Port (.op op))
    (lab : actual=label op i) (role : HEq p canonical)
    (negative : ∀ base,flowPort (.op op) base canonical=false) (base : Bool) :
    flowPort actual.sort base p=false := by
  subst actual
  cases eq_of_heq role
  exact negative base
section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable {g : Net signature N B W} {root : B} {boundary : B → Bool}
/-- Extract assignments from an already supplied whole detour. The argument
seam is fixed by the actual reversed principal route, rather than guessed
from a separate loop witness. No generatedness or total-input premise is used. -/
theorem BetaDetourBlocks.detour_assignments
    (flow : FlowBalance g boundary) (positive : boundary root=true)
    (edge : BetaEdge g) (pre loop suffix : List (Endpoint g))
    (preEnd : pre.getLast?=some (g.wire (.inl ⟨edge.app,edge.appCtx⟩)))
    (loopEnd : loop.getLast?=some (g.wire (.inl ⟨edge.lam,edge.lamBind⟩)))
    {a output : Context} {count : Nat}
    (path : BetaDetourBlocks g
      (pre++edge.principal++loop++edge.reverseRoute++(edge.argEnd::suffix)) a output count) :
    ∃ appContext bodyEnd bodyCount prefixCount tailCount,
      BetaDetourBlocks g (pre++edge.principal++loop) a bodyEnd bodyCount ∧
      BetaDetourBlocks g pre a appContext prefixCount ∧
      ExpandedLabelling g (pre++edge.principal) a appContext ∧
      BetaDetourBlocks g (edge.argEnd::suffix) bodyEnd output tailCount := by
  have bodyFinish : (pre++edge.principal++loop).getLast?=
      some (g.wire (.inl ⟨edge.lam,edge.lamBind⟩)) := by
    simp only [List.getLast?_append,loopEnd,Option.some_or]
  have bodyNonempty : pre++edge.principal++loop≠[] := by
    intro empty
    rw [empty] at bodyFinish
    cases bodyFinish
  have preNonempty : pre≠[] := by
    intro empty
    rw [empty] at preEnd
    cases preEnd
  have bodyPositive : flowEndpoint g flow.nodes boundary flow.vertices
      (g.wire (.inl ⟨edge.lam,edge.lamBind⟩))=true := by
    rw [flow.wiring]
    have negative := proper_incoming_flow (g.label edge.lam) edge.lamBind .lam edge.index
      lamBind edge.lamLabel edge.lamBind_role (by intro base; rfl) (flow.nodes edge.lam)
    change flowEndpoint g flow.nodes boundary flow.vertices (.inl ⟨edge.lam,edge.lamBind⟩)=false at negative
    rw [negative]
    rfl
  have appPositive : flowEndpoint g flow.nodes boundary flow.vertices
      (g.wire (.inl ⟨edge.app,edge.appCtx⟩))=true := by
    rw [flow.wiring]
    have negative := proper_incoming_flow (g.label edge.app) edge.appCtx .app edge.index
      appCtx edge.appLabel edge.appCtx_role (by intro base; rfl) (flow.nodes edge.app)
    change flowEndpoint g flow.nodes boundary flow.vertices (.inl ⟨edge.app,edge.appCtx⟩)=false at negative
    rw [negative]
    rfl
  have whole := path.labelling g
  have bodyWhole : ExpandedLabelling g
      ((pre++edge.principal++loop)++(edge.reverseRoute++(edge.argEnd::suffix))) a output := by
    simpa only [List.append_assoc] using whole
  obtain ⟨bodyEnd,bodyLabels⟩ := bodyWhole.prefix bodyNonempty
  have streamWhole : BetaDetourBlocks g
      ((pre++edge.principal++loop)++(edge.reverseRoute++(edge.argEnd::suffix))) a output count := by
    simpa only [List.append_assoc] using path
  obtain ⟨bodyCount,_,bodyStream⟩ := streamWhole.prefix_at_positive_assignment
    flow positive bodyLabels bodyFinish bodyPositive
  have prefixWhole : ExpandedLabelling g (pre++(edge.principal++loop)) a bodyEnd := by
    simpa only [List.append_assoc] using bodyLabels
  obtain ⟨appContext,prefixLabels⟩ := prefixWhole.prefix preNonempty
  have bodyStream' : BetaDetourBlocks g (pre++(edge.principal++loop)) a bodyEnd bodyCount := by
    simpa only [List.append_assoc] using bodyStream
  obtain ⟨prefixCount,_,prefixStream⟩ := bodyStream'.prefix_at_positive_assignment
    flow positive prefixLabels preEnd appPositive
  have ambient : ExpandedLabelling g (pre++edge.principal) a appContext := by
    apply prefixLabels.splice preEnd (edge.principal_labeling appContext).expanded edge.principalStart
    simpa only [Pairing.involutive] using ExpandedTurn.ordinary (edge.app_fun_turn appContext)
  have canonical := bodyStream.append_backward_paired edge (.single edge.argEnd bodyEnd) bodyFinish rfl
  have canonicalLabels : ExpandedLabelling g
      ((pre++edge.principal++loop++edge.reverseRoute)++[edge.argEnd]) a bodyEnd := by
    simpa only [List.append_assoc] using canonical.labelling g
  have argPositive : flowEndpoint g flow.nodes boundary flow.vertices edge.argEnd=true :=
    (AtProperRole.appArg edge.app edge.appArg edge.index edge.appLabel edge.appArg_role).outgoing_flow
      trivial flow.nodes boundary flow.vertices positive
  obtain ⟨tailCount,_,tailStream⟩ := path.suffix_at_positive_assignment
    flow positive canonicalLabels argPositive
  exact ⟨appContext,bodyEnd,bodyCount,prefixCount,tailCount,bodyStream,prefixStream,ambient,tailStream⟩
end
end Lamping.AG