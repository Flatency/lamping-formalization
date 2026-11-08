import Lamping.Lamping.PathSiteBetaLifting
namespace Lamping.AG
open Graph
section
variable {s : Schema} {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K → Label signature} (site : PathSite s kept (B:=B) (W:=W) (V:=V))

private theorem outside_turn {x y : Endpoint (cutFragment site.net (pathPartition s V) site.closed)}
    {a b : Context} (turn : PlugTurn (cutFragment site.net (pathPartition s V) site.closed) s.right.net
      (.inl x) (.inl y) a b) :
    LabelledTurn (cutFragment site.net (pathPartition s V) site.closed) x y a b := by
  cases turn with
  | left localTurn => exact localTurn

private theorem enter_context {x : Endpoint (cutFragment site.net (pathPartition s V) site.closed)}
    {y : Endpoint s.right.net} {a b : Context}
    (turn : PlugTurn (cutFragment site.net (pathPartition s V) site.closed) s.right.net (.inl x) (.inr y) a b) : a=b := by
  cases turn
  rfl

private theorem leave_context {x : Endpoint s.right.net}
    {y : Endpoint (cutFragment site.net (pathPartition s V) site.closed)} {a b : Context}
    (turn : PlugTurn (cutFragment site.net (pathPartition s V) site.closed) s.right.net (.inr x) (.inl y) a b) : a=b := by
  cases turn
  rfl

theorem Forward.outsideEnd {es : List (Endpoint (cutFragment site.net (pathPartition s V) site.closed))}
    (forward : Forward (cutFragment site.net (pathPartition s V) site.closed) es) :
    Forward site.net (es.map site.outsideEnd) := by
  induction forward with
  | single e => exact .single _
  | @node e f es n p q arrival leave direction rest ih =>
    apply Forward.node (.inl n) p q
    · exact (site.outsideEnd_wire e).trans (congrArg site.outsideEnd arrival)
    · exact congrArg site.outsideEnd leave
    · exact direction
    · exact ih
  | @transparent e f es w d arrival leave rest ih =>
    apply Forward.transparent (.inl w) d
    · exact (site.outsideEnd_wire e).trans (congrArg site.outsideEnd arrival)
    · exact congrArg site.outsideEnd leave
    · exact ih

def RawOutsidePositive {boundary : B → Bool} (flow : FlowBalance site.net boundary)
    (raw : List (PlugSegment (cutFragment site.net (pathPartition s V) site.closed) s.right.net)) : Prop :=
  ∀ e, .inl e ∈ raw →
    flowEndpoint (cutFragment site.net (pathPartition s V) site.closed)
      (site.cut_flowBalance flow).nodes
      (Sum.elim boundary (fun f => !(site.frontierFlow flow f)))
      (site.cut_flowBalance flow).vertices e = true

/-- Actual root labels in the plug force positivity of every outside-cut
occurrence. The explicit replacement witness preserves those cut values. -/
theorem PlugLabelling.outside_positive {boundary : B → Bool} (flow : FlowBalance site.net boundary)
    (root : B) (rootPolarity : boundary root=true)
    {raw a b} (labels : PlugLabelling (cutFragment site.net (pathPartition s V) site.closed) s.right.net raw a b)
    (rooted : (raw.map (plugEnd _ _)).head?=some (.inr (.inl root))) :
    RawOutsidePositive site flow raw := by
  obtain ⟨rhs⟩ := s.flow_preservation (site.frontierFlow flow) (site.left_flowBalance flow)
  let c := cutFragment site.net (pathPartition s V) site.closed
  let target := FlowBalance.plug c s.right.net boundary (site.frontierFlow flow) (site.cut_flowBalance flow) rhs
  have positives := (labels.actual _ _).root_positive_departures target root rooted rootPolarity
  intro e mem
  have positive := positives ((plugEnd c.label s.right.net.label) (.inl e)) (List.mem_map_of_mem mem)
  change flowEndpoint (plug c s.right.net) (Sum.elim (site.cut_flowBalance flow).nodes rhs.nodes)
    boundary (plugPolarity (site.frontierFlow flow) (site.cut_flowBalance flow).vertices rhs.vertices)
    ((plugEnd c.label s.right.net.label) (.inl e)) = true at positive
  rw [flowEndpoint_plugLeft] at positive
  exact positive
end

private theorem app_forward_roles {kind : Kind} {p q : Port kind}
    (sort : kind=.op .app) (source : HEq p AG.appCtx)
    (target : HEq q (Sum.inl () : Port (.op .app))) : ForwardPorts kind p q := by
  subst kind
  have hp : p=AG.appCtx := eq_of_heq source
  have hq : q=.inl () := eq_of_heq target
  subst p; subst q
  exact ⟨rfl,Or.inl rfl⟩

private theorem lam_forward_roles {kind : Kind} {p q : Port kind}
    (sort : kind=.op .lam) (source : HEq p (Sum.inl () : Port (.op .lam)))
    (target : HEq q AG.lamBody) : ForwardPorts kind p q := by
  subst kind
  have hp : p=.inl () := eq_of_heq source
  have hq : q=AG.lamBody := eq_of_heq target
  subst p; subst q
  exact ⟨rfl,rfl⟩

section
variable {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K → Label signature} {i : Nat}
variable (site : PathSite (.beta i) kept (B:=B) (W:=W) (V:=V))

private theorem context_direction {edge : BetaEdge site.net} (geometry : SiteBetaGeometry site edge)
    {e : Endpoint (cutFragment site.net (pathPartition (.beta i) V) site.closed)} {oldTail : List (Endpoint site.net)}
    (arrival : (cutFragment site.net (pathPartition (.beta i) V) site.closed).wire e = .inr (.inl (.inr (.inl false))))
    (head : oldTail.head?=some (site.outsideEnd (.inr (.inl (.inr (.inr true))))))
    (rest : ExpandedForward site.net oldTail) : ExpandedForward site.net (site.outsideEnd e::(edge.principal++oldTail)) := by
  have arrives : site.net.wire (site.outsideEnd e)=.inl ⟨edge.app,edge.appCtx⟩ := by
    rw [site.outsideEnd_wire,arrival,geometry.appCtx]
    rfl
  have principal := (ExpandedForward.single (g:=site.net) (site.outsideEnd e)).splice rfl
    edge.principal_forward.expanded edge.principalStart (by
      change ExpandedDirection site.net (site.net.wire (site.outsideEnd e)) edge.funEnd
      rw [arrives]
      exact .node edge.app edge.appCtx edge.appFun
        (app_forward_roles (congrArg Label.sort edge.appLabel) edge.appCtx_role edge.appFun_role))
  have finish : ([site.outsideEnd e]++edge.principal).getLast?=some (site.net.wire edge.ctxEnd) := by
    simp only [List.getLast?_append,edge.principalEnd,Option.some_or,BetaEdge.ctxEnd]
  have starts : oldTail.head?=some (.inl ⟨edge.lam,edge.lamBody⟩) := by rw [geometry.body]; exact head
  exact principal.splice finish rest starts (by
    simpa only [Pairing.involutive] using ExpandedDirection.node (g:=site.net) edge.lam edge.lamCtx edge.lamBody
      (lam_forward_roles (congrArg Label.sort edge.lamLabel) edge.lamCtx_role edge.lamBody_role))

private theorem binding_direction {edge : BetaEdge site.net} (geometry : SiteBetaGeometry site edge)
    {e : Endpoint (cutFragment site.net (pathPartition (.beta i) V) site.closed)} {oldTail : List (Endpoint site.net)}
    (arrival : (cutFragment site.net (pathPartition (.beta i) V) site.closed).wire e = .inr (.inl (.inr (.inr false))))
    (head : oldTail.head?=some (site.outsideEnd (.inr (.inl (.inr (.inl true))))))
    (rest : ExpandedForward site.net oldTail) : ExpandedForward site.net (site.outsideEnd e::(edge.reverseRoute++oldTail)) := by
  have arrives : site.net.wire (site.outsideEnd e)=.inl ⟨edge.lam,edge.lamBind⟩ := by
    rw [site.outsideEnd_wire,arrival,geometry.binding]
    rfl
  have reversed := (ExpandedForward.single (g:=site.net) (site.outsideEnd e)).splice rfl
    edge.reverse_forward.expanded edge.reverse_start (by
      change ExpandedDirection site.net (site.net.wire (site.outsideEnd e)) edge.ctxEnd
      rw [arrives]
      exact .bindToCtx edge)
  have finish : ([site.outsideEnd e]++edge.reverseRoute).getLast?=some (site.net.wire edge.funEnd) := by
    simp only [List.getLast?_append,edge.reverse_finish,Option.some_or]
  have starts : oldTail.head?=some edge.argEnd := by rw [geometry.argument]; exact head
  exact reversed.splice finish rest starts (by
    simpa only [Pairing.involutive] using ExpandedDirection.funToArg (g:=site.net) edge)

theorem BetaPathResidual.forward {boundary : B → Bool} (flow : FlowBalance site.net boundary)
    {edge : BetaEdge site.net} (geometry : SiteBetaGeometry site edge) {raw old}
    (relation : BetaPathResidual site edge raw old) {a b : Context}
    (labels : PlugLabelling (cutFragment site.net (pathPartition (.beta i) V) site.closed) (Schema.beta i).right.net raw a b)
    (positive : RawOutsidePositive site flow raw) : ExpandedForward site.net old := by
  induction relation generalizing a b with
  | single e => exact .single _
  | @outside e f tail oldTail relation ih =>
    cases labels with
    | cons turn after =>
      have localTurn := outside_turn site turn
      have rest := ih after (by intro x mem; exact positive x (List.mem_cons_of_mem _ mem))
      have pe := positive e (by simp)
      have incoming : flowEndpoint _ (site.cut_flowBalance flow).nodes
          (Sum.elim boundary (fun f => !(site.frontierFlow flow f))) (site.cut_flowBalance flow).vertices
          ((cutFragment site.net (pathPartition (.beta i) V) site.closed).wire e)=false := by
        rw [(site.cut_flowBalance flow).wiring,pe]
        rfl
      have pair := (localTurn.prepend_forward_of_flow (site.cut_flowBalance flow) incoming e rfl (.single f)).outsideEnd site
      have head := relation.head site rfl
      obtain ⟨xs,same⟩ := List.head?_eq_some_iff.mp head
      rw [same] at rest ⊢
      cases pair.expanded with
      | cons direction last => exact .cons direction rest
  | context arrival relation ih =>
    cases labels with
    | cons turn after =>
      have same := enter_context site turn
      cases same
      cases after with
      | cons turn after =>
        have same := leave_context site turn
        cases same
        apply context_direction site geometry arrival (relation.head site rfl)
        apply ih after
        intro x mem
        exact positive x (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ mem))
  | binding arrival relation ih =>
    cases labels with
    | cons turn after =>
      have same := enter_context site turn
      cases same
      cases after with
      | cons turn after =>
        have same := leave_context site turn
        cases same
        apply binding_direction site geometry arrival (relation.head site rfl)
        apply ih after
        intro x mem
        exact positive x (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ mem))

theorem PathSite.beta_root_forward_ancestor {boundary : B → Bool}
    (flow : FlowBalance site.net boundary) (root : B) (rootPolarity : boundary root=true)
    {es : List (Endpoint site.reduce)} {a b : Context} (labels : Labelling site.reduce es a b)
    (rooted : es.head?=some (.inr (.inl root)))
    (last : Endpoint (cutFragment site.net (pathPartition (.beta i) V) site.closed))
    (finish : es.getLast?=some (AG.plugLeft _ _ last)) :
    ∃ (edge : BetaEdge site.net) (old : List (Endpoint site.net)),
      SiteBetaGeometry site edge ∧
      BetaPathResidual site edge (es.map (plugEnd _ _).invFun) old ∧
      ExpandedLabelling site.net old a b ∧ ExpandedForward site.net old ∧
      old.head?=some (.inr (.inl root)) ∧ old.getLast?=some (site.outsideEnd last) := by
  obtain ⟨edge,old,geometry,relation,oldLabels,start,endAt⟩ :=
    site.beta_root_ancestor flow root rootPolarity labels rooted last finish
  have rawLabels := labels.plug_decomposition _ _
  have rawRoot : ((es.map (plugEnd _ _).invFun).map (plugEnd _ _)).head?=some (.inr (.inl root)) := by
    rw [plug_decomposition_flatten]
    exact rooted
  have positive := rawLabels.outside_positive site flow root rootPolarity rawRoot
  exact ⟨edge,old,geometry,relation,oldLabels,relation.forward site flow geometry rawLabels positive,start,endAt⟩
end
end Lamping.AG
