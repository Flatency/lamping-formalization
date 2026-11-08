import Lamping.Lamping.PathSiteBetaCoherent
namespace Lamping.AG
open Graph
section
variable {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K → Label signature} {i : Nat}
variable (site : PathSite (.beta i) kept (B:=B) (W:=W) (V:=V))

private theorem reflect_outside {x y : Endpoint (cutFragment site.net (pathPartition (.beta i) V) site.closed)}
    {a b originalA originalB : Context}
    (shape : LabelledTurn (cutFragment site.net (pathPartition (.beta i) V) site.closed) x y originalA originalB)
    (turn : ExpandedTurn site.net (site.outsideEnd x) (site.outsideEnd y) a b) :
    LabelledTurn (cutFragment site.net (pathPartition (.beta i) V) site.closed) x y a b := by
  cases shape with
  | node node p q rule =>
    change ExpandedTurn site.net (.inl ⟨.inl node,p⟩) (.inl ⟨.inl node,q⟩) a b at turn
    have ordinary := turn.ordinary_of_shape (LabelledTurn.node (g:=site.net) (.inl node) p q rule)
    cases ordinary with
    | node node p q actual => exact .node _ _ _ actual
  | transparent vertex direction context =>
    change ExpandedTurn site.net (.inr (.inr (.inl vertex,direction)))
      (.inr (.inr (.inl vertex,!direction))) a b at turn
    have ordinary := turn.ordinary_of_shape (LabelledTurn.transparent (g:=site.net) (.inl vertex) direction originalA)
    cases ordinary
    exact .transparent vertex direction a

private theorem peel_identity {g : Net signature K B W} {e f : Endpoint g}
    {route tail : List (Endpoint g)} {a b : Context}
    (head : tail.head?=some f)
    (prefixLabels : ExpandedLabelling g (e::(route++[f])) a a)
    (labels : ExpandedLabelling g (e::(route++tail)) a b) : ExpandedLabelling g tail a b := by
  obtain ⟨suffix,tailSplit⟩ := List.head?_eq_some_iff.mp head
  rw [tailSplit] at labels ⊢
  have labels' : ExpandedLabelling g ((e::route)++f::suffix) a b := by simpa only [List.cons_append] using labels
  obtain ⟨middle,before,after⟩ := labels'.split_segment
  have prefix' : ExpandedLabelling g ((e::route)++[f]) a a := by simpa only [List.cons_append] using prefixLabels
  have equal := before.output_unique prefix'
  rw [equal] at after
  exact after

private theorem context_identity {edge : BetaEdge site.net} (geometry : SiteBetaGeometry site edge)
    {e : Endpoint (cutFragment site.net (pathPartition (.beta i) V) site.closed)}
    (arrival : (cutFragment site.net (pathPartition (.beta i) V) site.closed).wire e =
      .inr (.inl (.inr (.inl false)))) (a : Context) :
    ExpandedLabelling site.net (site.outsideEnd e::(edge.principal++
      [site.outsideEnd (.inr (.inl (.inr (.inr true))))])) a a := by
  have arrives : site.net.wire (site.outsideEnd e)=.inl ⟨edge.app,edge.appCtx⟩ := by
    rw [site.outsideEnd_wire,arrival,geometry.appCtx]; rfl
  have finish : [site.outsideEnd e].getLast?=some (site.net.wire (.inl ⟨edge.app,edge.appCtx⟩)) := by
    rw [←arrives,Pairing.involutive]; rfl
  have labels := edge.body_entry_labeling [site.outsideEnd e] (.single _ a) finish
  have body : site.outsideEnd (.inr (.inl (.inr (.inr true)))) = .inl ⟨edge.lam,edge.lamBody⟩ := by
    rw [geometry.body]; rfl
  simpa only [List.singleton_append,List.append_assoc,body] using labels

private theorem binding_identity {edge : BetaEdge site.net} (geometry : SiteBetaGeometry site edge)
    {e : Endpoint (cutFragment site.net (pathPartition (.beta i) V) site.closed)}
    (arrival : (cutFragment site.net (pathPartition (.beta i) V) site.closed).wire e =
      .inr (.inl (.inr (.inr false)))) (a : Context) :
    ExpandedLabelling site.net (site.outsideEnd e::(edge.reverseRoute++
      [site.outsideEnd (.inr (.inl (.inr (.inl true))))])) a a := by
  have arrives : site.net.wire (site.outsideEnd e)=.inl ⟨edge.lam,edge.lamBind⟩ := by
    rw [site.outsideEnd_wire,arrival,geometry.binding]; rfl
  have labels := (ExpandedLabelling.single (g:=site.net) (site.outsideEnd e) a).splice rfl
    (edge.reverse_labeling a).expanded edge.reverse_start (by
      change ExpandedTurn site.net (site.net.wire (site.outsideEnd e)) edge.ctxEnd a a
      rw [arrives]; exact .bindToCtx edge a)
  have finish : ([site.outsideEnd e]++edge.reverseRoute).getLast?=some (site.net.wire edge.funEnd) := by
    simp only [List.getLast?_append,edge.reverse_finish,Option.some_or]
  have result := labels.splice finish (.single edge.argEnd a) rfl (by
    simpa only [Pairing.involutive] using ExpandedTurn.funToArg (g:=site.net) edge a)
  have argument : site.outsideEnd (.inr (.inl (.inr (.inl true))))=edge.argEnd := by
    rw [geometry.argument]; rfl
  simpa only [List.singleton_append,List.append_assoc,argument] using result

private theorem left_turn {c : Net signature K (B⊕(Bool⊕Bool)) W}
    {r : Net signature Empty (Bool⊕Bool) Empty} {x y : Endpoint c} {a b : Context}
    (turn : PlugTurn c r (.inl x) (.inl y) a b) : LabelledTurn c x y a b := by
  cases turn with | left actual => exact actual

private theorem enter_equal {c : Net signature K (B⊕(Bool⊕Bool)) W}
    {r : Net signature Empty (Bool⊕Bool) Empty} {x : Endpoint c} {y : Endpoint r} {a b : Context}
    (turn : PlugTurn c r (.inl x) (.inr y) a b) : a=b := by cases turn; rfl
private theorem leave_equal {c : Net signature K (B⊕(Bool⊕Bool)) W}
    {r : Net signature Empty (Bool⊕Bool) Empty} {x : Endpoint r} {y : Endpoint c} {a b : Context}
    (turn : PlugTurn c r (.inr x) (.inl y) a b) : a=b := by cases turn; rfl

/-- Contract any new assignment on the fixed literal ancestor. The original
reduced labelling supplies only outside physical turn shapes. Its contexts
can differ completely from the assignment being contracted. -/
theorem BetaPathResidual.contract {edge : BetaEdge site.net} (geometry : SiteBetaGeometry site edge)
    {raw old : List _} (relation : BetaPathResidual site edge raw old)
    {originalA originalB a b : Context}
    (shape : PlugLabelling (cutFragment site.net (pathPartition (.beta i) V) site.closed)
      (Schema.beta i).right.net raw originalA originalB)
    (labels : ExpandedLabelling site.net old a b) :
    PlugLabelling (cutFragment site.net (pathPartition (.beta i) V) site.closed)
      (Schema.beta i).right.net raw a b := by
  induction relation generalizing originalA originalB a b with
  | single e => cases labels; exact .single _ _
  | @outside e f tail oldTail relation ih =>
    cases shape with
    | cons turn after =>
      have oldHead := relation.head site rfl
      obtain ⟨xs,same⟩ := List.head?_eq_some_iff.mp oldHead
      rw [same] at labels
      cases labels with
      | cons actual rest =>
        have localShape := left_turn turn
        have localActual := reflect_outside site localShape (by
          rw [←site.outsideEnd_wire]; exact actual)
        exact .cons (.left localActual) (ih after (by rw [same]; exact rest))
  | @context e tail oldTail arrival relation ih =>
    cases shape with
    | cons turn after =>
      cases enter_equal turn
      cases after with
      | cons turn after =>
        cases leave_equal turn
        have rest := peel_identity (relation.head site rfl) (context_identity site geometry arrival a) labels
        have changed := ih after rest
        apply PlugLabelling.cons
        · change PlugTurn _ _ (.inl ((cutFragment site.net (pathPartition (.beta i) V) site.closed).wire e)) _ a a
          rw [arrival]; exact .enter _ a
        · exact .cons (.leave _ a) changed
  | @binding e tail oldTail arrival relation ih =>
    cases shape with
    | cons turn after =>
      cases enter_equal turn
      cases after with
      | cons turn after =>
        cases leave_equal turn
        have rest := peel_identity (relation.head site rfl) (binding_identity site geometry arrival a) labels
        have changed := ih after rest
        apply PlugLabelling.cons
        · change PlugTurn _ _ (.inl ((cutFragment site.net (pathPartition (.beta i) V) site.closed).wire e)) _ a a
          rw [arrival]; exact .enter _ a
        · exact .cons (.leave _ a) changed

theorem BetaPathResidual.contract_actual {edge : BetaEdge site.net} (geometry : SiteBetaGeometry site edge)
    {es : List (Endpoint site.reduce)} {old : List (Endpoint site.net)}
    (relation : BetaPathResidual site edge (es.map (plugEnd _ _).invFun) old)
    {originalA originalB a b : Context}
    (shape : Labelling site.reduce es originalA originalB)
    (labels : ExpandedLabelling site.net old a b) : Labelling site.reduce es a b := by
  have raw := relation.contract site geometry (shape.plug_decomposition _ _) labels
  have actual := raw.actual _ _
  rw [plug_decomposition_flatten] at actual
  exact actual

/-- A genuine beta-step total-input consequence at an actual retained typed
terminal. It supplies only root-input existence, not tail synchronization,
Nesting/Transparency, or full Independence preservation. -/
theorem PathSite.beta_root_inputs {boundary : B → Bool}
    (flow : FlowBalance site.net boundary) (root : B) (rootPolarity : boundary root=true)
    (invariants : OrdinaryPathInvariants site.net root)
    {es : List (Endpoint site.reduce)} {input output : Context}
    (labels : Labelling site.reduce es input output) (rooted : es.head?=some (.inr (.inl root)))
    (last : Endpoint (cutFragment site.net (pathPartition (.beta i) V) site.closed))
    (finish : es.getLast?=some (AG.plugLeft _ _ last))
    (role : ProperRole) (level : Nat)
    (atTerminal : AtProperRole site.net root (site.net.wire (site.outsideEnd last)) role level)
    (incoming : role.incoming) :
    ∀ requested : Context, ∃ result,Labelling site.reduce es requested result := by
  obtain ⟨edge,old,geometry,relation,_,_,_,allInputs⟩ := site.beta_root_typed_uniform_ancestor flow root
    rootPolarity invariants labels rooted last finish role level atTerminal incoming
  intro requested
  obtain ⟨result,coherent⟩ := allInputs requested
  exact ⟨result,relation.contract_actual site geometry labels (coherent.labelling _)⟩

/-- Incoming proper roles at an actual retained reduced endpoint reflect to
the old endpoint through the actual cut/plug wiring. -/
theorem PathSite.beta_outside_incoming (root : B)
    (last : Endpoint (cutFragment site.net (pathPartition (.beta i) V) site.closed))
    (role : ProperRole) (level : Nat)
    (atTerminal : AtProperRole site.reduce root
      (site.reduce.wire (AG.plugLeft _ _ last)) role level) (incoming : role.incoming) :
    AtProperRole site.net root (site.net.wire (site.outsideEnd last)) role level := by
  have wire := plugLeft_wire (cutFragment site.net (pathPartition (.beta i) V) site.closed)
    (Schema.beta i).right.net last
  change site.reduce.wire (AG.plugLeft _ _ last)=AG.plugLeft _ _
    ((cutFragment site.net (pathPartition (.beta i) V) site.closed).wire last) at wire
  rw [wire] at atTerminal
  rw [site.outsideEnd_wire]
  generalize (cutFragment site.net (pathPartition (.beta i) V) site.closed).wire last = endpoint at atTerminal ⊢
  rcases endpoint with ⟨node,p⟩ | ((boundary | frontier) | ⟨vertex,direction⟩)
  · cases atTerminal with
    | appCtx node p level lab port => exact AtProperRole.appCtx (g:=site.net) (root:=root) (.inl node) p level lab port
    | appFun node p level lab port => exact AtProperRole.appFun (g:=site.net) (root:=root) (.inl node) p level lab port
    | appArg node p level lab port => exact AtProperRole.appArg (g:=site.net) (root:=root) (.inl node) p level lab port
    | lamCtx node p level lab port => exact AtProperRole.lamCtx (g:=site.net) (root:=root) (.inl node) p level lab port
    | lamBody node p level lab port => exact AtProperRole.lamBody (g:=site.net) (root:=root) (.inl node) p level lab port
    | lamBind node p level lab port => exact AtProperRole.lamBind (g:=site.net) (root:=root) (.inl node) p level lab port
  · cases atTerminal
    exact False.elim incoming
  · cases atTerminal
  · cases atTerminal

theorem PathSite.beta_root_inputs_at_reduced {boundary : B → Bool}
    (flow : FlowBalance site.net boundary) (root : B) (rootPolarity : boundary root=true)
    (invariants : OrdinaryPathInvariants site.net root)
    {es : List (Endpoint site.reduce)} {input output : Context}
    (labels : Labelling site.reduce es input output) (rooted : es.head?=some (.inr (.inl root)))
    (last : Endpoint (cutFragment site.net (pathPartition (.beta i) V) site.closed))
    (finish : es.getLast?=some (AG.plugLeft _ _ last))
    (role : ProperRole) (level : Nat)
    (atTerminal : AtProperRole site.reduce root (site.reduce.wire (AG.plugLeft _ _ last)) role level)
    (incoming : role.incoming) :
    ∀ requested : Context, ∃ result,Labelling site.reduce es requested result :=
  site.beta_root_inputs flow root rootPolarity invariants labels rooted last finish role level
    (site.beta_outside_incoming root last role level atTerminal incoming) incoming

private theorem incoming_kept {root : B} {terminal : Endpoint site.reduce} {role : ProperRole} {level : Nat}
    (atTerminal : AtProperRole site.reduce root terminal role level) (incoming : role.incoming) :
    ∃ (node : K) (p : Port (kept node).sort),terminal=.inl ⟨.inl node,p⟩ := by
  cases atTerminal with
  | root => exact False.elim incoming
  | appCtx node p level lab port => cases node with
    | inl node => exact ⟨node,p,rfl⟩
    | inr node => exact nomatch node
  | appFun node p level lab port => exact False.elim incoming
  | appArg node p level lab port => exact False.elim incoming
  | lamCtx node p level lab port => cases node with
    | inl node => exact ⟨node,p,rfl⟩
    | inr node => exact nomatch node
  | lamBody node p level lab port => exact False.elim incoming
  | lamBind node p level lab port => cases node with
    | inl node => exact ⟨node,p,rfl⟩
    | inr node => exact nomatch node

/-- The actual beta root-input component of Independence preservation.
Every metadata premise refers to the reduced graph itself; the retained
outside endpoint and its old typed role are derived from actual wiring. -/
theorem PathSite.beta_typed_root_inputs {boundary : B → Bool}
    (flow : FlowBalance site.net boundary) (root : B) (rootPolarity : boundary root=true)
    (invariants : OrdinaryPathInvariants site.net root)
    {es : List (Endpoint site.reduce)} {input output : Context}
    (labels : Labelling site.reduce es input output) (rooted : es.head?=some (.inr (.inl root)))
    (terminal : Endpoint site.reduce) (role : ProperRole) (level : Nat)
    (finish : es.getLast?=some (site.reduce.wire terminal))
    (atTerminal : AtProperRole site.reduce root terminal role level) (incoming : role.incoming) :
    ∀ requested : Context, ∃ result,Labelling site.reduce es requested result := by
  obtain ⟨node,p,same⟩ := incoming_kept site atTerminal incoming
  let c := cutFragment site.net (pathPartition (.beta i) V) site.closed
  let r := (Schema.beta i).right.net
  let last : Endpoint c := c.wire (.inl ⟨node,p⟩)
  have represented : site.reduce.wire terminal=AG.plugLeft c r last := by
    rw [same]
    exact plugLeft_wire c r (.inl ⟨node,p⟩)
  have lastFinish : es.getLast?=some (AG.plugLeft c r last) := finish.trans (congrArg some represented)
  have actualRole : AtProperRole site.reduce root (site.reduce.wire (AG.plugLeft c r last)) role level := by
    rw [←represented,Pairing.involutive]
    exact atTerminal
  exact site.beta_root_inputs_at_reduced flow root rootPolarity invariants labels rooted last lastFinish
    role level actualRole incoming
end
end Lamping.AG


