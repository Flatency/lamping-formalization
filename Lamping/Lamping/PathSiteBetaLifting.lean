import Lamping.Lamping.PathSiteBetaAncestor
namespace Lamping.AG
open Graph
section
variable {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K → Label signature} {i : Nat}
variable (site : PathSite (.beta i) kept (B:=B) (W:=W) (V:=V))

/-- Only the four physical seams needed by the beta block lift. The route and
all its transparent segments remain those of the supplied actual BetaEdge. -/
structure SiteBetaGeometry (edge : BetaEdge site.net) : Prop where
  appCtx : (.inl ⟨edge.app,edge.appCtx⟩ : Endpoint site.net) = .inl ⟨.inr (.inl ()),.inr false⟩
  body : (.inl ⟨edge.lam,edge.lamBody⟩ : Endpoint site.net) = .inl ⟨.inr (.inr ()),.inr true⟩
  binding : (.inl ⟨edge.lam,edge.lamBind⟩ : Endpoint site.net) = .inl ⟨.inr (.inr ()),.inr false⟩
  argument : edge.argEnd = .inl ⟨.inr (.inl ()),.inr true⟩

theorem PathSite.siteBetaGeometry_exists : ∃ edge : BetaEdge site.net, SiteBetaGeometry site edge := by
  obtain ⟨edge,_,_,_,_,argument,binding,body,appCtx⟩ := site.betaEdge_identified
  exact ⟨edge,appCtx,body,binding,argument⟩

private theorem context_block {edge : BetaEdge site.net} (geometry : SiteBetaGeometry site edge)
    {e : Endpoint (cutFragment site.net (pathPartition (.beta i) V) site.closed)}
    {oldTail : List (Endpoint site.net)} {a b : Context}
    (arrival : (cutFragment site.net (pathPartition (.beta i) V) site.closed).wire e = .inr (.inl (.inr (.inl false))))
    (head : oldTail.head? = some (site.outsideEnd (.inr (.inl (.inr (.inr true))))))
    (labels : ExpandedLabelling site.net oldTail a b) :
    ExpandedLabelling site.net (site.outsideEnd e::(edge.principal++oldTail)) a b := by
  have arrives : site.net.wire (site.outsideEnd e) = .inl ⟨edge.app,edge.appCtx⟩ := by
    rw [site.outsideEnd_wire,arrival,geometry.appCtx]
    rfl
  have finish : [site.outsideEnd e].getLast? = some (site.net.wire (.inl ⟨edge.app,edge.appCtx⟩)) := by
    rw [←arrives,Pairing.involutive]
    rfl
  have starts : oldTail.head? = some (.inl ⟨edge.lam,edge.lamBody⟩) := by
    rw [geometry.body]
    exact head
  exact edge.body_with_loop_labeling [site.outsideEnd e] oldTail (.single _ _) finish starts labels

private theorem binding_block {edge : BetaEdge site.net} (geometry : SiteBetaGeometry site edge)
    {e : Endpoint (cutFragment site.net (pathPartition (.beta i) V) site.closed)}
    {oldTail : List (Endpoint site.net)} {a b : Context}
    (arrival : (cutFragment site.net (pathPartition (.beta i) V) site.closed).wire e = .inr (.inl (.inr (.inr false))))
    (head : oldTail.head? = some (site.outsideEnd (.inr (.inl (.inr (.inl true))))))
    (labels : ExpandedLabelling site.net oldTail a b) :
    ExpandedLabelling site.net (site.outsideEnd e::(edge.reverseRoute++oldTail)) a b := by
  have arrives : site.net.wire (site.outsideEnd e) = .inl ⟨edge.lam,edge.lamBind⟩ := by
    rw [site.outsideEnd_wire,arrival,geometry.binding]
    rfl
  have starts : oldTail.head? = some edge.argEnd := by
    rw [geometry.argument]
    exact head
  have reversed := (ExpandedLabelling.single (g:=site.net) (site.outsideEnd e) a).splice rfl
    (edge.reverse_labeling a).expanded edge.reverse_start
    (by
      change ExpandedTurn site.net (site.net.wire (site.outsideEnd e)) edge.ctxEnd a a
      rw [arrives]
      exact ExpandedTurn.bindToCtx edge a)
  have finish : ([site.outsideEnd e]++edge.reverseRoute).getLast? = some (site.net.wire edge.funEnd) := by
    simp only [List.getLast?_append,edge.reverse_finish,Option.some_or]
  have whole := reversed.splice finish labels starts
    (by simpa only [Pairing.involutive] using ExpandedTurn.funToArg (g:=site.net) edge a)
  exact whole

/-- Actual finite beta excursions lift to one ordered old expanded path with
the same input and output contexts. Here entrance direction is explicit;
the rooted theorem below derives it from structural source flow. -/
theorem WireExcursions.beta_lift {edge : BetaEdge site.net} (geometry : SiteBetaGeometry site edge)
    {raw a b} (path : WireExcursions (cutFragment site.net (pathPartition (.beta i) V) site.closed)
      (Schema.beta i).right.net raw a b) (directions : BetaEntriesForward site raw) :
    ∃ old, BetaPathResidual site edge raw old ∧ ExpandedLabelling site.net old a b := by
  induction path with
  | single e a => exact ⟨_,.single e,.single _ _⟩
  | @outside e f tail a b d turn rest ih =>
    obtain ⟨old,relation,labels⟩ := ih (by
      intro x mem
      exact directions x (List.mem_cons_of_mem _ mem))
    refine ⟨_,.outside relation,?_⟩
    have head := relation.head site rfl
    obtain ⟨xs,same⟩ := List.head?_eq_some_iff.mp head
    rw [same] at labels ⊢
    have actual := turn.outsideEnd site
    rw [←site.outsideEnd_wire] at actual
    exact .cons (.ordinary actual) labels
  | @through e f tail a b arrival rest ih =>
    have entry := directions f (by simp)
    obtain ⟨old,relation,labels⟩ := ih (by
      intro x mem
      exact directions x (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ mem)))
    rcases entry with entry | entry
    · subst f
      exact ⟨_,.context arrival relation,context_block site geometry arrival (relation.head site rfl) labels⟩
    · subst f
      exact ⟨_,.binding arrival relation,binding_block site geometry arrival (relation.head site rfl) labels⟩

theorem WireExcursions.beta_root_lift {boundary : B → Bool}
    (flow : FlowBalance site.net boundary) (root : B) (rootPolarity : boundary root=true)
    {raw a b} (path : WireExcursions (cutFragment site.net (pathPartition (.beta i) V) site.closed)
      (Schema.beta i).right.net raw a b)
    (rooted : (raw.map (plugEnd _ _)).head?=some (.inr (.inl root))) :
    ∃ (edge : BetaEdge site.net) (old : List (Endpoint site.net)),
      SiteBetaGeometry site edge ∧ BetaPathResidual site edge raw old ∧ ExpandedLabelling site.net old a b := by
  obtain ⟨edge,geometry⟩ := site.siteBetaGeometry_exists
  obtain ⟨old,relation,labels⟩ := path.beta_lift site geometry (path.beta_entries_forward site flow root rootPolarity rooted)
  exact ⟨edge,old,geometry,relation,labels⟩

/-- Whole physical beta ancestor, with the designated boundary root, literal
residual relation, retained outside last segment, and unchanged A/B labels.
This establishes semantic path transport, not generated/coherent membership. -/
theorem PathSite.beta_root_ancestor {boundary : B → Bool}
    (flow : FlowBalance site.net boundary) (root : B) (rootPolarity : boundary root=true)
    {es : List (Endpoint site.reduce)} {a b : Context} (labels : Labelling site.reduce es a b)
    (rooted : es.head?=some (.inr (.inl root)))
    (last : Endpoint (cutFragment site.net (pathPartition (.beta i) V) site.closed))
    (finish : es.getLast? = some (AG.plugLeft _ _ last)) :
    ∃ (edge : BetaEdge site.net) (old : List (Endpoint site.net)),
      SiteBetaGeometry site edge ∧
      BetaPathResidual site edge (es.map (plugEnd _ _).invFun) old ∧
      ExpandedLabelling site.net old a b ∧
      old.head?=some (.inr (.inl root)) ∧ old.getLast?=some (site.outsideEnd last) := by
  let c := cutFragment site.net (pathPartition (.beta i) V) site.closed
  let r := (Schema.beta i).right.net
  let first : Endpoint c := .inr (.inl (.inl root))
  have path := labels.wire_excursions c r first last rooted finish
  have start : ((es.map (plugEnd c.label r.label).invFun).map (plugEnd c.label r.label)).head? =
      some (.inr (.inl root)) := by
    rw [plug_decomposition_flatten]
    exact rooted
  obtain ⟨edge,old,geometry,relation,oldLabels⟩ := path.beta_root_lift site flow root rootPolarity start
  refine ⟨edge,old,geometry,relation,oldLabels,?_,?_⟩
  · apply relation.head site (first:=first)
    rw [List.head?_map,rooted]
    rfl
  · apply relation.finish site
    rw [List.getLast?_map,finish]
    exact congrArg some ((plugEnd c.label r.label).left_inv (.inl last))
end
end Lamping.AG
