import Lamping.Lamping.PathSiteBetaDirection
import Lamping.Lamping.ReducedOutsideProperRoles
namespace Lamping.AG
open Graph
section
variable {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K → Label signature} {i : Nat}
variable (site : PathSite (.beta i) kept (B:=B) (W:=W) (V:=V))

/-- Proper-source flow fixes every departure polarity without a root-path
assumption. In particular the two backwards RHS entrances cannot occur. -/
theorem WireExcursions.beta_proper_entries {boundary : B → Bool}
    (flow : FlowBalance site.net boundary) (root : B) (rootPositive : boundary root=true)
    {raw a b first role level}
    (path : WireExcursions (cutFragment site.net (pathPartition (.beta i) V) site.closed)
      (Schema.beta i).right.net raw a b)
    (head : (raw.map (plugEnd _ _)).head?=some first)
    (source : AtProperRole site.reduce root first role level) (outgoing : role.outgoing) :
    BetaEntriesForward site raw := by
  obtain ⟨changed,glue⟩ := site.reduce_flowBalance_glue flow
  have positives := ((path.labelling _ _).actual _ _).positive_departures changed (by
    intro e atHead
    rw [head] at atHead
    cases Option.some.inj atHead
    exact source.outgoing_flow outgoing changed.nodes boundary changed.vertices rootPositive)
  intro f mem
  have positive := positives ((plugEnd _ _) (.inr (.inr (.inl f)))) (List.mem_map_of_mem mem)
  rcases f with d | d <;> cases d
  · exact Or.inl rfl
  · change (!(changed.vertices (.inr (.inl true))))=true at positive
    rw [glue] at positive
    change (!(!(!true)))=true at positive
    cases positive
  · exact Or.inr rfl
  · change (!(changed.vertices (.inr (.inr true))))=true at positive
    rw [glue] at positive
    change (!(!(!true)))=true at positive
    cases positive

/-- Positivity of actual outside occurrences for an arbitrary outgoing proper
source. The cut values are inherited by the constructed replacement witness. -/
theorem PlugLabelling.proper_outside_positive {boundary : B → Bool}
    (flow : FlowBalance site.net boundary) (root : B) (rootPositive : boundary root=true)
    {raw a b first role level}
    (labels : PlugLabelling (cutFragment site.net (pathPartition (.beta i) V) site.closed)
      (Schema.beta i).right.net raw a b)
    (head : (raw.map (plugEnd _ _)).head?=some first)
    (source : AtProperRole site.reduce root first role level) (outgoing : role.outgoing) :
    RawOutsidePositive site flow raw := by
  obtain ⟨rhs⟩ := (Schema.beta i).flow_preservation (site.frontierFlow flow) (site.left_flowBalance flow)
  let c := cutFragment site.net (pathPartition (.beta i) V) site.closed
  let target := FlowBalance.plug c (Schema.beta i).right.net boundary (site.frontierFlow flow)
    (site.cut_flowBalance flow) rhs
  have positives := (labels.actual _ _).positive_departures target (by
    intro e atHead
    rw [head] at atHead
    cases Option.some.inj atHead
    exact source.outgoing_flow outgoing target.nodes boundary target.vertices rootPositive)
  intro e mem
  have positive := positives ((plugEnd c.label (Schema.beta i).right.net.label) (.inl e)) (List.mem_map_of_mem mem)
  change flowEndpoint (plug c (Schema.beta i).right.net) (Sum.elim (site.cut_flowBalance flow).nodes rhs.nodes)
    boundary (plugPolarity (site.frontierFlow flow) (site.cut_flowBalance flow).vertices rhs.vertices)
    ((plugEnd c.label (Schema.beta i).right.net.label) (.inl e)) = true at positive
  rw [flowEndpoint_plugLeft] at positive
  exact positive

/-- An actual beta path between proper endpoints has an ordered same-assignment
expanded ancestor, even when its source is not root-accessible. No transparency,
independence, generation or completion assumption is used. -/
theorem PathSite.beta_proper_ancestor {boundary : B → Bool}
    (flow : FlowBalance site.net boundary) (root : B) (rootPositive : boundary root=true)
    {es : List (Endpoint site.reduce)} {a b : Context} {first last sr tr m n}
    (labels : Labelling site.reduce es a b)
    (head : es.head?=some first) (finish : es.getLast?=some (site.reduce.wire last))
    (source : AtProperRole site.reduce root first sr m) (outgoing : sr.outgoing)
    (target : AtProperRole site.reduce root last tr n) :
    ∃ (edge : BetaEdge site.net) (old : List (Endpoint site.net)) (oldFirst oldLast : Endpoint site.net),
      SiteBetaGeometry site edge ∧
      BetaPathResidual site edge (es.map (plugEnd _ _).invFun) old ∧
      ExpandedLabelling site.net old a b ∧ ExpandedForward site.net old ∧
      old.head?=some oldFirst ∧ old.getLast?=some (site.net.wire oldLast) ∧
      AtProperRole site.net root oldFirst sr m ∧ AtProperRole site.net root oldLast tr n := by
  obtain ⟨start,startEq⟩ := site.reduced_proper_outside (fun e => nomatch e) source
  obtain ⟨stop,stopEq⟩ := site.reduced_proper_outside (fun e => nomatch e) target
  let c := cutFragment site.net (pathPartition (.beta i) V) site.closed
  let r := (Schema.beta i).right.net
  have startAt : es.head?=some (AG.plugLeft c r start) := head.trans (congrArg some startEq)
  have endAt : es.getLast?=some (AG.plugLeft c r (c.wire stop)) := by
    rw [finish,stopEq]
    change some ((plug c r).wire (AG.plugLeft c r stop)) = _
    rw [plugLeft_wire]
  have path := labels.wire_excursions c r start (c.wire stop) startAt endAt
  have rawHead : ((es.map (plugEnd c.label r.label).invFun).map (plugEnd c.label r.label)).head?=some first := by
    rw [plug_decomposition_flatten]
    exact head
  obtain ⟨edge,geometry⟩ := site.siteBetaGeometry_exists
  obtain ⟨old,relation,oldLabels⟩ := path.beta_lift site geometry
    (path.beta_proper_entries site flow root rootPositive rawHead source outgoing)
  have rawLabels := labels.plug_decomposition c r
  refine ⟨edge,old,site.outsideEnd start,site.outsideEnd stop,geometry,relation,oldLabels,
    relation.forward site flow geometry rawLabels
      (rawLabels.proper_outside_positive site flow root rootPositive rawHead source outgoing),?_,?_,?_,?_⟩
  · apply relation.head site
    rw [List.head?_map,startAt]
    exact congrArg some ((plugEnd c.label r.label).left_inv (.inl start))
  · rw [site.outsideEnd_wire]
    apply relation.finish site
    rw [List.getLast?_map,endAt]
    exact congrArg some ((plugEnd c.label r.label).left_inv (.inl (c.wire stop)))
  · exact site.reduced_outside_proper_role root start sr m (startEq ▸ source)
  · exact site.reduced_outside_proper_role root stop tr n (stopEq ▸ target)
end
end Lamping.AG

