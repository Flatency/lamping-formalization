import Lamping.Lambda.BetaIncidencePreimages
import Lamping.Lambda.UncreatedChainTransport
import Lamping.Lamping.ChainSyntaxIncidence
import Lamping.Lambda.PrerequisiteVertexRanks
namespace Lamping.AG
open Graph Lambda Lambda.Labelled

private theorem edge_preimage_forward
    (origins : BetaEdgePreimages body argument site edges oldEdges) (member : edge∈edges) :
    ∃ old,old∈oldEdges ∧BetaNodePreimage body argument site edge old := by
  induction origins with
  | nil => cases member
  | @cons first oldFirst rest oldRest origin tail ih =>
    rcases List.mem_cons.mp member with equal | below
    · subst edge;exact ⟨oldFirst,List.mem_cons_self,origin⟩
    · obtain ⟨old,inside,related⟩ := ih below
      exact ⟨old,List.mem_cons_of_mem _ inside,related⟩

private theorem edge_preimage_backward
    (origins : BetaEdgePreimages body argument site edges oldEdges) (member : old∈oldEdges) :
    ∃ edge,edge∈edges ∧BetaNodePreimage body argument site edge old := by
  induction origins with
  | nil => cases member
  | @cons first oldFirst rest oldRest origin tail ih =>
    rcases List.mem_cons.mp member with equal | below
    · subst old;exact ⟨first,List.mem_cons_self,origin⟩
    · obtain ⟨edge,inside,related⟩ := ih below
      exact ⟨edge,List.mem_cons_of_mem _ inside,related⟩

private theorem tail_not_old_head
    (origins : BetaEdgePreimages body argument site edges oldEdges)
    (absent : oldHead∉oldEdges) (member : edge∈edges)
    (origin : BetaNodePreimage body argument site edge oldHead) : False := by
  obtain ⟨old,inside,related⟩ := edge_preimage_forward origins member
  have same := origin.unique related
  exact absent (same ▸ inside)

private theorem edge_preimage_injective
    (origins : BetaEdgePreimages body argument site edges oldEdges) (nodup : oldEdges.Nodup)
    (leftMember : left∈edges) (rightMember : right∈edges)
    (leftOrigin : BetaNodePreimage body argument site left old)
    (rightOrigin : BetaNodePreimage body argument site right old) : left=right := by
  induction origins with
  | nil => cases leftMember
  | @cons first oldFirst rest oldRest headOrigin tail ih =>
    obtain ⟨absent,tailNodup⟩ := List.nodup_cons.mp nodup
    rcases List.mem_cons.mp leftMember with leftEqual | leftBelow
    · subst left
      have oldEq : old=oldFirst := leftOrigin.unique headOrigin
      subst old
      rcases List.mem_cons.mp rightMember with rightEqual | rightBelow
      · exact rightEqual.symm
      · exact False.elim (tail_not_old_head tail absent rightBelow rightOrigin)
    · rcases List.mem_cons.mp rightMember with rightEqual | rightBelow
      · subst right
        have oldEq : old=oldFirst := rightOrigin.unique headOrigin
        subst old
        exact False.elim (tail_not_old_head tail absent leftBelow leftOrigin)
      · exact ih tailNodup leftBelow rightBelow

private noncomputable def bij_of_bijective {A B : Type} (f : A →B)
    (injective : Function.Injective f) (surjective : Function.Surjective f) : Bij A B where
  toFun := f
  invFun := fun b=>Classical.choose (surjective b)
  left_inv := fun a=>injective (Classical.choose_spec (surjective (f a)))
  right_inv := fun b=>Classical.choose_spec (surjective b)

private noncomputable def incidence_iso_of_edges
    {left right : EdgeLabelledIncidence} (edges : Bij left.Edge right.Edge)
    (vertices : left.Vertex →right.Vertex) (injective : Function.Injective vertices)
    (sources : ∀ edge,vertices (left.source edge)=right.source (edges edge))
    (targets : ∀ edge,vertices (left.target edge)=right.target (edges edge))
    (labels : ∀ edge,left.label edge=right.label (edges edge))
    (incident : ∀ vertex,∃ edge,vertex=right.source edge ∨vertex=right.target edge) :
    ChainIncidenceIso left right := by
  have surjective : Function.Surjective vertices := by
    intro vertex
    obtain ⟨edge,endpoint⟩ := incident vertex
    rcases endpoint with source | target
    · refine ⟨left.source (edges.invFun edge),?_⟩
      rw [sources,edges.right_inv,source]
    · refine ⟨left.target (edges.invFun edge),?_⟩
      rw [targets,edges.right_inv,target]
  exact ⟨bij_of_bijective vertices injective surjective,edges,sources,targets,labels⟩
private theorem chain_edge_lookup (chain : PrerequisiteChain term start edges)
    (member : edge∈edges) : ∃ current,term.subterm edge=some current := by
  rcases chain.eligible member with ⟨parent,stamp,fn,arg,equal,lookup⟩ | ⟨stamp,body,lookup⟩
  · refine ⟨fn,?_⟩
    rw [equal,LTerm.subterm_append,lookup];cases fn <;> rfl
  · exact ⟨_,lookup⟩

private noncomputable def preimage_edge_bij
    {source target body argument : LTerm} {site start oldStart : Path} {edges oldEdges : List Path}
    (sourceClosed : Closed source.erase) (targetClosed : Closed target.erase)
    (chain : PrerequisiteChain target start edges) (oldChain : PrerequisiteChain source oldStart oldEdges)
    (origins : BetaEdgePreimages body argument site edges oldEdges) :
    {bijection : Bij (chainSyntaxIncidence target targetClosed edges).Edge
      (chainSyntaxIncidence source sourceClosed oldEdges).Edge //
      ∀ edge,BetaNodePreimage body argument site edge.val.val (bijection edge).val.val} := by
  let left := chainSyntaxIncidence target targetClosed edges
  let right := chainSyntaxIncidence source sourceClosed oldEdges
  have exists_image (edge : left.Edge) : ∃ old : right.Edge,
      BetaNodePreimage body argument site edge.val.val old.val.val := by
    obtain ⟨old,member,related⟩ := edge_preimage_forward origins edge.property
    obtain ⟨node,lookup⟩ := chain_edge_lookup oldChain member
    have valid : (subtermAt source.erase old).isSome := by rw [←LTerm.erase_subterm,lookup];rfl
    exact ⟨⟨⟨old,valid⟩,member⟩,related⟩
  let image : left.Edge →right.Edge := fun edge=>Classical.choose (exists_image edge)
  have image_spec (edge : left.Edge) : BetaNodePreimage body argument site edge.val.val (image edge).val.val :=
    Classical.choose_spec (exists_image edge)
  have injective : Function.Injective image := by
    intro first second same
    have equal := congrArg (fun edge : right.Edge=>edge.val.val) same
    change (image first).val.val=(image second).val.val at equal
    have related : BetaNodePreimage body argument site second.val.val (image first).val.val := by
      rw [equal];exact image_spec second
    exact Subtype.ext (Subtype.ext (edge_preimage_injective origins oldChain.nodup first.property second.property
      (image_spec first) related))
  have surjective : Function.Surjective image := by
    intro old
    obtain ⟨edge,member,related⟩ := edge_preimage_backward origins old.property
    obtain ⟨node,lookup⟩ := chain_edge_lookup chain member
    have valid : (subtermAt target.erase edge).isSome := by rw [←LTerm.erase_subterm,lookup];rfl
    let actual : left.Edge := ⟨⟨edge,valid⟩,member⟩
    exact ⟨actual,Subtype.ext (Subtype.ext ((image_spec actual).unique related))⟩
  exact ⟨bij_of_bijective image injective surjective,image_spec⟩
private theorem proper_prerequisite_incident {target : LTerm} (closed : Closed target.erase)
    {edges : List Path} {position : SyntaxIncidence.ProperPosition target}
    (incident : (syntaxIncidenceGraph target closed).Incident (fun edge=>edge.val∈edges) (some position)) :
    PrerequisiteIncident target edges position.val := by
  obtain ⟨edge,chosen,endpoint⟩ := incident
  refine ⟨position.property,edge.val,chosen,?_⟩
  rcases endpoint with source | targetEnd
  · left
    change some position=SyntaxIncidence.source target edge at source
    have actual := SyntaxIncidence.source_spec target edge
    rw [←source] at actual
    exact actual
  · right
    change some position=SyntaxIncidence.target target closed edge at targetEnd
    have actual := SyntaxIncidence.target_spec target closed edge
    rw [←targetEnd] at actual
    exact actual

private theorem vertex_preimage_injective
    {source target body argument : LTerm} {site start : Path} {edges : List Path} {beta alpha : Label}
    (targetClosed : Closed target.erase) (step : StepAt site source target)
    (redex : source.subterm site=some (.app beta (.lam alpha body) argument))
    (chain : PrerequisiteChain target start edges)
    (uncreated : ∀ edge∈edges,¬BetaCreatedIncoming body site edge)
    {left right : SyntaxIncidence.Vertex target} {old : SyntaxIncidence.Vertex source}
    (leftIncident : (syntaxIncidenceGraph target targetClosed).Incident (fun edge=>edge.val∈edges) left)
    (rightIncident : (syntaxIncidenceGraph target targetClosed).Incident (fun edge=>edge.val∈edges) right)
    (leftOrigin : BetaVertexPreimage body argument site source target left old)
    (rightOrigin : BetaVertexPreimage body argument site source target right old) : left=right := by
  cases leftOrigin with
  | boundary => cases rightOrigin;rfl
  | proper leftOrigin =>
    cases rightOrigin with
    | proper rightOrigin =>
      exact congrArg some (Subtype.ext (step.incident_preimage_injective redex chain uncreated
        (proper_prerequisite_incident targetClosed leftIncident)
        (proper_prerequisite_incident targetClosed rightIncident) leftOrigin rightOrigin))

/-- Construct the actual directed edge-induced isomorphism from real
all-old chains and their pointwise occurrence preimages. Edge bijectivity
uses the old chain's distinct occurrences; vertex injectivity uses actual
incident subchain ranks and constructors. Both endpoint maps are derived.
The returned maps retain their literal beta preimage specifications. -/
noncomputable def uncreated_chain_iso
    {source target body argument : LTerm} {site start oldStart : Path} {edges oldEdges : List Path} {beta alpha : Label}
    (sourceClosed : Closed source.erase) (targetClosed : Closed target.erase)
    (step : StepAt site source target)
    (redex : source.subterm site=some (.app beta (.lam alpha body) argument))
    (chain : PrerequisiteChain target start edges) (oldChain : PrerequisiteChain source oldStart oldEdges)
    (uncreated : ∀ edge∈edges,¬BetaCreatedIncoming body site edge)
    (origins : BetaEdgePreimages body argument site edges oldEdges) :
    {iso : ChainIncidenceIso (chainSyntaxIncidence target targetClosed edges)
      (chainSyntaxIncidence source sourceClosed oldEdges) //
      (∀ edge,BetaNodePreimage body argument site edge.val.val (iso.edges edge).val.val) ∧
      ∀ vertex,BetaVertexPreimage body argument site source target vertex.val (iso.vertices vertex).val} := by
  let left := chainSyntaxIncidence target targetClosed edges
  let right := chainSyntaxIncidence source sourceClosed oldEdges
  obtain ⟨edgeBij,edgeSpec⟩ := preimage_edge_bij sourceClosed targetClosed chain oldChain origins
  have source_related (edge : left.Edge) :
      BetaVertexPreimage body argument site source target (left.source edge).val (right.source (edgeBij edge)).val := by
    obtain ⟨node,lookup⟩ := chain_edge_lookup chain edge.property
    obtain ⟨oldVertex,oldEndpoint,related⟩ := step.beta_incidence_source_preimage redex
      (edgeSpec edge) lookup (uncreated _ edge.property) (SyntaxIncidence.source_spec target edge.val)
    have same := SyntaxIncidence.Source.unique oldEndpoint (SyntaxIncidence.source_spec source (edgeBij edge).val)
    rw [same] at related
    exact related
  have target_related (edge : left.Edge) :
      BetaVertexPreimage body argument site source target (left.target edge).val (right.target (edgeBij edge)).val := by
    obtain ⟨oldVertex,oldEndpoint,related⟩ := step.beta_incidence_target_preimage redex
      (edgeSpec edge) (SyntaxIncidence.target_spec target targetClosed edge.val)
    have same := SyntaxIncidence.Target.unique oldEndpoint
      (SyntaxIncidence.target_spec source sourceClosed (edgeBij edge).val)
    rw [same] at related
    exact related
  have exists_vertex (vertex : left.Vertex) : ∃ old : right.Vertex,
      BetaVertexPreimage body argument site source target vertex.val old.val := by
    obtain ⟨edge,chosen,endpoint⟩ := vertex.property
    let selected : left.Edge := ⟨edge,chosen⟩
    rcases endpoint with source | targetEnd
    · refine ⟨right.source (edgeBij selected),?_⟩
      rw [source];exact source_related selected
    · refine ⟨right.target (edgeBij selected),?_⟩
      rw [targetEnd];exact target_related selected
  let image : left.Vertex →right.Vertex := fun vertex=>Classical.choose (exists_vertex vertex)
  have image_spec (vertex : left.Vertex) : BetaVertexPreimage body argument site source target vertex.val (image vertex).val :=
    Classical.choose_spec (exists_vertex vertex)
  have injective : Function.Injective image := by
    intro first second same
    have secondOrigin := image_spec second
    rw [←same] at secondOrigin
    exact Subtype.ext (vertex_preimage_injective targetClosed step redex chain uncreated
      first.property second.property (image_spec first) secondOrigin)
  have sourceEq (edge : left.Edge) : image (left.source edge)=right.source (edgeBij edge) :=
    Subtype.ext ((image_spec (left.source edge)).unique (source_related edge))
  have targetEq (edge : left.Edge) : image (left.target edge)=right.target (edgeBij edge) :=
    Subtype.ext ((image_spec (left.target edge)).unique (target_related edge))
  have labelEq (edge : left.Edge) : left.label edge=right.label (edgeBij edge) := by
    obtain ⟨node,lookup⟩ := chain_edge_lookup chain edge.property
    obtain ⟨old,oldLookup,labels⟩ := step.beta_preimage_label redex (edgeSpec edge) lookup (uncreated _ edge.property)
    change SyntaxIncidence.label target edge.val=SyntaxIncidence.label source (edgeBij edge).val
    rw [SyntaxIncidence.label_of_lookup target edge.val lookup,
      SyntaxIncidence.label_of_lookup source (edgeBij edge).val oldLookup]
    exact labels.symm
  have incident : ∀ vertex : right.Vertex,∃ edge,vertex=right.source edge ∨vertex=right.target edge := by
    intro vertex
    obtain ⟨edge,chosen,endpoint⟩ := vertex.property
    refine ⟨⟨edge,chosen⟩,?_⟩
    rcases endpoint with source | targetEnd
    · left;exact Subtype.ext source
    · right;exact Subtype.ext targetEnd
  exact ⟨incidence_iso_of_edges edgeBij image injective sourceEq targetEq labelEq incident,edgeSpec,image_spec⟩

/-- Automatic bare incidence reflection for an actual all-old chain.
Neither an old chain, a coordinate map nor a desired isomorphism is input.
This theorem does not assert equality of physical graph representations. -/
theorem uncreated_chain_incidence
    {source target body argument : LTerm} {site start : Path} {edges : List Path} {beta alpha : Label}
    (sourceClosed : Closed source.erase) (targetClosed : Closed target.erase)
    (step : StepAt site source target)
    (redex : source.subterm site=some (.app beta (.lam alpha body) argument))
    (chain : PrerequisiteChain target start edges)
    (uncreated : ∀ edge∈edges,¬BetaCreatedIncoming body site edge) :
    ∃ oldStart oldEdges,PrerequisiteChain source oldStart oldEdges ∧
      edges.map target.labelAt=oldEdges.map source.labelAt ∧edges.length=oldEdges.length ∧
      ∃ iso : ChainIncidenceIso (chainSyntaxIncidence target targetClosed edges)
        (chainSyntaxIncidence source sourceClosed oldEdges),
        (∀ edge,BetaNodePreimage body argument site edge.val.val (iso.edges edge).val.val) ∧
        ∀ vertex,BetaVertexPreimage body argument site source target vertex.val (iso.vertices vertex).val := by
  obtain ⟨oldStart,oldEdges,_,oldChain,origins,labels,lengths⟩ :=
    step.uncreated_chain_reflect redex chain uncreated
  obtain ⟨iso,edgeOrigins,vertexOrigins⟩ :=
    uncreated_chain_iso sourceClosed targetClosed step redex chain oldChain uncreated origins
  exact ⟨oldStart,oldEdges,oldChain,labels,lengths,iso,edgeOrigins,vertexOrigins⟩
end Lamping.AG
