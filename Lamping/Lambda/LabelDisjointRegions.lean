import Lamping.Lambda.LabelBodySubregions
namespace Lamping.Lambda.Labelled

mutual
  theorem Label.supported_incompatible (separate : ∀ n,region n → ¬other n) :
      ∀ l : Label,l.Supported region → l.Supported other → False
    | .single a => Letter.supported_incompatible separate a
    | .cons a _ => fun left right => Letter.supported_incompatible separate a left.1 right.1
  theorem Letter.supported_incompatible (separate : ∀ n,region n → ¬other n) :
      ∀ a : Letter,a.Supported region → a.Supported other → False
    | .atom n => separate n
    | .over l | .under l => Label.supported_incompatible separate l
end

/-- A real edit in a disjoint subtree retains the whole selected subtree,
including its root label, syntax and all original variable indices. -/
theorem RegionCut.disjoint_subterm (cut : RegionCut region head t u)
    (apart : DisjointPositions head site) : u.subterm site=t.subterm site := by
  induction cut generalizing site with
  | here => exact False.elim (DisjointPositions.nil_left apart)
  | fn cut ih =>
    cases site with
    | nil => exact False.elim (DisjointPositions.nil_right apart)
    | cons step rest =>
      cases step with
      | body => rfl
      | arg => rfl
      | fn => exact ih apart.child
  | arg cut ih =>
    cases site with
    | nil => exact False.elim (DisjointPositions.nil_right apart)
    | cons step rest =>
      cases step with
      | body => rfl
      | fn => rfl
      | arg => exact ih apart.child
  | body cut ih =>
    cases site with
    | nil => exact False.elim (DisjointPositions.nil_right apart)
    | cons step rest =>
      cases step with
      | fn => rfl
      | arg => rfl
      | body => exact ih apart.child

/-- A regional node cannot be supplied by a disjoint actually edited head
region. Outside that head, the original node label remains at its real path. -/
theorem RegionCut.disjoint_supported_node_locates
    (cut : RegionCut (SourceRegion headTerm) head t u) (initial : INIT t)
    (atHead : t.subterm head=some headTerm) (atRegion : t.subterm site=some regionTerm)
    (apart : DisjointPositions head site) (atNode : u.subterm p=some node)
    (support : node.label.Supported (SourceRegion regionTerm)) : ∃ suffix,p=site++suffix := by
  have notInHead : ¬∃ suffix,p=head++suffix := by
    intro inside
    have headSupport := cut.internal_node_supported atNode inside
    exact Label.supported_incompatible
      (fun n member other => LTerm.disjoint_subterm_labels initial atHead atRegion apart (Label.atom n) member other)
      node.label headSupport support
  have oldLabel : t.labelAt p=some node.label := by
    rw [←cut.outside_labels notInHead]
    simp only [LTerm.labelAt,atNode,Option.map_some]
  obtain ⟨old,oldLookup,labelEq⟩ := Option.map_eq_some_iff.mp oldLabel
  obtain ⟨n,atomic⟩ := initial.1 old.label (LTerm.label_mem_of_subterm oldLookup)
  have oldSupport : old.label.Supported (SourceRegion regionTerm) := labelEq ▸ support
  have member : old.label∈regionTerm.labels := by
    rw [atomic] at oldSupport ⊢
    exact oldSupport
  exact LTerm.initial_region_locates t initial atRegion oldLookup member

/-- The real one-step history constructs the labelled head-region cut. -/
theorem StepAt.region_cut (step : StepAt head t u) (initial : INIT t)
    (atHead : t.subterm head=some headTerm) : RegionCut (SourceRegion headTerm) head t u := by
  apply (History.cons step (.nil _)).region_cut initial atHead
  intro p member
  have same : p=head := List.mem_singleton.mp member
  exact ⟨[],by simp [same]⟩

/-- Actual local-basis edges supported in a disjoint original subregion are
inside its unchanged image, and strict support excludes its incoming edge. -/
theorem StepAt.disjoint_subregion_edge_cover (step : StepAt head t u) (initial : INIT t)
    (atHead : t.subterm head=some headTerm) (atRegion : t.subterm site=some regionTerm)
    (apart : DisjointPositions head site)
    (member : e∈sourceEdges [] .external (initLabels u.erase))
    (support : (e.atom.relabel (initialRelabelling u 0)).Supported (SourceRegion regionTerm))
    (rootAvoid : (e.atom.relabel (initialRelabelling u 0)).Supported
      (fun n => Label.atom n≠regionTerm.label)) :
    ∃ env ctx copy,SourceSubterm [] .external (initLabels u.erase) site env ctx copy ∧
      e∈sourceEdges env ctx copy ∧ e.atom≠copy.label := by
  have cut := step.region_cut initial atHead
  have atomMember : e.atom∈(initLabels u.erase).labels := by
    rw [←sourceEdges_atoms (initLabels u.erase) [] .external]
    exact List.mem_map.mpr ⟨e,member,rfl⟩
  obtain ⟨p,node,atNode,labelEq⟩ := LTerm.label_mem_located _ atomMember
  have currentNode := LTerm.basis_node_transport u atNode
  have nodeSupport : (node.relabel (initialRelabelling u 0)).label.Supported (SourceRegion regionTerm) := by
    simpa only [LTerm.label_relabel,labelEq] using support
  obtain ⟨suffix,paths⟩ := cut.disjoint_supported_node_locates initial atHead atRegion apart currentNode nodeSupport
  have currentRegion : u.subterm site=some regionTerm := (cut.disjoint_subterm apart).trans atRegion
  have basisRegion : ((initLabels u.erase).subterm site).map (LTerm.relabel (initialRelabelling u 0))=some regionTerm := by
    rw [←LTerm.subterm_relabel,show (initLabels u.erase).relabel (initialRelabelling u 0)=u from initialRelabelling_factor u 0]
    exact currentRegion
  obtain ⟨copy,copyLookup,copyEq⟩ := Option.map_eq_some_iff.mp basisRegion
  obtain ⟨env,ctx,located⟩ := SourceSubterm.of_lookup (initLabels u.erase) copyLookup [] .external
  rw [paths,LTerm.subterm_append,copyLookup] at atNode
  have insideAtom : e.atom∈copy.labels := labelEq ▸ LTerm.label_mem_of_subterm atNode
  obtain ⟨localEdge,localMember,atomEq⟩ := sourceEdges_has_label (env := env) (atPort := ctx) insideAtom
  have sameEdge : localEdge=e := sourceEdges_unique (init_is_INIT _) (located.edges_subset _ localMember) member atomEq
  refine ⟨env,ctx,copy,located,sameEdge ▸ localMember,?_⟩
  intro rootEq
  have rootSupport : (copy.relabel (initialRelabelling u 0)).label.Supported
      (fun n => Label.atom n≠regionTerm.label) := by
    simpa only [LTerm.label_relabel,←rootEq] using rootAvoid
  have oldAvoid := copyEq ▸ rootSupport
  obtain ⟨n,atomic⟩ := initial.1 regionTerm.label (LTerm.label_mem_of_subterm atRegion)
  rw [atomic] at oldAvoid
  exact oldAvoid rfl
/-- The entire actual supported walk stays in the unchanged disjoint region. -/
theorem StepAt.disjoint_subregion_walk (step : StepAt head t u) (initial : INIT t)
    (atHead : t.subterm head=some headTerm) (atRegion : t.subterm site=some regionTerm)
    (apart : DisjointPositions head site)
    (walk : SourceWalk (sourceEdges [] .external (initLabels u.erase)) start word finish)
    (support : ∀ e∈word,(initialRelabelling u 0 e.atom).Supported (SourceRegion regionTerm))
    (rootAvoid : ∀ e∈word,(initialRelabelling u 0 e.atom).Supported (fun n => Label.atom n≠regionTerm.label)) :
    ∃ env ctx copy,SourceSubterm [] .external (initLabels u.erase) site env ctx copy ∧
      SourceWalk (sourceEdges env ctx copy) start word finish ∧
      ∀ e∈word,Label.atom e.atom≠copy.label := by
  have currentLookup : u.subterm site=some regionTerm := ((step.region_cut initial atHead).disjoint_subterm apart).trans atRegion
  have basisLookup : ((initLabels u.erase).subterm site).map (LTerm.relabel (initialRelabelling u 0))=some regionTerm := by
    rw [←LTerm.subterm_relabel,show (initLabels u.erase).relabel (initialRelabelling u 0)=u from initialRelabelling_factor u 0]
    exact currentLookup
  obtain ⟨copy,copyLookup,_⟩ := Option.map_eq_some_iff.mp basisLookup
  obtain ⟨env,ctx,located⟩ := SourceSubterm.of_lookup (initLabels u.erase) copyLookup [] .external
  have restrict : ∀ {a e b},e∈word → SourceTraverse (sourceEdges [] .external (initLabels u.erase)) a e b →
      SourceTraverse (sourceEdges env ctx copy) a e b ∧ Label.atom e.atom≠copy.label := by
    intro a e b inWord traverse
    cases traverse with
    | @forward edge n member atomic =>
      obtain ⟨newEnv,newCtx,newCopy,newLocated,edgeMember,nonroot⟩ :=
        step.disjoint_subregion_edge_cover initial atHead atRegion apart member
          (by simpa only [atomic,Label.relabel_atom] using support _ inWord)
          (by simpa only [atomic,Label.relabel_atom] using rootAvoid _ inWord)
      obtain ⟨envEq,ctxEq,copyEq⟩ := newLocated.unique located
      exact ⟨.forward (envEq ▸ ctxEq ▸ copyEq ▸ edgeMember) atomic,by simpa only [←atomic,←copyEq] using nonroot⟩
    | @backward edge n member atomic =>
      obtain ⟨newEnv,newCtx,newCopy,newLocated,edgeMember,nonroot⟩ :=
        step.disjoint_subregion_edge_cover initial atHead atRegion apart member
          (by simpa only [atomic,Label.relabel_atom] using support _ inWord)
          (by simpa only [atomic,Label.relabel_atom] using rootAvoid _ inWord)
      obtain ⟨envEq,ctxEq,copyEq⟩ := newLocated.unique located
      exact ⟨.backward (envEq ▸ ctxEq ▸ copyEq ▸ edgeMember) atomic,by simpa only [←atomic,←copyEq] using nonroot⟩
  refine ⟨env,ctx,copy,located,walk.restrict_traversals (fun member traverse => (restrict member traverse).1),?_⟩
  intro e member
  obtain ⟨a,b,traverse⟩ := walk.traverse_of_mem member
  exact (restrict member traverse).2

/-- A real disjoint head transports strict degree support into the unchanged
region's local INIT coordinates, with the identical actual tail schedule. -/
theorem StepAt.disjoint_subregion_degree (step : StepAt head t u) (initial : INIT t)
    (atHead : t.subterm head=some headTerm) (atRegion : t.subterm site=some regionTerm)
    (apart : DisjointPositions head site)
    (history : History ps u target) (basisHistory : History ps (initLabels u.erase) basisTarget)
    (globalDegree : target.degreeAt p=some globalLabel) (basisDegree : basisTarget.degreeAt p=some basisLabel)
    (support : globalLabel.Supported (SourceRegion regionTerm))
    (rootAvoid : globalLabel.Supported (fun n => Label.atom n≠regionTerm.label)) :
    ∃ env ctx copy,SourceSubterm [] .external (initLabels u.erase) site env ctx copy ∧
      basisLabel.Supported (SourceRegion copy) ∧ ∀ e∈basisLabel.edgeWord,Label.atom e.atom≠copy.label := by
  have transported := history.local_degree_transport basisHistory basisDegree
  have labelEq : basisLabel.relabel (initialRelabelling u 0)=globalLabel :=
    Option.some.inj (transported.1.symm.trans globalDegree)
  have localSupport := (Label.supported_relabel _ _ basisLabel).mp (labelEq.symm ▸ support)
  have localAvoid := (Label.supported_relabel _ _ basisLabel).mp (labelEq.symm ▸ rootAvoid)
  obtain ⟨appId,lamId,walk⟩ := basisHistory.degree_walk (init_is_INIT _) basisDegree
  obtain ⟨env,ctx,copy,located,localWalk,nonroot⟩ := step.disjoint_subregion_walk initial atHead atRegion apart walk
    ((Label.supported_iff_within _ basisLabel).mp localSupport)
    ((Label.supported_iff_within _ basisLabel).mp localAvoid)
  exact ⟨env,ctx,copy,located,(Label.supported_iff_within _ basisLabel).mpr localWalk.within_source,nonroot⟩
end Lamping.Lambda.Labelled
