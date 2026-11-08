import Lamping.Lambda.DisjointBlocks
import Lamping.Lambda.LabelContextualRegions
namespace Lamping.Lambda.Labelled

/-- Arbitrary-context beta argument subregion edge coverage, using the
unchanged global target INIT basis and its actual outer binder ports. -/
theorem StepAt.argument_subregion_edge_cover {body argument regionTerm : LTerm}
    (step : StepAt head t u) (initial : INIT t)
    (source : t.subterm head=some (.app beta (.lam alpha body) argument))
    (atRegion : argument.subterm regionSite=some regionTerm)
    (member : e∈sourceEdges [] .external (initLabels u.erase))
    (support : (e.atom.relabel (initialRelabelling u 0)).Supported (SourceRegion regionTerm))
    (rootAvoid : (e.atom.relabel (initialRelabelling u 0)).Supported (fun n => Label.atom n≠regionTerm.label)) :
    ∃ occurrence env ctx copy,ArgumentOccurrence body.erase occurrence ∧
      SourceSubterm [] .external (initLabels u.erase) ((head++occurrence)++regionSite) env ctx copy ∧
      e∈sourceEdges env ctx copy ∧ e.atom≠copy.label := by
  have atomMember : e.atom∈(initLabels u.erase).labels := by
    rw [←sourceEdges_atoms (initLabels u.erase) [] .external]
    exact List.mem_map.mpr ⟨e,member,rfl⟩
  obtain ⟨p,node,atNode,labelEq⟩ := LTerm.label_mem_located _ atomMember
  have currentNode := LTerm.basis_node_transport u atNode
  have nodeSupport : (node.relabel (initialRelabelling u 0)).label.Supported (SourceRegion regionTerm) := by
    simpa only [LTerm.label_relabel,labelEq] using support
  obtain ⟨occurrence,wholeCopy,suffix,occurs,wholeLookup,interior,paths⟩ :=
    step.argument_subregion_node_locates initial source atRegion currentNode nodeSupport
  rw [paths,LTerm.subterm_append] at atNode
  obtain ⟨copy,copyLookup,insideNode⟩ := Option.bind_eq_some_iff.mp atNode
  obtain ⟨env,ctx,located⟩ := SourceSubterm.of_lookup (initLabels u.erase) copyLookup [] .external
  have insideAtom : e.atom∈copy.labels := labelEq ▸ LTerm.label_mem_of_subterm insideNode
  obtain ⟨localEdge,localMember,atomEq⟩ := sourceEdges_has_label (env := env) (atPort := ctx) insideAtom
  have sameEdge : localEdge=e := sourceEdges_unique (init_is_INIT _) (located.edges_subset _ localMember) member atomEq
  refine ⟨occurrence,env,ctx,copy,occurs,located,sameEdge ▸ localMember,?_⟩
  intro rootEq
  have currentRoot := LTerm.basis_node_transport u copyLookup
  rw [LTerm.subterm_append,wholeLookup] at currentRoot
  have rootSupport : (copy.relabel (initialRelabelling u 0)).label.Supported
      (fun n => Label.atom n≠regionTerm.label) := by
    simpa only [LTerm.label_relabel,←rootEq] using rootAvoid
  obtain ⟨old,oldLookup,oldSupport⟩ := interior.supported_node_origin currentRoot rootSupport
  have same : old=regionTerm := Option.some.inj (oldLookup.symm.trans atRegion)
  cases same
  have headInitial := initial.subterm source
  have regionInArgument := LTerm.label_mem_of_subterm atRegion
  obtain ⟨n,atomic⟩ := headInitial.1 regionTerm.label
    (List.mem_cons_of_mem _ (List.mem_append_right _ regionInArgument))
  rw [atomic] at oldSupport
  exact oldSupport rfl

/-- Arbitrary-context beta body subregion edge coverage. Current root support
reflects to the original body root through the actual beta substitution. -/
theorem StepAt.body_subregion_edge_cover {body argument regionTerm : LTerm}
    (step : StepAt head t u) (initial : INIT t)
    (source : t.subterm head=some (.app beta (.lam alpha body) argument))
    (atRegion : body.subterm regionSite=some regionTerm)
    (member : e∈sourceEdges [] .external (initLabels u.erase))
    (support : (e.atom.relabel (initialRelabelling u 0)).Supported (SourceRegion regionTerm))
    (rootAvoid : (e.atom.relabel (initialRelabelling u 0)).Supported (fun n => Label.atom n≠regionTerm.label)) :
    ∃ env ctx copy,SourceSubterm [] .external (initLabels u.erase) (head++regionSite) env ctx copy ∧
      e∈sourceEdges env ctx copy ∧ e.atom≠copy.label := by
  have atomMember : e.atom∈(initLabels u.erase).labels := by
    rw [←sourceEdges_atoms (initLabels u.erase) [] .external]
    exact List.mem_map.mpr ⟨e,member,rfl⟩
  obtain ⟨p,node,atNode,labelEq⟩ := LTerm.label_mem_located _ atomMember
  have currentNode := LTerm.basis_node_transport u atNode
  have nodeSupport : (node.relabel (initialRelabelling u 0)).label.Supported (SourceRegion regionTerm) := by
    simpa only [LTerm.label_relabel,labelEq] using support
  obtain ⟨current,suffix,currentLookup,paths,reflects⟩ :=
    step.body_subregion_node_locates initial source atRegion currentNode nodeSupport
  rw [paths,LTerm.subterm_append] at atNode
  obtain ⟨copy,copyLookup,insideNode⟩ := Option.bind_eq_some_iff.mp atNode
  obtain ⟨env,ctx,located⟩ := SourceSubterm.of_lookup (initLabels u.erase) copyLookup [] .external
  have insideAtom : e.atom∈copy.labels := labelEq ▸ LTerm.label_mem_of_subterm insideNode
  obtain ⟨localEdge,localMember,atomEq⟩ := sourceEdges_has_label (env := env) (atPort := ctx) insideAtom
  have sameEdge : localEdge=e := sourceEdges_unique (init_is_INIT _) (located.edges_subset _ localMember) member atomEq
  refine ⟨env,ctx,copy,located,sameEdge ▸ localMember,?_⟩
  intro rootEq
  have currentRoot := LTerm.basis_node_transport u copyLookup
  have sameCurrent : current=copy.relabel (initialRelabelling u 0) := Option.some.inj (currentLookup.symm.trans currentRoot)
  have rootSupport : (copy.relabel (initialRelabelling u 0)).label.Supported
      (fun n => Label.atom n≠regionTerm.label) := by
    simpa only [LTerm.label_relabel,←rootEq] using rootAvoid
  have oldSupport := reflects _ (sameCurrent.symm ▸ rootSupport)
  obtain ⟨n,atomic⟩ := (initial.subterm source).redex_body.1 regionTerm.label (LTerm.label_mem_of_subterm atRegion)
  rw [atomic] at oldSupport
  exact oldSupport rfl
/-- Actual global argument-copy components for arbitrary head positions.
Every covered signed traversal stays in one syntax-disjoint component. -/
theorem StepAt.argument_subregion_walk {body argument regionTerm : LTerm}
    (step : StepAt head t u) (initial : INIT t)
    (source : t.subterm head=some (.app beta (.lam alpha body) argument))
    (atRegion : argument.subterm regionSite=some regionTerm)
    (walk : SourceWalk (sourceEdges [] .external (initLabels u.erase)) start word finish)
    (support : ∀ e∈word,(initialRelabelling u 0 e.atom).Supported (SourceRegion regionTerm))
    (rootAvoid : ∀ e∈word,(initialRelabelling u 0 e.atom).Supported (fun n => Label.atom n≠regionTerm.label)) :
    ∃ occurrence env ctx copy,ArgumentOccurrence body.erase occurrence ∧
      SourceSubterm [] .external (initLabels u.erase) ((head++occurrence)++regionSite) env ctx copy ∧
      SourceWalk (sourceEdges env ctx copy) start word finish ∧ ∀ e∈word,Label.atom e.atom≠copy.label := by
  classical
  let Index := {p : Path // ArgumentOccurrence body.erase p ∧
    ∃ env ctx sub,SourceSubterm [] .external (initLabels u.erase) ((head++p)++regionSite) env ctx sub}
  have dataExists : ∀ i : Index,∃ data : List Label × SourcePort × LTerm,
      SourceSubterm [] .external (initLabels u.erase) ((head++i.val)++regionSite) data.1 data.2.1 data.2.2 := by
    intro i
    obtain ⟨env,ctx,sub,located⟩ := i.property.2
    exact ⟨(env,ctx,sub),located⟩
  let component := fun i : Index => Classical.choose (dataExists i)
  have components := fun i : Index => Classical.choose_spec (dataExists i)
  have apart : ∀ i j : Index,i≠j → DisjointPositions ((head++i.val)++regionSite) ((head++j.val)++regionSite) := by
    intro i j different
    have old := i.property.1.disjoint_of_ne j.property.1 (by
      intro same
      exact different (Subtype.ext same))
    exact ((((DisjointPositions.prefix old head).descend_left regionSite).symm).descend_left regionSite).symm
  have cover : ∀ {a e b},e∈word → SourceTraverse (sourceEdges [] .external (initLabels u.erase)) a e b →
      ∃ i : Index,SourceTraverse (sourceEdges (component i).1 (component i).2.1 (component i).2.2) a e b ∧
        Label.atom e.atom≠(component i).2.2.label := by
    intro a e b inWord traverse
    cases traverse with
    | @forward edge n member atomic =>
      obtain ⟨occurrence,env,ctx,sub,occurs,located,edgeMember,nonroot⟩ :=
        step.argument_subregion_edge_cover initial source atRegion member
          (by simpa only [atomic,Label.relabel_atom] using support _ inWord)
          (by simpa only [atomic,Label.relabel_atom] using rootAvoid _ inWord)
      let i : Index := ⟨occurrence,occurs,env,ctx,sub,located⟩
      obtain ⟨envEq,ctxEq,subEq⟩ := located.unique (components i)
      refine ⟨i,.forward (envEq ▸ ctxEq ▸ subEq ▸ edgeMember) atomic,?_⟩
      change Label.atom n≠(Classical.choose (dataExists i)).2.2.label
      rw [←subEq,←atomic]
      exact nonroot
    | @backward edge n member atomic =>
      obtain ⟨occurrence,env,ctx,sub,occurs,located,edgeMember,nonroot⟩ :=
        step.argument_subregion_edge_cover initial source atRegion member
          (by simpa only [atomic,Label.relabel_atom] using support _ inWord)
          (by simpa only [atomic,Label.relabel_atom] using rootAvoid _ inWord)
      let i : Index := ⟨occurrence,occurs,env,ctx,sub,located⟩
      obtain ⟨envEq,ctxEq,subEq⟩ := located.unique (components i)
      refine ⟨i,.backward (envEq ▸ ctxEq ▸ subEq ▸ edgeMember) atomic,?_⟩
      change Label.atom n≠(Classical.choose (dataExists i)).2.2.label
      rw [←subEq,←atomic]
      exact nonroot
  obtain ⟨i,inside,nonroot⟩ := SourceWalk.one_component components (init_is_INIT _) apart walk cover
  exact ⟨i.val,(component i).1,(component i).2.1,(component i).2.2,i.property.1,components i,inside,nonroot⟩

/-- The body subregion remains the one actual global subtree at head++site. -/
theorem StepAt.body_subregion_walk {body argument regionTerm : LTerm}
    (step : StepAt head t u) (initial : INIT t)
    (source : t.subterm head=some (.app beta (.lam alpha body) argument))
    (atRegion : body.subterm regionSite=some regionTerm)
    (walk : SourceWalk (sourceEdges [] .external (initLabels u.erase)) start word finish)
    (support : ∀ e∈word,(initialRelabelling u 0 e.atom).Supported (SourceRegion regionTerm))
    (rootAvoid : ∀ e∈word,(initialRelabelling u 0 e.atom).Supported (fun n => Label.atom n≠regionTerm.label)) :
    ∃ env ctx copy,SourceSubterm [] .external (initLabels u.erase) (head++regionSite) env ctx copy ∧
      SourceWalk (sourceEdges env ctx copy) start word finish ∧ ∀ e∈word,Label.atom e.atom≠copy.label := by
  obtain ⟨current,currentLocal,_⟩ := LTerm.contract_subterm_root_reflect
    (beta := beta) (alpha := alpha) (argument := argument) atRegion
  have currentLookup : u.subterm (head++regionSite)=some current := by
    rw [LTerm.subterm_append,step.contract_lookup source]
    exact currentLocal
  have basisLookup : ((initLabels u.erase).subterm (head++regionSite)).map (LTerm.relabel (initialRelabelling u 0))=some current := by
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
        step.body_subregion_edge_cover initial source atRegion member
          (by simpa only [atomic,Label.relabel_atom] using support _ inWord)
          (by simpa only [atomic,Label.relabel_atom] using rootAvoid _ inWord)
      obtain ⟨envEq,ctxEq,copyEq⟩ := newLocated.unique located
      exact ⟨.forward (envEq ▸ ctxEq ▸ copyEq ▸ edgeMember) atomic,by simpa only [←atomic,←copyEq] using nonroot⟩
    | @backward edge n member atomic =>
      obtain ⟨newEnv,newCtx,newCopy,newLocated,edgeMember,nonroot⟩ :=
        step.body_subregion_edge_cover initial source atRegion member
          (by simpa only [atomic,Label.relabel_atom] using support _ inWord)
          (by simpa only [atomic,Label.relabel_atom] using rootAvoid _ inWord)
      obtain ⟨envEq,ctxEq,copyEq⟩ := newLocated.unique located
      exact ⟨.backward (envEq ▸ ctxEq ▸ copyEq ▸ edgeMember) atomic,by simpa only [←atomic,←copyEq] using nonroot⟩
  refine ⟨env,ctx,copy,located,walk.restrict_traversals (fun member traverse => (restrict member traverse).1),?_⟩
  intro e member
  obtain ⟨a,b,traverse⟩ := walk.traverse_of_mem member
  exact (restrict member traverse).2
/-- Degree-level contextual argument localization along the two actual,
identical global/local schedules after a real head at any syntax position. -/
theorem StepAt.argument_subregion_degree {body argument regionTerm : LTerm}
    (step : StepAt head t u) (initial : INIT t)
    (source : t.subterm head=some (.app beta (.lam alpha body) argument))
    (atRegion : argument.subterm regionSite=some regionTerm)
    (history : History ps u target) (basisHistory : History ps (initLabels u.erase) basisTarget)
    (globalDegree : target.degreeAt p=some globalLabel) (basisDegree : basisTarget.degreeAt p=some basisLabel)
    (support : globalLabel.Supported (SourceRegion regionTerm))
    (rootAvoid : globalLabel.Supported (fun n => Label.atom n≠regionTerm.label)) :
    ∃ occurrence env ctx copy,ArgumentOccurrence body.erase occurrence ∧
      SourceSubterm [] .external (initLabels u.erase) ((head++occurrence)++regionSite) env ctx copy ∧
      basisLabel.Supported (SourceRegion copy) ∧ ∀ e∈basisLabel.edgeWord,Label.atom e.atom≠copy.label := by
  have transported := history.local_degree_transport basisHistory basisDegree
  have labelEq : basisLabel.relabel (initialRelabelling u 0)=globalLabel :=
    Option.some.inj (transported.1.symm.trans globalDegree)
  have localSupport := (Label.supported_relabel _ _ basisLabel).mp (labelEq.symm ▸ support)
  have localAvoid := (Label.supported_relabel _ _ basisLabel).mp (labelEq.symm ▸ rootAvoid)
  obtain ⟨appId,lamId,walk⟩ := basisHistory.degree_walk (init_is_INIT _) basisDegree
  obtain ⟨occurrence,env,ctx,copy,occurs,located,localWalk,nonroot⟩ := step.argument_subregion_walk initial source atRegion walk
    ((Label.supported_iff_within _ basisLabel).mp localSupport)
    ((Label.supported_iff_within _ basisLabel).mp localAvoid)
  exact ⟨occurrence,env,ctx,copy,occurs,located,(Label.supported_iff_within _ basisLabel).mpr localWalk.within_source,nonroot⟩

/-- Degree-level contextual body localization, with exact old/global and
new/local labels and a real global head++region path. -/
theorem StepAt.body_subregion_degree {body argument regionTerm : LTerm}
    (step : StepAt head t u) (initial : INIT t)
    (source : t.subterm head=some (.app beta (.lam alpha body) argument))
    (atRegion : body.subterm regionSite=some regionTerm)
    (history : History ps u target) (basisHistory : History ps (initLabels u.erase) basisTarget)
    (globalDegree : target.degreeAt p=some globalLabel) (basisDegree : basisTarget.degreeAt p=some basisLabel)
    (support : globalLabel.Supported (SourceRegion regionTerm))
    (rootAvoid : globalLabel.Supported (fun n => Label.atom n≠regionTerm.label)) :
    ∃ env ctx copy,SourceSubterm [] .external (initLabels u.erase) (head++regionSite) env ctx copy ∧
      basisLabel.Supported (SourceRegion copy) ∧ ∀ e∈basisLabel.edgeWord,Label.atom e.atom≠copy.label := by
  have transported := history.local_degree_transport basisHistory basisDegree
  have labelEq : basisLabel.relabel (initialRelabelling u 0)=globalLabel :=
    Option.some.inj (transported.1.symm.trans globalDegree)
  have localSupport := (Label.supported_relabel _ _ basisLabel).mp (labelEq.symm ▸ support)
  have localAvoid := (Label.supported_relabel _ _ basisLabel).mp (labelEq.symm ▸ rootAvoid)
  obtain ⟨appId,lamId,walk⟩ := basisHistory.degree_walk (init_is_INIT _) basisDegree
  obtain ⟨env,ctx,copy,located,localWalk,nonroot⟩ := step.body_subregion_walk initial source atRegion walk
    ((Label.supported_iff_within _ basisLabel).mp localSupport)
    ((Label.supported_iff_within _ basisLabel).mp localAvoid)
  exact ⟨env,ctx,copy,located,(Label.supported_iff_within _ basisLabel).mpr localWalk.within_source,nonroot⟩
end Lamping.Lambda.Labelled
