import Lamping.Lambda.LabelCopyInteriors
namespace Lamping.Lambda.Labelled

theorem Label.Supported.mono {l : Label} {region larger : Nat → Prop} (supported : l.Supported region)
    (extendRegion : ∀ n,region n → larger n) : l.Supported larger := by
  rw [Label.supported_iff_within] at supported ⊢
  exact fun e member => extendRegion _ (supported e member)

/-- A strict original-argument subregion is transported into the corresponding
subregion of one actual argument copy. Avoiding its original root atom is
essential: a copy may occur as the function of an outside application. -/
theorem root_beta_argument_subregion_edge_cover {body argument regionTerm : LTerm}
    (initial : INIT (.app beta (.lam alpha body) argument))
    (atRegion : argument.subterm regionSite=some regionTerm)
    (member : e∈sourceEdges [] .external (initLabels (LTerm.contract beta alpha body argument).erase))
    (support : (e.atom.relabel (initialRelabelling (LTerm.contract beta alpha body argument) 0)).Supported
      (SourceRegion regionTerm))
    (rootAvoid : (e.atom.relabel (initialRelabelling (LTerm.contract beta alpha body argument) 0)).Supported
      (fun n => Label.atom n≠regionTerm.label)) :
    ∃ occurrence env ctx copy,ArgumentOccurrence body.erase occurrence ∧
      SourceSubterm [] .external (initLabels (LTerm.contract beta alpha body argument).erase)
        (occurrence++regionSite) env ctx copy ∧ e∈sourceEdges env ctx copy ∧ e.atom≠copy.label := by
  let target := LTerm.contract beta alpha body argument
  let basis := initLabels target.erase
  let subst := initialRelabelling target 0
  have subset := LTerm.labels_subset_of_subterm atRegion
  have coarseSupport := support.mono (fun n member => subset (Label.atom n) member)
  obtain ⟨occurrence,env,ctx,wholeCopy,occurs,atWhole,wholeEdge,wholeNonroot⟩ :=
    root_beta_argument_edge_cover initial member coarseSupport
  have inWhole : e.atom∈wholeCopy.labels := by
    rw [←sourceEdges_atoms wholeCopy env ctx]
    exact List.mem_map.mpr ⟨e,wholeEdge,rfl⟩
  obtain ⟨relative,node,atNode,labelEq⟩ := LTerm.label_mem_located wholeCopy inWhole
  have basisAt : basis.subterm (occurrence++relative)=some node := by
    rw [LTerm.subterm_append,atWhole.lookup]
    exact atNode
  have globalWhole := LTerm.basis_node_transport target atWhole.lookup
  have interior := LTerm.contract_argument_copy_interior occurs globalWhole
  have globalNode := LTerm.basis_node_transport target basisAt
  have localGlobalNode : (wholeCopy.relabel subst).subterm relative=some (node.relabel subst) := by
    rw [LTerm.subterm_append,globalWhole] at globalNode
    exact globalNode
  have currentSupport : (node.relabel subst).label.Supported (SourceRegion regionTerm) := by
    simpa only [LTerm.label_relabel,labelEq] using support
  have argumentInitial : INIT argument := by
    refine ⟨?_,(List.nodup_append.mp (List.nodup_cons.mp initial.2).2).2.1⟩
    intro l member
    exact initial.1 l (List.mem_cons_of_mem _ (List.mem_append_right _ member))
  obtain ⟨suffix,located⟩ := interior.region_locates argumentInitial atRegion localGlobalNode currentSupport
  have regionAtNode : basis.subterm ((occurrence++regionSite)++suffix)=some node := by
    simpa only [located,List.append_assoc] using basisAt
  rw [LTerm.subterm_append] at regionAtNode
  obtain ⟨copy,copyLookup,insideNode⟩ := Option.bind_eq_some_iff.mp regionAtNode
  obtain ⟨regionEnv,regionCtx,atCopy⟩ := SourceSubterm.of_lookup basis copyLookup [] .external
  have regionAtom : e.atom∈copy.labels := labelEq ▸ LTerm.label_mem_of_subterm insideNode
  obtain ⟨regionEdge,edgeMember,atomEq⟩ := sourceEdges_has_label (env := regionEnv) (atPort := regionCtx) regionAtom
  have sameEdge : regionEdge=e := sourceEdges_unique (init_is_INIT _) (atCopy.edges_subset _ edgeMember) member atomEq
  refine ⟨occurrence,regionEnv,regionCtx,copy,occurs,atCopy,sameEdge ▸ edgeMember,?_⟩
  intro isRoot
  have currentRoot := LTerm.basis_node_transport target copyLookup
  have localCurrentRoot : (wholeCopy.relabel subst).subterm regionSite=some (copy.relabel subst) := by
    rw [LTerm.subterm_append,globalWhole] at currentRoot
    exact currentRoot
  have currentAvoid : (copy.relabel subst).label.Supported (fun n => Label.atom n≠regionTerm.label) := by
    simpa only [LTerm.label_relabel,←isRoot] using rootAvoid
  obtain ⟨old,atOld,oldAvoid⟩ := interior.supported_node_origin localCurrentRoot currentAvoid
  have oldEq : old=regionTerm := Option.some.inj (atOld.symm.trans atRegion)
  cases oldEq
  obtain ⟨n,atomic⟩ := argumentInitial.1 regionTerm.label (LTerm.label_mem_of_subterm atRegion)
  rw [atomic] at oldAvoid
  exact oldAvoid rfl
def ArgumentRegionComponentSite (body : Term) (basis : LTerm) (regionSite : Path) :=
  {p : Path // ArgumentOccurrence body p ∧
    ∃ env ctx sub,SourceSubterm [] .external basis (p++regionSite) env ctx sub}

noncomputable def argumentRegionComponent (site : ArgumentRegionComponentSite body basis regionSite) :
    List Label × SourcePort × LTerm :=
  Classical.choose (show ∃ data : List Label × SourcePort × LTerm,
    SourceSubterm [] .external basis (site.val++regionSite) data.1 data.2.1 data.2.2 from by
      obtain ⟨env,ctx,sub,located⟩ := site.property.2
      exact ⟨(env,ctx,sub),located⟩)

theorem argumentRegionComponent_located (site : ArgumentRegionComponentSite body basis regionSite) :
    SourceSubterm [] .external basis (site.val++regionSite)
      (argumentRegionComponent site).1 (argumentRegionComponent site).2.1 (argumentRegionComponent site).2.2 := by
  exact Classical.choose_spec (show ∃ data : List Label × SourcePort × LTerm,
    SourceSubterm [] .external basis (site.val++regionSite) data.1 data.2.1 data.2.2 from by
      obtain ⟨env,ctx,sub,located⟩ := site.property.2
      exact ⟨(env,ctx,sub),located⟩)

/-- Strict support in any actual original argument subregion localizes a
nonempty transported walk to one actual copy of that very subregion. -/
theorem root_beta_argument_subregion_walk_one_copy {body argument regionTerm : LTerm}
    (initial : INIT (.app beta (.lam alpha body) argument))
    (atRegion : argument.subterm regionSite=some regionTerm)
    (walk : SourceWalk (sourceEdges [] .external
      (initLabels (LTerm.contract beta alpha body argument).erase)) start word finish)
    (support : ∀ e∈word,(initialRelabelling (LTerm.contract beta alpha body argument) 0 e.atom).Supported
      (SourceRegion regionTerm))
    (rootAvoid : ∀ e∈word,(initialRelabelling (LTerm.contract beta alpha body argument) 0 e.atom).Supported
      (fun n => Label.atom n≠regionTerm.label)) :
    ∃ occurrence env ctx copy,ArgumentOccurrence body.erase occurrence ∧
      SourceSubterm [] .external (initLabels (LTerm.contract beta alpha body argument).erase)
        (occurrence++regionSite) env ctx copy ∧ SourceWalk (sourceEdges env ctx copy) start word finish ∧
      ∀ e∈word,Label.atom e.atom≠copy.label := by
  let basis := initLabels (LTerm.contract beta alpha body argument).erase
  let Index := ArgumentRegionComponentSite body.erase basis regionSite
  let component := fun i : Index => argumentRegionComponent i
  have components := fun i : Index => argumentRegionComponent_located i
  have apart : ∀ i j : Index,i≠j → DisjointPositions (i.val++regionSite) (j.val++regionSite) := by
    intro i j different
    have old := i.property.1.disjoint_of_ne j.property.1 (by
      intro same
      exact different (Subtype.ext same))
    exact ((old.descend_left regionSite).symm.descend_left regionSite).symm
  have cover : ∀ {s e r},e∈word → SourceTraverse (sourceEdges [] .external basis) s e r →
      ∃ i : Index,SourceTraverse (sourceEdges (component i).1 (component i).2.1 (component i).2.2) s e r ∧
        Label.atom e.atom≠(component i).2.2.label := by
    intro s e r inWord traverse
    cases traverse with
    | @forward edge n member atomic =>
      obtain ⟨occurrence,env,ctx,sub,occurs,located,edgeMember,notRoot⟩ :=
        root_beta_argument_subregion_edge_cover initial atRegion member
          (by simpa only [atomic,Label.relabel_atom] using support _ inWord)
          (by simpa only [atomic,Label.relabel_atom] using rootAvoid _ inWord)
      let i : Index := ⟨occurrence,occurs,env,ctx,sub,located⟩
      obtain ⟨envEq,ctxEq,subEq⟩ := located.unique (components i)
      refine ⟨i,.forward (envEq ▸ ctxEq ▸ subEq ▸ edgeMember) atomic,?_⟩
      change Label.atom n≠(argumentRegionComponent i).2.2.label
      rw [←subEq,←atomic]
      exact notRoot
    | @backward edge n member atomic =>
      obtain ⟨occurrence,env,ctx,sub,occurs,located,edgeMember,notRoot⟩ :=
        root_beta_argument_subregion_edge_cover initial atRegion member
          (by simpa only [atomic,Label.relabel_atom] using support _ inWord)
          (by simpa only [atomic,Label.relabel_atom] using rootAvoid _ inWord)
      let i : Index := ⟨occurrence,occurs,env,ctx,sub,located⟩
      obtain ⟨envEq,ctxEq,subEq⟩ := located.unique (components i)
      refine ⟨i,.backward (envEq ▸ ctxEq ▸ subEq ▸ edgeMember) atomic,?_⟩
      change Label.atom n≠(argumentRegionComponent i).2.2.label
      rw [←subEq,←atomic]
      exact notRoot
  obtain ⟨i,inside,nonroot⟩ := SourceWalk.one_component components (init_is_INIT _) apart walk cover
  exact ⟨i.val,(component i).1,(component i).2.1,(component i).2.2,i.property.1,components i,inside,nonroot⟩
/-- Degree-level localization for a proper or whole original argument region,
using only the two actual same-schedule labelled tails and strict support. -/
theorem root_beta_argument_subregion_degree_one_copy {body argument regionTerm : LTerm}
    (initial : INIT (.app beta (.lam alpha body) argument))
    (atRegion : argument.subterm regionSite=some regionTerm)
    (history : History ps (LTerm.contract beta alpha body argument) target)
    (basisHistory : History ps (initLabels (LTerm.contract beta alpha body argument).erase) basisTarget)
    (globalDegree : target.degreeAt p=some globalLabel)
    (basisDegree : basisTarget.degreeAt p=some basisLabel)
    (support : globalLabel.Supported (SourceRegion regionTerm))
    (rootAvoid : globalLabel.Supported (fun n => Label.atom n≠regionTerm.label)) :
    ∃ occurrence env ctx copy,ArgumentOccurrence body.erase occurrence ∧
      SourceSubterm [] .external (initLabels (LTerm.contract beta alpha body argument).erase)
        (occurrence++regionSite) env ctx copy ∧ basisLabel.Supported (SourceRegion copy) ∧
      ∀ e∈basisLabel.edgeWord,Label.atom e.atom≠copy.label := by
  have transported := history.local_degree_transport basisHistory basisDegree
  have labelEq : basisLabel.relabel (initialRelabelling (LTerm.contract beta alpha body argument) 0)=globalLabel :=
    Option.some.inj (transported.1.symm.trans globalDegree)
  have localSupport := (Label.supported_relabel _ _ basisLabel).mp (labelEq.symm ▸ support)
  have localAvoid := (Label.supported_relabel _ _ basisLabel).mp (labelEq.symm ▸ rootAvoid)
  have wordSupport := (Label.supported_iff_within _ basisLabel).mp localSupport
  have wordAvoid := (Label.supported_iff_within _ basisLabel).mp localAvoid
  obtain ⟨appId,lamId,walk⟩ := basisHistory.degree_walk (init_is_INIT _) basisDegree
  obtain ⟨occurrence,env,ctx,copy,occurs,located,localWalk,nonroot⟩ :=
    root_beta_argument_subregion_walk_one_copy initial atRegion walk wordSupport wordAvoid
  exact ⟨occurrence,env,ctx,copy,occurs,located,(Label.supported_iff_within _ basisLabel).mpr localWalk.within_source,nonroot⟩
end Lamping.Lambda.Labelled
