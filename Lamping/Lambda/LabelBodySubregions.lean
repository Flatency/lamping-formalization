import Lamping.Lambda.LabelSubstitutionRegions
namespace Lamping.Lambda.Labelled

/-- The original function body of an INIT redex is itself INIT. -/
theorem INIT.redex_body {body argument : LTerm}
    (initial : INIT (.app beta (.lam alpha body) argument)) : INIT body := by
  refine ⟨?_,(List.nodup_cons.mp (List.nodup_append.mp (List.nodup_cons.mp initial.2).2).1).2⟩
  intro l member
  exact initial.1 l (List.mem_cons_of_mem _ (List.mem_append_left _ (List.mem_cons_of_mem _ member)))

/-- The fired lambda is outside every actual original body subregion. -/
theorem initial_head_outside_body_subregion {body argument regionTerm : LTerm}
    (initial : INIT (.app beta (.lam alpha body) argument))
    (atRegion : body.subterm regionSite=some regionTerm) : ¬alpha.Supported (SourceRegion regionTerm) := by
  intro support
  obtain ⟨n,atomic⟩ := initial.1 alpha
    (List.mem_cons_of_mem _ (List.mem_append_left _ List.mem_cons_self))
  have member : alpha∈regionTerm.labels := by
    rw [atomic] at support ⊢
    exact support
  have bodyMember := LTerm.labels_subset_of_subterm atRegion alpha member
  exact (List.nodup_cons.mp (List.nodup_append.mp (List.nodup_cons.mp initial.2).2).1).1 bodyMember

/-- Original body and argument are truly syntax-disjoint, so every argument
label is nonregional for every selected old body subregion. -/
theorem initial_argument_outside_body_subregion {body argument regionTerm : LTerm}
    (initial : INIT (.app beta (.lam alpha body) argument))
    (atRegion : body.subterm regionSite=some regionTerm) : LTerm.OutsideRegion (SourceRegion regionTerm) argument := by
  intro l member support
  obtain ⟨n,atomic⟩ := initial.1 l (List.mem_cons_of_mem _ (List.mem_append_right _ member))
  have inRegion : l∈regionTerm.labels := by
    rw [atomic] at support ⊢
    exact support
  have inBody := LTerm.labels_subset_of_subterm atRegion l inRegion
  have disjoint := (List.nodup_append.mp (List.nodup_cons.mp initial.2).2).2.2
  exact disjoint l (List.mem_cons_of_mem _ inBody) l member rfl

/-- Strict support in an original body subregion puts each local INIT edge
inside the one actual surviving image at the same body path. All outside
argument/head hypotheses are derived from the real INIT redex. -/
theorem root_beta_body_subregion_edge_cover {body argument regionTerm : LTerm}
    (initial : INIT (.app beta (.lam alpha body) argument))
    (atRegion : body.subterm regionSite=some regionTerm)
    (member : e∈sourceEdges [] .external (initLabels (LTerm.contract beta alpha body argument).erase))
    (support : (e.atom.relabel (initialRelabelling (LTerm.contract beta alpha body argument) 0)).Supported
      (SourceRegion regionTerm))
    (rootAvoid : (e.atom.relabel (initialRelabelling (LTerm.contract beta alpha body argument) 0)).Supported
      (fun n => Label.atom n≠regionTerm.label)) :
    ∃ env ctx copy,SourceSubterm [] .external (initLabels (LTerm.contract beta alpha body argument).erase)
      regionSite env ctx copy ∧ e∈sourceEdges env ctx copy ∧ e.atom≠copy.label := by
  let target := LTerm.contract beta alpha body argument
  let basis := initLabels target.erase
  let subst := initialRelabelling target 0
  have atomMember : e.atom∈basis.labels := by
    rw [←sourceEdges_atoms basis [] .external]
    exact List.mem_map.mpr ⟨e,member,rfl⟩
  obtain ⟨p,node,atNode,labelEq⟩ := LTerm.label_mem_located basis atomMember
  have transported := LTerm.basis_node_transport target atNode
  have nodeSupport : (node.relabel subst).label.Supported (SourceRegion regionTerm) := by
    simpa only [LTerm.label_relabel,labelEq] using support
  obtain ⟨old,atOld,sameLabel⟩ := LTerm.contract_supported_body_node_origin
    (initial_argument_outside_body_subregion initial atRegion)
    (initial_head_outside_body_subregion initial atRegion) transported nodeSupport
  have oldSupport : old.label.Supported (SourceRegion regionTerm) := sameLabel ▸ nodeSupport
  obtain ⟨n,atomic⟩ := initial.redex_body.1 old.label (LTerm.label_mem_of_subterm atOld)
  have regionMember : old.label∈regionTerm.labels := by
    rw [atomic] at oldSupport ⊢
    exact oldSupport
  obtain ⟨suffix,paths⟩ := LTerm.initial_region_locates body initial.redex_body atRegion atOld regionMember
  have insideNode : (basis.subterm regionSite).bind (fun t => t.subterm suffix)=some node := by
    rw [←LTerm.subterm_append,←paths]
    exact atNode
  obtain ⟨copy,copyLookup,localNode⟩ := Option.bind_eq_some_iff.mp insideNode
  obtain ⟨env,ctx,atCopy⟩ := SourceSubterm.of_lookup basis copyLookup [] .external
  have insideAtom : e.atom∈copy.labels := labelEq ▸ LTerm.label_mem_of_subterm localNode
  obtain ⟨regionEdge,edgeMember,atomEq⟩ := sourceEdges_has_label (env := env) (atPort := ctx) insideAtom
  have sameEdge : regionEdge=e := sourceEdges_unique (init_is_INIT _) (atCopy.edges_subset _ edgeMember) member atomEq
  refine ⟨env,ctx,copy,atCopy,sameEdge ▸ edgeMember,?_⟩
  intro rootEq
  have rootLookup := LTerm.basis_node_transport target copyLookup
  obtain ⟨current,currentLookup,reflects⟩ := LTerm.contract_subterm_root_reflect
    (beta := beta) (alpha := alpha) (argument := argument) atRegion
  have sameCurrent : current=copy.relabel subst := Option.some.inj (currentLookup.symm.trans rootLookup)
  have avoid : (copy.relabel subst).label.Supported (fun n => Label.atom n≠regionTerm.label) := by
    simpa only [LTerm.label_relabel,←rootEq] using rootAvoid
  have oldAvoid := reflects _ (sameCurrent.symm ▸ avoid)
  obtain ⟨n,atomic⟩ := initial.redex_body.1 regionTerm.label (LTerm.label_mem_of_subterm atRegion)
  rw [atomic] at oldAvoid
  exact oldAvoid rfl
/-- A word edge really is traversed somewhere in its actual nonempty walk. -/
theorem SourceWalk.traverse_of_mem (walk : SourceWalk edges start word finish) (member : e∈word) :
    ∃ a b,SourceTraverse edges a e b := by
  induction walk with
  | edge traverse =>
    have same := List.mem_singleton.mp member
    cases same
    exact ⟨_,_,traverse⟩
  | join hp turn hq ihp ihq =>
    rcases List.mem_append.mp member with left | right
    · exact ihp left
    · exact ihq right

/-- Restrict an actual walk using exact signed traversals with unchanged
endpoints and turns, rather than only the unsigned word membership. -/
theorem SourceWalk.restrict_traversals (walk : SourceWalk edges start word finish)
    (restrict : ∀ {a e b},e∈word → SourceTraverse edges a e b → SourceTraverse smaller a e b) :
    SourceWalk smaller start word finish := by
  induction walk with
  | edge traverse => exact .edge (restrict List.mem_cons_self traverse)
  | join hp turn hq ihp ihq =>
    exact .join (ihp (fun member traverse => restrict (List.mem_append_left _ member) traverse)) turn
      (ihq (fun member traverse => restrict (List.mem_append_right _ member) traverse))

/-- All strict-regional target-basis edges lie in the one actual surviving
body subregion. The source syntax fixes that occurrence before the walk is
restricted, including body-root and variable-at-root substitution cases. -/
theorem root_beta_body_subregion_walk {body argument regionTerm : LTerm}
    (initial : INIT (.app beta (.lam alpha body) argument))
    (atRegion : body.subterm regionSite=some regionTerm)
    (walk : SourceWalk (sourceEdges [] .external
      (initLabels (LTerm.contract beta alpha body argument).erase)) start word finish)
    (support : ∀ e∈word,(initialRelabelling (LTerm.contract beta alpha body argument) 0 e.atom).Supported
      (SourceRegion regionTerm))
    (rootAvoid : ∀ e∈word,(initialRelabelling (LTerm.contract beta alpha body argument) 0 e.atom).Supported
      (fun n => Label.atom n≠regionTerm.label)) :
    ∃ env ctx copy,SourceSubterm [] .external (initLabels (LTerm.contract beta alpha body argument).erase)
      regionSite env ctx copy ∧ SourceWalk (sourceEdges env ctx copy) start word finish ∧
      ∀ e∈word,Label.atom e.atom≠copy.label := by
  let target := LTerm.contract beta alpha body argument
  let basis := initLabels target.erase
  let subst := initialRelabelling target 0
  obtain ⟨current,currentLookup,_⟩ := LTerm.contract_subterm_root_reflect
    (beta := beta) (alpha := alpha) (argument := argument) atRegion
  have basisLookup : (basis.subterm regionSite).map (LTerm.relabel subst)=some current := by
    rw [←LTerm.subterm_relabel]
    change ((initLabels target.erase).relabel (initialRelabelling target 0)).subterm regionSite=some current
    rw [show (initLabels target.erase).relabel (initialRelabelling target 0)=target from initialRelabelling_factor target 0]
    exact currentLookup
  obtain ⟨copy,copyLookup,_⟩ := Option.map_eq_some_iff.mp basisLookup
  obtain ⟨env,ctx,located⟩ := SourceSubterm.of_lookup basis copyLookup [] .external
  have restrict : ∀ {a e b},e∈word → SourceTraverse (sourceEdges [] .external basis) a e b →
      SourceTraverse (sourceEdges env ctx copy) a e b ∧ Label.atom e.atom≠copy.label := by
    intro a e b inWord traverse
    cases traverse with
    | @forward edge n member atomic =>
      obtain ⟨newEnv,newCtx,newCopy,newLocated,edgeMember,nonroot⟩ :=
        root_beta_body_subregion_edge_cover initial atRegion member
          (by simpa only [atomic,Label.relabel_atom] using support _ inWord)
          (by simpa only [atomic,Label.relabel_atom] using rootAvoid _ inWord)
      obtain ⟨envEq,ctxEq,copyEq⟩ := newLocated.unique located
      exact ⟨.forward (envEq ▸ ctxEq ▸ copyEq ▸ edgeMember) atomic,by simpa only [←atomic,←copyEq] using nonroot⟩
    | @backward edge n member atomic =>
      obtain ⟨newEnv,newCtx,newCopy,newLocated,edgeMember,nonroot⟩ :=
        root_beta_body_subregion_edge_cover initial atRegion member
          (by simpa only [atomic,Label.relabel_atom] using support _ inWord)
          (by simpa only [atomic,Label.relabel_atom] using rootAvoid _ inWord)
      obtain ⟨envEq,ctxEq,copyEq⟩ := newLocated.unique located
      exact ⟨.backward (envEq ▸ ctxEq ▸ copyEq ▸ edgeMember) atomic,by simpa only [←atomic,←copyEq] using nonroot⟩
  refine ⟨env,ctx,copy,located,walk.restrict_traversals (fun member traverse => (restrict member traverse).1),?_⟩
  intro e member
  obtain ⟨a,b,traverse⟩ := walk.traverse_of_mem member
  exact (restrict member traverse).2

/-- Degree transport into the one actual body subregion after a real beta,
retaining strict incoming-edge avoidance in the local INIT coordinates. -/
theorem root_beta_body_subregion_degree {body argument regionTerm : LTerm}
    (initial : INIT (.app beta (.lam alpha body) argument))
    (atRegion : body.subterm regionSite=some regionTerm)
    (history : History ps (LTerm.contract beta alpha body argument) target)
    (basisHistory : History ps (initLabels (LTerm.contract beta alpha body argument).erase) basisTarget)
    (globalDegree : target.degreeAt p=some globalLabel)
    (basisDegree : basisTarget.degreeAt p=some basisLabel)
    (support : globalLabel.Supported (SourceRegion regionTerm))
    (rootAvoid : globalLabel.Supported (fun n => Label.atom n≠regionTerm.label)) :
    ∃ env ctx copy,SourceSubterm [] .external (initLabels (LTerm.contract beta alpha body argument).erase)
      regionSite env ctx copy ∧ basisLabel.Supported (SourceRegion copy) ∧
      ∀ e∈basisLabel.edgeWord,Label.atom e.atom≠copy.label := by
  have transported := history.local_degree_transport basisHistory basisDegree
  have labelEq : basisLabel.relabel (initialRelabelling (LTerm.contract beta alpha body argument) 0)=globalLabel :=
    Option.some.inj (transported.1.symm.trans globalDegree)
  have localSupport := (Label.supported_relabel _ _ basisLabel).mp (labelEq.symm ▸ support)
  have localAvoid := (Label.supported_relabel _ _ basisLabel).mp (labelEq.symm ▸ rootAvoid)
  obtain ⟨appId,lamId,walk⟩ := basisHistory.degree_walk (init_is_INIT _) basisDegree
  obtain ⟨env,ctx,copy,located,localWalk,nonroot⟩ := root_beta_body_subregion_walk initial atRegion walk
    ((Label.supported_iff_within _ basisLabel).mp localSupport)
    ((Label.supported_iff_within _ basisLabel).mp localAvoid)
  exact ⟨env,ctx,copy,located,(Label.supported_iff_within _ basisLabel).mpr localWalk.within_source,nonroot⟩
end Lamping.Lambda.Labelled
