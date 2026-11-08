import Lamping.Lambda.LabelSubstitutionCopies
namespace Lamping.Lambda.Labelled

/-- INIT body labels lie outside the actual argument's original region. -/
theorem initial_body_outside_argument {body argument : LTerm}
    (initial : INIT (.app beta (.lam alpha body) argument)) :
    ∀ l∈body.labels,¬l.Supported (SourceRegion argument) := by
  intro l member support
  have sourceAt : (LTerm.app beta (.lam alpha body) argument).subterm [.fn,.body]=some body := by simp [LTerm.subterm]
  have inSource := LTerm.labels_subset_of_subterm sourceAt l member
  obtain ⟨n,atomic⟩ := initial.1 l inSource
  have inArgument : l∈argument.labels := by
    cases atomic
    exact support
  exact LTerm.disjoint_subterm_labels initial sourceAt (p := [.fn,.body]) (q := [.arg]) (by simp [LTerm.subterm])
    (DisjointPositions.head_ne (by intro equal; cases equal)) l member inArgument

/-- Every supported edge in the actual target's local INIT basis is an
internal nonroot edge of one actual argument occurrence. The induced
substitution is the existing target's labels, never a reset of its history. -/
theorem root_beta_argument_edge_cover {body argument : LTerm}
    (initial : INIT (.app beta (.lam alpha body) argument))
    (member : e∈sourceEdges [] .external (initLabels (LTerm.contract beta alpha body argument).erase))
    (support : (e.atom.relabel (initialRelabelling (LTerm.contract beta alpha body argument) 0)).Supported
      (SourceRegion argument)) :
    ∃ site env ctx copy,ArgumentOccurrence body.erase site ∧
      SourceSubterm [] .external (initLabels (LTerm.contract beta alpha body argument).erase) site env ctx copy ∧
      e∈sourceEdges env ctx copy ∧ e.atom≠copy.label := by
  let target := LTerm.contract beta alpha body argument
  let basis := initLabels target.erase
  let subst := initialRelabelling target 0
  have basisInitial : INIT basis := init_is_INIT _
  have atomMember : e.atom∈basis.labels := by
    rw [←sourceEdges_atoms basis [] .external]
    exact List.mem_map.mpr ⟨e,member,rfl⟩
  obtain ⟨p,node,atNode,labelEq⟩ := LTerm.label_mem_located basis atomMember
  have transported := LTerm.basis_node_transport target atNode
  have nodeSupport : (node.relabel subst).label.Supported (SourceRegion argument) := by
    simpa only [LTerm.label_relabel,labelEq] using support
  obtain ⟨site,currentCopy,suffix,occurs,atCurrentCopy,paths,nonempty,rootOutside⟩ :=
    LTerm.contract_supported_node_in_copy (initial_body_outside_argument initial) transported nodeSupport
  have copyLookup : (basis.subterm site).map (LTerm.relabel subst)=some currentCopy := by
    rw [←LTerm.subterm_relabel]
    change ((initLabels target.erase).relabel (initialRelabelling target 0)).subterm site=some currentCopy
    rw [show (initLabels target.erase).relabel (initialRelabelling target 0)=target from initialRelabelling_factor target 0]
    exact atCurrentCopy
  obtain ⟨copy,atCopy,copyEq⟩ := Option.map_eq_some_iff.mp copyLookup
  obtain ⟨env,ctx,atSite⟩ := SourceSubterm.of_lookup basis atCopy [] .external
  have localNode : copy.subterm suffix=some node := by
    rw [paths,LTerm.subterm_append,atCopy] at atNode
    exact atNode
  have insideAtom : e.atom∈copy.labels := labelEq ▸ LTerm.label_mem_of_subterm localNode
  obtain ⟨copyEdge,localEdge,atomEq⟩ := sourceEdges_has_label (env := env) (atPort := ctx) insideAtom
  have sameEdge : copyEdge=e := sourceEdges_unique basisInitial (atSite.edges_subset _ localEdge) member atomEq
  refine ⟨site,env,ctx,copy,occurs,atSite,sameEdge ▸ localEdge,?_⟩
  intro rootAtom
  have rootSupport : (copy.relabel subst).label.Supported (SourceRegion argument) := by
    simpa only [LTerm.label_relabel,←rootAtom] using support
  exact rootOutside (copyEq ▸ rootSupport)
/-- The environment and incoming port are determined by the actual syntax
path, as is the located labelled subtree. -/
theorem SourceSubterm.unique
    (first : SourceSubterm env ctx t p firstEnv firstCtx firstTerm)
    (second : SourceSubterm env ctx t p secondEnv secondCtx secondTerm) :
    firstEnv=secondEnv ∧ firstCtx=secondCtx ∧ firstTerm=secondTerm := by
  induction first with
  | nil => cases second; exact ⟨rfl,rfl,rfl⟩
  | fn _ ih => cases second with | fn second => exact ih second
  | arg _ ih => cases second with | arg second => exact ih second
  | body _ ih => cases second with | body second => exact ih second

/-- A located actual argument occurrence in the target INIT syntax. The
index records a path and proof of genuine location, with no path conclusion. -/
def ArgumentComponentSite (body : Term) (basis : LTerm) :=
  {p : Path // ArgumentOccurrence body p ∧ ∃ env ctx sub,SourceSubterm [] .external basis p env ctx sub}

noncomputable def argumentComponent (site : ArgumentComponentSite body basis) :
    List Label × SourcePort × LTerm :=
  Classical.choose (show ∃ data : List Label × SourcePort × LTerm,
    SourceSubterm [] .external basis site.val data.1 data.2.1 data.2.2 from by
      obtain ⟨env,ctx,sub,atSite⟩ := site.property.2
      exact ⟨(env,ctx,sub),atSite⟩)

theorem argumentComponent_located (site : ArgumentComponentSite body basis) :
    SourceSubterm [] .external basis site.val
      (argumentComponent site).1 (argumentComponent site).2.1 (argumentComponent site).2.2 := by
  exact Classical.choose_spec (show ∃ data : List Label × SourcePort × LTerm,
    SourceSubterm [] .external basis site.val data.1 data.2.1 data.2.2 from by
      obtain ⟨env,ctx,sub,atSite⟩ := site.property.2
      exact ⟨(env,ctx,sub),atSite⟩)

/-- The first real single-beta copy-localization bridge. Every signed edge of
the nonempty local INIT walk has regional image, so the entire walk belongs
to one actual argument copy. Shared external binders and erased forests are
handled by the actual port kernel and nonempty walk, respectively. -/
theorem root_beta_argument_walk_one_copy {body argument : LTerm}
    (initial : INIT (.app beta (.lam alpha body) argument))
    (walk : SourceWalk (sourceEdges [] .external
      (initLabels (LTerm.contract beta alpha body argument).erase)) start word finish)
    (support : ∀ e∈word,(initialRelabelling (LTerm.contract beta alpha body argument) 0 e.atom).Supported
      (SourceRegion argument)) :
    ∃ site env ctx copy,ArgumentOccurrence body.erase site ∧
      SourceSubterm [] .external (initLabels (LTerm.contract beta alpha body argument).erase) site env ctx copy ∧
      SourceWalk (sourceEdges env ctx copy) start word finish ∧
      ∀ e∈word,Label.atom e.atom≠copy.label := by
  let basis := initLabels (LTerm.contract beta alpha body argument).erase
  let Index := ArgumentComponentSite body.erase basis
  let component := fun i : Index => argumentComponent i
  have components := fun i : Index => argumentComponent_located i
  have apart : ∀ i j : Index,i≠j → DisjointPositions i.val j.val := by
    intro i j different
    exact i.property.1.disjoint_of_ne j.property.1 (by
      intro same
      exact different (Subtype.ext same))
  have cover : ∀ {s e r},e∈word → SourceTraverse (sourceEdges [] .external basis) s e r →
      ∃ i : Index,SourceTraverse (sourceEdges (component i).1 (component i).2.1 (component i).2.2) s e r ∧
        Label.atom e.atom≠(component i).2.2.label := by
    intro s e r inWord traverse
    cases traverse with
    | @forward edge n member atomic =>
      have edgeSupport : (edge.atom.relabel (initialRelabelling (LTerm.contract beta alpha body argument) 0)).Supported
          (SourceRegion argument) := by
        simpa only [atomic,Label.relabel_atom] using support _ inWord
      obtain ⟨site,env,ctx,sub,occurs,located,edgeMember,notRoot⟩ := root_beta_argument_edge_cover initial member edgeSupport
      let i : Index := ⟨site,occurs,env,ctx,sub,located⟩
      obtain ⟨envEq,ctxEq,subEq⟩ := located.unique (components i)
      refine ⟨i,?_,?_⟩
      · exact .forward (envEq ▸ ctxEq ▸ subEq ▸ edgeMember) atomic
      · change Label.atom n≠(argumentComponent i).2.2.label
        rw [←subEq,←atomic]
        exact notRoot
    | @backward edge n member atomic =>
      have edgeSupport : (edge.atom.relabel (initialRelabelling (LTerm.contract beta alpha body argument) 0)).Supported
          (SourceRegion argument) := by
        simpa only [atomic,Label.relabel_atom] using support _ inWord
      obtain ⟨site,env,ctx,sub,occurs,located,edgeMember,notRoot⟩ := root_beta_argument_edge_cover initial member edgeSupport
      let i : Index := ⟨site,occurs,env,ctx,sub,located⟩
      obtain ⟨envEq,ctxEq,subEq⟩ := located.unique (components i)
      refine ⟨i,?_,?_⟩
      · exact .backward (envEq ▸ ctxEq ▸ subEq ▸ edgeMember) atomic
      · change Label.atom n≠(argumentComponent i).2.2.label
        rw [←subEq,←atomic]
        exact notRoot
  obtain ⟨i,inside,nonroot⟩ := SourceWalk.one_component components (init_is_INIT _) apart walk cover
  exact ⟨i.val,(component i).1,(component i).2.1,(component i).2.2,i.property.1,components i,inside,nonroot⟩
/-- Every edge of an actual subtree walk is one of that subtree's labels. -/
theorem SourceWalk.within_source (walk : SourceWalk (sourceEdges env ctx t) start word finish) :
    EdgeWord.Within (SourceRegion t) word := by
  induction walk with
  | edge traverse =>
    cases traverse with
    | @forward edge n member atomic | @backward edge n member atomic =>
      intro e inWord
      have same := List.mem_singleton.mp inWord
      cases same
      change Label.atom n∈t.labels
      rw [←atomic,←sourceEdges_atoms t env ctx]
      exact List.mem_map.mpr ⟨edge,member,rfl⟩
  | join _ _ _ left right => exact (EdgeWord.within_append _ _ _).mpr ⟨left,right⟩

/-- A degree transported through a genuine tail, whose global image is
supported by the original argument, has all its local INIT atoms inside one
actual argument copy. This constructs the required copy instead of assuming
same-copy geometry or injectivity of the node map. -/
theorem root_beta_argument_degree_one_copy {body argument : LTerm}
    (initial : INIT (.app beta (.lam alpha body) argument))
    (history : History ps (LTerm.contract beta alpha body argument) target)
    (basisHistory : History ps (initLabels (LTerm.contract beta alpha body argument).erase) basisTarget)
    (globalDegree : target.degreeAt p=some globalLabel)
    (basisDegree : basisTarget.degreeAt p=some basisLabel)
    (support : globalLabel.Supported (SourceRegion argument)) :
    ∃ site env ctx copy,ArgumentOccurrence body.erase site ∧
      SourceSubterm [] .external (initLabels (LTerm.contract beta alpha body argument).erase) site env ctx copy ∧
      basisLabel.Supported (SourceRegion copy) ∧
      ∀ e∈basisLabel.edgeWord,Label.atom e.atom≠copy.label := by
  have transported := history.local_degree_transport basisHistory basisDegree
  have labelEq : basisLabel.relabel (initialRelabelling (LTerm.contract beta alpha body argument) 0)=globalLabel :=
    Option.some.inj (transported.1.symm.trans globalDegree)
  have localSupport := (Label.supported_relabel _ _ basisLabel).mp (labelEq.symm ▸ support)
  have wordSupport := (Label.supported_iff_within _ basisLabel).mp localSupport
  obtain ⟨appId,lamId,walk⟩ := basisHistory.degree_walk (init_is_INIT _) basisDegree
  obtain ⟨site,env,ctx,copy,occurs,located,localWalk,nonroot⟩ :=
    root_beta_argument_walk_one_copy initial walk wordSupport
  exact ⟨site,env,ctx,copy,occurs,located,(Label.supported_iff_within _ basisLabel).mpr localWalk.within_source,nonroot⟩
end Lamping.Lambda.Labelled
