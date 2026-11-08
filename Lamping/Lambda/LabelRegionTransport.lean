import Lamping.Lambda.LabelRegions
namespace Lamping.Lambda.Labelled

/-- A fixed original subtree is the only part allowed to change. Every
current label inside it uses only the specified original edge region. -/
inductive RegionCut (region : Nat → Prop) : Path → LTerm → LTerm → Prop where
  | here : u.Supported region → RegionCut region [] t u
  | fn : RegionCut region site f f' → RegionCut region (.fn::site) (.app l f a) (.app l f' a)
  | arg : RegionCut region site a a' → RegionCut region (.arg::site) (.app l f a) (.app l f a')
  | body : RegionCut region site b b' → RegionCut region (.body::site) (.lam l b) (.lam l b')

def LTerm.labelAt (t : LTerm) (p : Path) : Option Label := (t.subterm p).map LTerm.label

theorem RegionCut.outside_labels (cut : RegionCut region site t u)
    (outside : ¬∃ suffix,p=site++suffix) : u.labelAt p=t.labelAt p := by
  induction cut generalizing p with
  | here => exact False.elim (outside ⟨p,rfl⟩)
  | fn cut ih =>
    cases p with
    | nil => rfl
    | cons s p =>
      cases s with
      | body => rfl
      | arg => rfl
      | fn =>
        apply ih
        rintro ⟨suffix,eq⟩
        exact outside ⟨suffix,congrArg (Step.fn::·) eq⟩
  | arg cut ih =>
    cases p with
    | nil => rfl
    | cons s p =>
      cases s with
      | body => rfl
      | fn => rfl
      | arg =>
        apply ih
        rintro ⟨suffix,eq⟩
        exact outside ⟨suffix,congrArg (Step.arg::·) eq⟩
  | body cut ih =>
    cases p with
    | nil => rfl
    | cons s p =>
      cases s with
      | fn => rfl
      | arg => rfl
      | body =>
        apply ih
        rintro ⟨suffix,eq⟩
        exact outside ⟨suffix,congrArg (Step.body::·) eq⟩

theorem RegionCut.step (cut : RegionCut region site t u)
    (step : StepAt (site++suffix) u v) : RegionCut region site t v := by
  induction cut generalizing v with
  | here supported => exact .here (step.supported supported)
  | fn cut ih => cases step with | fn step => exact .fn (ih step)
  | arg cut ih => cases step with | arg step => exact .arg (ih step)
  | body cut ih => cases step with | body step => exact .body (ih step)

theorem RegionCut.history (cut : RegionCut region site t u) (history : History ps u v)
    (inside : ∀ p∈ps,∃ suffix,p=site++suffix) : RegionCut region site t v := by
  induction history with
  | nil => exact cut
  | cons step tail ih =>
    obtain ⟨suffix,eq⟩ := inside _ List.mem_cons_self
    apply ih (cut.step (eq ▸ step))
    exact fun p member => inside p (List.mem_cons_of_mem _ member)

theorem RegionCut.initial (t : LTerm) (atSite : t.subterm site=some subtree)
    (supported : subtree.Supported region) : RegionCut region site t t := by
  induction site generalizing t with
  | nil =>
    simp only [LTerm.subterm,Option.some.injEq] at atSite
    cases atSite
    exact .here supported
  | cons s site ih =>
    cases t with
    | var => cases s <;> simp [LTerm.subterm] at atSite
    | lam l b =>
      cases s with
      | fn => simp [LTerm.subterm] at atSite
      | arg => simp [LTerm.subterm] at atSite
      | body => exact .body (ih b atSite)
    | app l f a =>
      cases s with
      | body => simp [LTerm.subterm] at atSite
      | fn => exact .fn (ih f atSite)
      | arg => exact .arg (ih a atSite)

/-- A supported current node must actually be inside the cut. Outside nodes
retain distinct original atomic labels, so cannot acquire regional support. -/
theorem RegionCut.supported_node_internal
    (cut : RegionCut (SourceRegion subtree) site t u) (initial : INIT t)
    (atSite : t.subterm site=some subtree) (atNode : u.subterm p=some node)
    (supported : node.label.Supported (SourceRegion subtree)) : ∃ suffix,p=site++suffix := by
  by_cases inside : ∃ suffix,p=site++suffix
  · exact inside
  · have outside := cut.outside_labels inside
    have sourceAt : t.labelAt p=some node.label := by
      rw [←outside]
      simp [LTerm.labelAt,atNode]
    obtain ⟨old,atOld,same⟩ := Option.map_eq_some_iff.mp sourceAt
    have atomic := initial.1 old.label (LTerm.label_mem_of_subterm atOld)
    obtain ⟨n,eq⟩ := atomic
    have oldSupport : old.label.Supported (SourceRegion subtree) := same ▸ supported
    have member : old.label∈subtree.labels := by
      rw [eq]
      rw [eq] at oldSupport
      exact oldSupport
    exact LTerm.initial_region_locates t initial atSite atOld member

theorem RegionCut.subtree_supported (cut : RegionCut region site t u) :
    ∃ result,u.subterm site=some result ∧ result.Supported region := by
  induction cut with
  | here supported => exact ⟨_,by simp [LTerm.subterm],supported⟩
  | fn cut ih => exact ih
  | arg cut ih => exact ih
  | body cut ih => exact ih

theorem RegionCut.internal_node_supported (cut : RegionCut region site t u)
    (atNode : u.subterm p=some node) (inside : ∃ suffix,p=site++suffix) :
    node.label.Supported region := by
  obtain ⟨result,atResult,supported⟩ := cut.subtree_supported
  obtain ⟨suffix,rfl⟩ := inside
  rw [LTerm.subterm_append,atResult] at atNode
  exact (LTerm.supported_iff _ _).mp supported _ (LTerm.label_mem_of_subterm atNode)

theorem History.region_cut (history : History ps t u) (initial : INIT t)
    (atSite : t.subterm site=some subtree)
    (inside : ∀ p∈ps,∃ suffix,p=site++suffix) :
    RegionCut (SourceRegion subtree) site t u := by
  have support := LTerm.atomic_region_support
    (fun l member => initial.1 l (LTerm.labels_subset_of_subterm atSite l member))
  exact (RegionCut.initial t atSite support).history history inside

theorem History.internal_label_support_iff (history : History ps t u) (initial : INIT t)
    (atSite : t.subterm site=some subtree)
    (inside : ∀ p∈ps,∃ suffix,p=site++suffix) (atNode : u.subterm p=some node) :
    node.label.Supported (SourceRegion subtree) ↔ ∃ suffix,p=site++suffix := by
  have cut := history.region_cut initial atSite inside
  exact ⟨cut.supported_node_internal initial atSite atNode,cut.internal_node_supported atNode⟩

theorem LTerm.label_relabel (t : LTerm) (s) : (t.relabel s).label=t.label.relabel s := by
  cases t <;> rfl

theorem LTerm.basis_node_transport (u : LTerm)
    (atBasis : (initLabels u.erase).subterm p=some node) :
    u.subterm p=some (node.relabel (initialRelabelling u 0)) := by
  have transported := congrArg (fun t : LTerm => t.subterm p) (initialRelabelling_factor u 0)
  change ((initLabels u.erase).relabel (initialRelabelling u 0)).subterm p=u.subterm p at transported
  rw [LTerm.subterm_relabel,atBasis] at transported
  exact transported.symm

/-- The exact relevant-domain support reflection needed after an internal
head contraction. Local INIT coordinates are proof coordinates, not a reset. -/
theorem RegionCut.local_basis_region (cut : RegionCut (SourceRegion subtree) site t u)
    (initial : INIT t) (atSite : t.subterm site=some subtree) :
    ∃ basisSubtree,(initLabels u.erase).subterm site=some basisSubtree ∧
      ∀ n,n<nodeCount u.erase →
        ((initialRelabelling u 0 n).Supported (SourceRegion subtree) ↔
          SourceRegion basisSubtree n) := by
  obtain ⟨currentSubtree,atCurrent,_⟩ := cut.subtree_supported
  have basisLookup : ((initLabels u.erase).subterm site).map (LTerm.relabel (initialRelabelling u 0))=
      some currentSubtree := by
    rw [←LTerm.subterm_relabel,show (initLabels u.erase).relabel (initialRelabelling u 0)=u from initialRelabelling_factor u 0,
      atCurrent]
  obtain ⟨basisSubtree,atBasis,subtreeEq⟩ := Option.map_eq_some_iff.mp basisLookup
  refine ⟨basisSubtree,atBasis,?_⟩
  intro n bound
  constructor
  · intro support
    have atomMember : Label.atom n∈(initLabels u.erase).labels := by
      rw [initLabels,labels_initFrom]
      apply List.mem_map.mpr
      refine ⟨n,?_,rfl⟩
      simp only [List.mem_range']
      exact ⟨n,bound,by omega⟩
    obtain ⟨p,node,atNode,labelEq⟩ := LTerm.label_mem_located _ atomMember
    have currentNode := LTerm.basis_node_transport u atNode
    have currentSupport : (node.relabel (initialRelabelling u 0)).label.Supported (SourceRegion subtree) := by
      simpa only [LTerm.label_relabel,labelEq,Label.relabel_atom] using support
    obtain ⟨suffix,pathEq⟩ := cut.supported_node_internal initial atSite currentNode currentSupport
    rw [pathEq,LTerm.subterm_append,atBasis] at atNode
    have member := LTerm.label_mem_of_subterm atNode
    change Label.atom n∈basisSubtree.labels
    exact labelEq ▸ member
  · intro member
    obtain ⟨suffix,node,atNode,labelEq⟩ := LTerm.label_mem_located basisSubtree member
    have lookup : (initLabels u.erase).subterm (site++suffix)=some node := by
      rw [LTerm.subterm_append,atBasis]
      exact atNode
    have currentNode := LTerm.basis_node_transport u lookup
    have support := cut.internal_node_supported currentNode ⟨suffix,rfl⟩
    simpa only [LTerm.label_relabel,labelEq,Label.relabel_atom] using support

mutual
  theorem Label.supported_relabel (s) (region) : ∀ l : Label,
      (l.relabel s).Supported region ↔ l.Supported (fun n => (s n).Supported region)
    | .single a => Letter.supported_relabel s region a
    | .cons a l => by
        simp only [Label.relabel,Label.supported_concat,Label.Supported,
          Letter.supported_relabel,Label.supported_relabel]
  theorem Letter.supported_relabel (s) (region) : ∀ a : Letter,
      (a.relabel s).Supported region ↔ a.Supported (fun n => (s n).Supported region)
    | .atom _ => Iff.rfl
    | .over l => Label.supported_relabel s region l
    | .under l => Label.supported_relabel s region l
end

theorem Label.supported_congr_on {l : Label} {relevant left right : Nat → Prop}
    (domain : l.Supported relevant)
    (equivalent : ∀ n,relevant n → (left n ↔ right n)) :
    l.Supported left ↔ l.Supported right := by
  simp only [Label.supported_iff_within] at domain ⊢
  constructor
  · intro support e member
    exact (equivalent e.atom (domain e member)).mp (support e member)
  · intro support e member
    exact (equivalent e.atom (domain e member)).mpr (support e member)

theorem LTerm.basis_atom_bound (u : LTerm)
    (member : Label.atom n∈(initLabels u.erase).labels) : n<nodeCount u.erase := by
  rw [initLabels,labels_initFrom] at member
  obtain ⟨m,inRange,equal⟩ := List.mem_map.mp member
  have same : m=n := by simpa only [Label.atom,Label.single.injEq,Letter.atom.injEq] using equal
  cases same
  obtain ⟨i,bound,equal⟩ := List.mem_range'.mp inRange
  omega

/-- After an actual internally confined prefix, the same tail has exact
degree/support reflection in its local INIT coordinates. The global degree
is still measured from the original INIT source with no label reset. -/
theorem History.local_degree_region_reflection
    (prefixHistory : History ps t u) (initial : INIT t)
    (atSite : t.subterm site=some subtree)
    (inside : ∀ p∈ps,∃ suffix,p=site++suffix)
    (globalTail : History qs u v) (localTail : History qs (initLabels u.erase) z)
    (degree : z.degreeAt p=some l) :
    ∃ basisSubtree,(initLabels u.erase).subterm site=some basisSubtree ∧
      v.degreeAt p=some (l.relabel (initialRelabelling u 0)) ∧
      ((l.relabel (initialRelabelling u 0)).Supported (SourceRegion subtree) ↔
        l.Supported (SourceRegion basisSubtree)) := by
  have cut := prefixHistory.region_cut initial atSite inside
  obtain ⟨basisSubtree,atBasis,reflection⟩ := cut.local_basis_region initial atSite
  refine ⟨basisSubtree,atBasis,(globalTail.local_degree_transport localTail degree).1,?_⟩
  rw [Label.supported_relabel]
  obtain ⟨body,atLambda⟩ := LTerm.degreeAt_lambda degree
  have supported := (LTerm.supported_iff _ _).mp
    (localTail.supported (init_is_INIT u.erase).supported) l (LTerm.label_mem_of_subterm atLambda)
  exact Label.supported_congr_on supported
    (fun n member => reflection n (LTerm.basis_atom_bound u member))
end Lamping.Lambda.Labelled
