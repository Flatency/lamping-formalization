import Lamping.Lambda.LabelPathInjective
namespace Lamping.Lambda.Labelled

/-- A coordinate map changes original node identities, preserving port kinds.
It may identify different copies of a node. No injectivity is required. -/
def SourcePort.relabel (nodes : Nat → Label) : SourcePort → SourcePort
  | .external => .external
  | .free i => .free i
  | .appContext l => .appContext (l.relabel nodes)
  | .appFn l => .appFn (l.relabel nodes)
  | .appArg l => .appArg (l.relabel nodes)
  | .lamContext l => .lamContext (l.relabel nodes)
  | .lamBody l => .lamBody (l.relabel nodes)
  | .lamBind l => .lamBind (l.relabel nodes)

theorem sourceBinder_relabel (nodes) (env : List Label) (i : Nat) :
    (sourceBinder env i).relabel nodes=sourceBinder (env.map (Label.relabel nodes)) i := by
  induction env generalizing i with
  | nil => simp [sourceBinder,SourcePort.relabel]
  | cons l env ih =>
    cases i with
    | zero => rfl
    | succ i => simpa only [List.map_cons,sourceBinder_succ] using ih i

/-- Paired source labelling: term labels record routes; app/lambda labels in
the second term record original node identities. These are different maps. -/
inductive OriginRoutes (edges : List SourceEdge) : List Label → SourcePort → LTerm → LTerm → Prop where
  | var : SourceRoute edges ctx l (sourceBinder env i) →
      OriginRoutes edges env ctx (.var l i) (.var arbitrary i)
  | lam : SourceRoute edges ctx l (.lamContext origin) →
      OriginRoutes edges (origin::env) (.lamBody origin) b b' →
      OriginRoutes edges env ctx (.lam l b) (.lam origin b')
  | app : SourceRoute edges ctx l (.appContext origin) →
      OriginRoutes edges env (.appFn origin) f f' → OriginRoutes edges env (.appArg origin) a a' →
      OriginRoutes edges env ctx (.app l f a) (.app origin f' a')

theorem TermRoutes.origin_exists (h : TermRoutes edges env ctx t) :
    ∃ origins, OriginRoutes edges env ctx t origins := by
  induction h with
  | var route => exact ⟨_,.var (arbitrary := Label.atom 0) route⟩
  | lam route body ih => obtain ⟨b,hb⟩ := ih; exact ⟨_,.lam route hb⟩
  | app route fn arg hf ha =>
    obtain ⟨f,hf⟩ := hf
    obtain ⟨a,ha⟩ := ha
    exact ⟨_,.app route hf ha⟩

theorem OriginRoutes.erase (h : OriginRoutes edges env ctx t origins) : origins.erase=t.erase := by
  induction h with
  | var => rfl
  | lam _ _ ih => exact congrArg Term.lam ih
  | app _ _ _ hf ha => simp only [LTerm.erase,hf,ha]

/-- Every local atomic basis edge is replaced by an actual route between the
mapped original ports. This is proved from paired syntax, not assumed. -/
theorem OriginRoutes.replacement_routes
    (basis : LTerm)
    (paired : OriginRoutes edges (env.map (Label.relabel nodes)) (ctx.relabel nodes)
      (basis.relabel degrees) (basis.relabel nodes))
    (member : e∈sourceEdges env ctx basis) :
    SourceRoute edges (e.fromPort.relabel nodes) (e.atom.relabel degrees) (e.toPort.relabel nodes) := by
  induction basis generalizing env ctx with
  | var l i =>
    cases paired with
    | var route =>
      simp only [sourceEdges,List.mem_singleton] at member
      cases member
      simpa only [sourceBinder_relabel] using route
  | lam l b hb =>
    cases paired with
    | lam route body =>
      simp only [sourceEdges,List.mem_cons] at member
      rcases member with rfl | member
      · exact route
      · apply hb (env := l::env) (ctx := .lamBody l) _ member
        simpa only [List.map_cons,SourcePort.relabel] using body
  | app l f a hf ha =>
    cases paired with
    | app route fn arg =>
      simp only [sourceEdges,List.mem_cons,List.mem_append] at member
      rcases member with rfl | member | member
      · exact route
      · apply hf (ctx := .appFn l) _ member
        exact fn
      · apply ha (ctx := .appArg l) _ member
        exact arg

/-- The induced edge substitution has a concrete node-coordinate map. Copies
may share original identities; the result deliberately asserts no injection. -/
theorem History.induced_edge_routes (h : History ps t u) (hi : INIT t) :
    ∃ nodes : Nat → Label, ∀ e∈sourceEdges [] .external (initLabels u.erase),
      SourceRoute (sourceEdges [] .external t) (e.fromPort.relabel nodes)
        (e.atom.relabel (initialRelabelling u 0)) (e.toPort.relabel nodes) := by
  obtain ⟨origins,paired⟩ := (h.generated_source_routes hi).origin_exists
  let nodes := initialRelabelling origins 0
  have atomEq : (initLabels u.erase).relabel (initialRelabelling u 0)=u := initialRelabelling_factor u 0
  have nodeEq : (initLabels u.erase).relabel nodes=origins := by
    rw [← paired.erase]
    exact initialRelabelling_factor origins 0
  refine ⟨nodes,?_⟩
  intro e he
  apply OriginRoutes.replacement_routes (initLabels u.erase) (degrees := initialRelabelling u 0) (nodes := nodes) _ he
  simpa only [atomEq,nodeEq,List.map_nil,SourcePort.relabel] using paired

/-- General source graph turns, including the direct context/argument and
body/binding turns not needed in the degree-path subclass. -/
inductive GraphTurn : SourcePort → SourcePort → Prop where
  | appContextFn (l) : GraphTurn (.appContext l) (.appFn l)
  | appContextArg (l) : GraphTurn (.appContext l) (.appArg l)
  | appFnArg (l) : GraphTurn (.appFn l) (.appArg l)
  | lamContextBody (l) : GraphTurn (.lamContext l) (.lamBody l)
  | lamContextBind (l) : GraphTurn (.lamContext l) (.lamBind l)
  | lamBodyBind (l) : GraphTurn (.lamBody l) (.lamBind l)
  | symm : GraphTurn a b → GraphTurn b a

theorem SourceTurn.graphTurn (h : SourceTurn a b) : GraphTurn a b := by
  induction h with
  | appOver => exact .appContextFn _
  | lamOver => exact .lamContextBody _
  | lamUnder => exact .symm (.lamContextBind _)
  | appUnder => exact .appFnArg _
  | symm _ ih => exact .symm ih

theorem GraphTurn.relabel (h : GraphTurn a b) (nodes) : GraphTurn (a.relabel nodes) (b.relabel nodes) := by
  induction h with
  | appContextFn => exact .appContextFn _
  | appContextArg => exact .appContextArg _
  | appFnArg => exact .appFnArg _
  | lamContextBody => exact .lamContextBody _
  | lamContextBind => exact .lamContextBind _
  | lamBodyBind => exact .lamBodyBind _
  | symm _ ih => exact .symm ih

/-- Arbitrary nonempty original lambda-graph paths with oriented edges. -/
inductive GraphWalk (edges : List SourceEdge) : SourcePort → EdgeWord → SourcePort → Prop where
  | edge : SourceTraverse edges a e b → GraphWalk edges a [e] b
  | join : GraphWalk edges a p b → GraphTurn b c → GraphWalk edges c q d → GraphWalk edges a (p++q) d

theorem GraphWalk.reverse (h : GraphWalk edges a p b) : GraphWalk edges b (EdgeWord.reverse p) a := by
  induction h with
  | edge h => exact .edge h.flip
  | join _ turn _ hp hq => rw [EdgeWord.reverse_append]; exact .join hq (.symm turn) hp

theorem SourceWalk.graphWalk (h : SourceWalk edges a p b) : GraphWalk edges a p b := by
  induction h with
  | edge h => exact .edge h
  | join _ turn _ hp hq => exact .join hp turn.graphTurn hq

theorem SourceRoute.graphWalk (h : SourceRoute edges a l b) : GraphWalk edges a l.edgeWord b := h.walk.graphWalk

/-- Actual graph-path edge substitution, sensitive to the orientation of every
edge. The atom replacement routes are obtained above from genuine beta transport. -/
theorem GraphWalk.edge_substitution (walk : GraphWalk targetEdges a p b)
    (replacements : ∀ e∈targetEdges, SourceRoute originalEdges (e.fromPort.relabel nodes)
      (e.atom.relabel degrees) (e.toPort.relabel nodes)) :
    GraphWalk originalEdges (a.relabel nodes)
      (EdgeWord.substitute (fun n => (degrees n).edgeWord) p) (b.relabel nodes) := by
  induction walk with
  | edge traversal =>
    cases traversal with
    | forward member atomic =>
      have route := replacements _ member
      rw [atomic,Label.relabel_atom] at route
      simpa only [EdgeWord.substitute,List.flatMap_cons,List.flatMap_nil,List.append_nil,if_false] using route.graphWalk
    | backward member atomic =>
      have route := replacements _ member
      rw [atomic,Label.relabel_atom] at route
      simpa only [EdgeWord.substitute,List.flatMap_cons,List.flatMap_nil,List.append_nil,if_true] using route.graphWalk.reverse
  | join _ turn _ hp hq =>
    rw [EdgeWord.substitute_append]
    exact .join hp (turn.relabel nodes) hq

/-- AG6.2.14 path validity: every real path in the local target INIT graph
substitutes to a real path in the fixed original INIT graph. -/
theorem History.induced_path_transport (h : History ps t u) (hi : INIT t) :
    ∃ nodes : Nat → Label, ∀ {a p b}, GraphWalk (sourceEdges [] .external (initLabels u.erase)) a p b →
      GraphWalk (sourceEdges [] .external t) (a.relabel nodes)
        (EdgeWord.substitute (fun n => (initialRelabelling u 0 n).edgeWord) p) (b.relabel nodes) := by
  obtain ⟨nodes,replacements⟩ := h.induced_edge_routes hi
  exact ⟨nodes,fun walk => walk.edge_substitution replacements⟩

/-- Composition acts on complete oriented replacement words, including all
backwards edges. It is not composition by unsigned concatenation. -/
theorem EdgeWord.substitute_comp (outer inner : Nat → EdgeWord) (p : EdgeWord) :
    substitute outer (substitute inner p)=
      substitute (fun n => substitute outer (inner n)) p := by
  induction p with
  | nil => rfl
  | cons e p ih =>
    rw [show e::p=[e]++p from rfl,substitute_append,substitute_append,
      substitute_append,ih]
    congr 1
    cases e with
    | mk n b =>
      cases b <;> simp only [substitute,List.flatMap_cons,List.flatMap_nil,
        List.append_nil,Bool.false_eq_true,if_false,if_true]
      exact substitute_reverse outer (inner n)

theorem EdgeWord.relabelling_comp (outer inner : Nat → Label) (p : EdgeWord) :
    substitute (fun n => (outer n).edgeWord) (substitute (fun n => (inner n).edgeWord) p)=
      substitute (fun n => ((inner n).relabel outer).edgeWord) p := by
  rw [substitute_comp]
  simp only [Label.edgeWord_relabel]

theorem LTerm.subterm_relabel (t : LTerm) (s) (p : Path) :
    (t.relabel s).subterm p=(t.subterm p).map (LTerm.relabel s) := by
  induction p generalizing t with
  | nil => simp [LTerm.subterm]
  | cons step p ih => cases t <;> cases step <;> simp [LTerm.subterm,LTerm.relabel,ih]

theorem LTerm.degree_relabel (t : LTerm) (s) :
    (t.relabel s).degree=t.degree.map (Label.relabel s) := by
  cases t with
  | var => rfl
  | lam => rfl
  | app l f a => cases f <;> rfl

theorem LTerm.degreeAt_relabel (t : LTerm) (s) (p : Path) :
    (t.relabel s).degreeAt p=(t.degreeAt p).map (Label.relabel s) := by
  simp only [LTerm.degreeAt,LTerm.subterm_relabel]
  cases t.subterm p <;> simp [LTerm.degree_relabel]

/-- A local INIT tail is merely proof coordinates: its degree is substituted
back to the unchanged global labelled history, at the identical redex path. -/
theorem History.local_degree_transport (global : History ps u v)
    (localHistory : History ps (initLabels u.erase) z) (degree : z.degreeAt p=some l) :
    v.degreeAt p=some (l.relabel (initialRelabelling u 0)) ∧
    (l.relabel (initialRelabelling u 0)).edgeWord=
      EdgeWord.substitute (fun n => (initialRelabelling u 0 n).edgeWord) l.edgeWord := by
  have transported := localHistory.relabel (initialRelabelling u 0)
  rw [show (initLabels u.erase).relabel (initialRelabelling u 0)=u from initialRelabelling_factor u 0] at transported
  have same := transported.deterministic global
  constructor
  · rw [←same,LTerm.degreeAt_relabel,degree]
    rfl
  · exact Label.edgeWord_relabel _ _

/-- Every live app/lambda origin is an original atomic node identity. Variable
coordinates do not name graph nodes and are assigned an arbitrary atom. -/
theorem TermRoutes.atomic_origin_exists
    (routes : TermRoutes (sourceEdges sourceEnv sourceCtx source) env ctx t) :
    ∃ origins, OriginRoutes (sourceEdges sourceEnv sourceCtx source) env ctx t origins ∧
      ∀ l∈origins.labels, IsAtomic l := by
  induction routes with
  | var route =>
    refine ⟨.var (Label.atom 0) _,.var route,?_⟩
    intro l member
    have eq : l=Label.atom 0 := by simpa only [LTerm.labels,List.mem_singleton] using member
    exact ⟨0,eq⟩
  | lam route body ih =>
    obtain ⟨origins,paired,atomic⟩ := ih
    obtain ⟨n,_,eq⟩ := route.lam_last_atom
    refine ⟨_,.lam route paired,?_⟩
    intro a member
    simp only [LTerm.labels,List.mem_cons] at member
    rcases member with rfl | member
    · exact ⟨n,eq⟩
    · exact atomic a member
  | app route fn arg hf ha =>
    obtain ⟨f',pairedF,atomicF⟩ := hf
    obtain ⟨a',pairedA,atomicA⟩ := ha
    obtain ⟨n,_,eq⟩ := route.app_last_atom
    refine ⟨_,.app route pairedF pairedA,?_⟩
    intro a member
    simp only [LTerm.labels,List.mem_cons,List.mem_append] at member
    rcases member with rfl | member | member
    · exact ⟨n,eq⟩
    · exact atomicF a member
    · exact atomicA a member

/-- The node-coordinate map is atomic on the complete relevant target basis.
It can still identify nodes belonging to distinct copies. -/
theorem History.induced_atomic_node_routes (h : History ps t u) (hi : INIT t) :
    ∃ nodes : Nat → Label, (∀ n,n<nodeCount u.erase → IsAtomic (nodes n)) ∧
      ∀ e∈sourceEdges [] .external (initLabels u.erase),
        SourceRoute (sourceEdges [] .external t) (e.fromPort.relabel nodes)
          (e.atom.relabel (initialRelabelling u 0)) (e.toPort.relabel nodes) := by
  obtain ⟨origins,paired,atomic⟩ := (h.generated_source_routes hi).atomic_origin_exists
  let nodes := initialRelabelling origins 0
  have nodeEq : (initLabels u.erase).relabel nodes=origins := by
    rw [←paired.erase]
    exact initialRelabelling_factor origins 0
  refine ⟨nodes,?_,?_⟩
  · intro n bound
    apply atomic
    apply initialRelabelling_mem origins 0 n (Nat.zero_le _)
    simpa only [paired.erase,Nat.zero_add] using bound
  · intro e member
    apply OriginRoutes.replacement_routes (initLabels u.erase)
      (degrees := initialRelabelling u 0) (nodes := nodes) _ member
    simpa only [show (initLabels u.erase).relabel (initialRelabelling u 0)=u from initialRelabelling_factor u 0,
      nodeEq,List.map_nil,SourcePort.relabel] using paired
end Lamping.Lambda.Labelled
